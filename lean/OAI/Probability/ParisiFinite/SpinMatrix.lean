import Mathlib
import OAI.Probability.ParisiFinite.FiniteMaxHamiltonian

namespace OAI

/-! Spin Matrix. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped Topology
open Filter
open scoped BigOperators Matrix

namespace SeedControl

attribute [local instance 100] LieRing.ofAssociativeRing

abbrev SpinMatrix := Matrix (Fin 2) (Fin 2) ℂ

def x : SpinMatrix := !![0, -Complex.I; -Complex.I, 0]
def y : SpinMatrix := !![0, -1; 1, 0]
def z : SpinMatrix := !![-Complex.I, 0; 0, Complex.I]

theorem lie_z_y : ⁅z,y⁆ = (-2 : ℝ) • x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ring.lie_def, x, y, z] <;> ring

theorem lie_z_lie_z_x : ⁅z,⁅z,x⁆⁆ = (-4 : ℝ) • x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ring.lie_def, x, z] <;> ring

abbrev Ensemble (ι : Type*) := (ι → SpinMatrix) × (ℝ × ℝ)

def generatorZ {ι : Type*} (c : ι → ℝ) : Ensemble ι := (fun i => c i • z, 1, 0)
def generatorY {ι : Type*} (d : ι → ℝ) : Ensemble ι := (fun i => d i • y, 0, 1)
def fieldX {ι : Type*} (f : ι → ℝ) : Ensemble ι := (fun i => f i • x, 0, 0)

theorem generator_bracket {ι : Type*} (c d : ι → ℝ) :
    ⁅generatorZ c, generatorY d⁆ = (-2 : ℝ) • fieldX (fun i => c i * d i) := by
  apply Prod.ext
  · funext i
    change ⁅c i • z, d i • y⁆ = (-2 : ℝ) • ((c i * d i) • x)
    rw [smul_lie, lie_smul, lie_z_y]
    simp only [smul_smul]
    congr 1
    ring
  · ext <;> simp [generatorZ, generatorY, fieldX, Ring.lie_def]

theorem generator_double_bracket {ι : Type*} (c f : ι → ℝ) :
    ⁅generatorZ c, ⁅generatorZ c, fieldX f⁆⁆ = (-4 : ℝ) • fieldX (fun i => c i ^ 2 * f i) := by
  apply Prod.ext
  · funext i
    change ⁅c i • z, ⁅c i • z, f i • x⁆⁆ = (-4 : ℝ) • ((c i ^ 2 * f i) • x)
    rw [smul_lie, smul_lie, lie_smul, lie_smul, lie_smul, lie_z_lie_z_x]
    simp only [smul_smul]
    congr 1
    ring
  · ext <;> simp [generatorZ, fieldX, Ring.lie_def]

theorem fieldX_mul_mem {ι : Type*} (L : LieSubalgebra ℝ (Ensemble ι))
    {c d : ι → ℝ} (hc : generatorZ c ∈ L) (hd : generatorY d ∈ L) :
    fieldX (fun i => c i * d i) ∈ L := by
  have h := L.lie_mem hc hd
  rw [generator_bracket] at h
  have h' := L.smul_mem (-1/2 : ℝ) h
  simpa only [smul_smul, show (-1/2:ℝ)*(-2)=1 by norm_num, one_smul] using h'

theorem fieldX_sq_mul_mem {ι : Type*} (L : LieSubalgebra ℝ (Ensemble ι))
    {c f : ι → ℝ} (hc : generatorZ c ∈ L) (hf : fieldX f ∈ L) :
    fieldX (fun i => c i ^ 2 * f i) ∈ L := by
  have h := L.lie_mem hc (L.lie_mem hc hf)
  rw [generator_double_bracket] at h
  have h' := L.smul_mem (-1/4 : ℝ) h
  simpa only [smul_smul, show (-1/4:ℝ)*(-4)=1 by norm_num, one_smul] using h'

@[simp] theorem fieldX_add {ι : Type*} (f g : ι → ℝ) :
    fieldX (fun i => f i + g i) = fieldX f + fieldX g := by
  apply Prod.ext
  · funext i; exact add_smul _ _ _
  · simp [fieldX]

@[simp] theorem fieldX_const_mul {ι : Type*} (t : ℝ) (f : ι → ℝ) :
    fieldX (fun i => t * f i) = t • fieldX f := by
  apply Prod.ext
  · funext i; exact mul_smul _ _ _
  · simp [fieldX]

theorem weighted_power_mem {ι : Type*} (L : LieSubalgebra ℝ (Ensemble ι))
    {c d : ι → ℝ} (hc : generatorZ c ∈ L) (hd : generatorY d ∈ L) (k : ℕ) :
    fieldX (fun i => c i * d i * (c i ^ 2)^k) ∈ L := by
  induction k with
  | zero => simpa using fieldX_mul_mem L hc hd
  | succ k ih =>
    have h := fieldX_sq_mul_mem L hc ih
    convert h using 1
    congr 1
    funext i
    ring

theorem weighted_polynomial_mem {ι : Type*} (L : LieSubalgebra ℝ (Ensemble ι))
    {c d : ι → ℝ} (hc : generatorZ c ∈ L) (hd : generatorY d ∈ L) (P : Polynomial ℝ) :
    fieldX (fun i => c i * d i * P.eval (c i ^ 2)) ∈ L := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [Polynomial.eval_add, mul_add, fieldX_add] using L.add_mem hP hQ
  | monomial k a =>
    have h := L.smul_mem a (weighted_power_mem L hc hd k)
    rw [← fieldX_const_mul] at h
    convert h using 1
    congr 1
    funext i
    rw [Polynomial.eval_monomial]
    ring

 
theorem interpolate_finite_fibers {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (h : ∀ i j, a i = a j → b i = b j) :
    ∃ P : Polynomial ℝ, ∀ i, P.eval (a i) = b i := by
  classical
  let f : ℝ → ℝ := fun t => if ht : ∃ i, a i = t then b ht.choose else 0
  have hf (i : ι) : f (a i) = b i := by
    dsimp only [f]
    rw [dite_eq_left ⟨i, rfl⟩]
    exact h _ _ (Exists.choose_spec (show ∃ j, a j = a i from ⟨i, rfl⟩))
  refine ⟨Lagrange.interpolate (Finset.univ.image a) id f, fun i => ?_⟩
  calc
    _ = f (a i) := Lagrange.eval_interpolate_at_node f (fun _ _ _ _ he => he)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    _ = b i := hf i

 

theorem common_axis_mem {ι : Type*} [Fintype ι] (L : LieSubalgebra ℝ (Ensemble ι))
    {c d : ι → ℝ} (hc : generatorZ c ∈ L) (hd : generatorY d ∈ L)
    (hn : ∀ i, c i * d i ≠ 0)
    (hs : ∀ i j, c i ^ 2 = c j ^ 2 → c i * d i = c j * d j) :
    fieldX (fun _ => 1) ∈ L := by
  obtain ⟨P, hP⟩ := interpolate_finite_fibers (fun i => c i ^ 2)
    (fun i => (c i * d i)⁻¹) (fun i j he => congrArg Inv.inv (hs i j he))
  have h := weighted_polynomial_mem L hc hd P
  simpa only [hP, mul_inv_cancel₀ (hn _)] using h

 
theorem exists_generic_slope (s : Finset (ℝ × ℝ)) (h : ∀ v ∈ s, v ≠ 0) :
    ∃ t : ℝ, ∀ v ∈ s, v.1 + t * v.2 ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := (s.finite_toSet.image (fun v : ℝ × ℝ => -v.1 / v.2)).exists_notMem
  refine ⟨t, fun v hv he => ?_⟩
  by_cases hv2 : v.2 = 0
  · have hv1 : v.1 = 0 := by simpa [hv2] using he
    exact h v hv (Prod.ext hv1 hv2)
  · apply ht
    exact ⟨v, hv, (eq_div_iff hv2).mpr (by nlinarith) |>.symm⟩

 

theorem exists_separating_frame {ι : Type*} [Fintype ι]
    (v : ι → ℝ × ℝ) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : ℝ, a^2+b^2=1 ∧
      (∀ i, (a*(v i).1+b*(v i).2) * (-b*(v i).1+a*(v i).2) ≠ 0) ∧
      (∀ i j, (a*(v i).1+b*(v i).2)^2 = (a*(v j).1+b*(v j).2)^2 →
        v i = v j ∨ v i = -v j) := by
  classical
  let s : Finset (ℝ × ℝ) :=
    (Finset.univ.image v ∪ Finset.univ.image (fun i => ((v i).2, -(v i).1)) ∪
      (Finset.univ.product Finset.univ).image (fun ij : ι × ι => v ij.1 - v ij.2) ∪
      (Finset.univ.product Finset.univ).image (fun ij : ι × ι => v ij.1 + v ij.2)).erase 0
  obtain ⟨t, ht⟩ := exists_generic_slope s (fun w hw => (Finset.mem_erase.mp hw).1)
  have hproj (i : ι) : (v i).1 + t*(v i).2 ≠ 0 := by
    apply ht
    simp [s, hv i]
  have hperp (i : ι) : (v i).2 - t*(v i).1 ≠ 0 := by
    have hn : ((v i).2, -(v i).1) ≠ (0 : ℝ×ℝ) := by
      intro h
      apply hv i
      exact Prod.ext (neg_eq_zero.mp (congrArg Prod.snd h)) (congrArg Prod.fst h)
    have hm : ((v i).2, -(v i).1) ∈ s := by
      simp [s, hn]
      exact Or.inr (Or.inl ⟨i,rfl,rfl⟩)
    simpa only [mul_neg, ← sub_eq_add_neg] using ht _ hm
  have hsep (i j : ι) : ((v i).1+t*(v i).2)^2 = ((v j).1+t*(v j).2)^2 →
      v i = v j ∨ v i = -v j := by
    intro he
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
    · by_contra hn
      have hn' : v i - v j ≠ 0 := sub_ne_zero.mpr (not_or.mp hn).1
      have hm : v i - v j ∈ s := by simp [s, hn']
      apply ht _ hm
      change (v i).1-(v j).1 + t*((v i).2-(v j).2) = 0
      linarith
    · by_contra hn
      have hn' : v i + v j ≠ 0 := by
        intro hz
        exact (not_or.mp hn).2 (eq_neg_of_add_eq_zero_left hz)
      have hm : v i + v j ∈ s := by simp [s, hn']
      apply ht _ hm
      change (v i).1+(v j).1 + t*((v i).2+(v j).2) = 0
      linarith
  let r := Real.sqrt (1+t^2)
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r^2 = 1+t^2 := Real.sq_sqrt (by positivity)
  refine ⟨1/r,t/r,?_,?_,?_⟩
  · field_simp
    nlinarith [sq_nonneg t]
  · intro i
    rw [show 1/r*(v i).1+(t/r)*(v i).2 = ((v i).1+t*(v i).2)/r by ring,
      show -(t/r)*(v i).1+(1/r)*(v i).2 = ((v i).2-t*(v i).1)/r by ring]
    exact mul_ne_zero (div_ne_zero (hproj i) hr.ne') (div_ne_zero (hperp i) hr.ne')
  · intro i j he
    apply hsep i j
    have he' : (((v i).1+t*(v i).2)/r)^2 = (((v j).1+t*(v j).2)/r)^2 := by
      convert he using 1 <;> ring
    simpa only [div_pow, div_left_inj' (pow_ne_zero 2 hr.ne')] using he'

 

theorem common_axis_generated {ι : Type*} [Fintype ι]
    (v : ι → ℝ × ℝ) (hv : ∀ i, v i ≠ 0) :
    ∃ a b : ℝ, a^2+b^2=1 ∧
      fieldX (fun _ : ι => 1) ∈ LieSubalgebra.lieSpan ℝ (Ensemble ι)
        {generatorZ (fun i => a*(v i).1+b*(v i).2),
         generatorY (fun i => -b*(v i).1+a*(v i).2)} := by
  obtain ⟨a,b,hab,hn,hs⟩ := exists_separating_frame v hv
  refine ⟨a,b,hab,common_axis_mem _ ?_ ?_ hn ?_⟩
  · exact LieSubalgebra.subset_lieSpan (by simp)
  · exact LieSubalgebra.subset_lieSpan (by simp)
  · intro i j he
    rcases hs i j he with h | h
    · simp [h]
    · simp only [h, Prod.fst_neg, Prod.snd_neg]
      ring

end SeedControl

namespace QuaternionControl
open PulseControl ExactPulseControl
variable {ι : Type*} [Fintype ι]
abbrev QField (ι : Type*) := ι → Quaternion ℝ
instance quaternionStarModule : StarModule ℝ (Quaternion ℝ) where
  star_smul := by intro r q; ext <;> simp

local instance spinMatrixQFieldNormedAlgebra : NormedAlgebra ℚ (QField ι) :=
  NormedAlgebra.restrictScalars ℚ ℝ (QField ι)

def qX (f : ι → ℝ) : QField ι := fun i => ⟨0,0,0,f i⟩
def qY (f : ι → ℝ) : QField ι := fun i => ⟨0,0,f i,0⟩
def qZ (f : ι → ℝ) : QField ι := fun i => ⟨0,f i,0,0⟩
def gen (c d : ι → ℝ) (a : Bool) : QField ι := if a then qZ c else qY d

def tang (c d : ι → ℝ) := actualTangents (gen c d)

omit [Fintype ι] in
@[simp] theorem qX_add (f g : ι → ℝ) : qX (fun i => f i+g i)=qX f+qX g := by
  funext i
  change (⟨0,0,0,f i+g i⟩ : Quaternion ℝ) = (⟨0,0,0,f i⟩ : Quaternion ℝ) + (⟨0,0,0,g i⟩ : Quaternion ℝ)
  ext <;> simp
omit [Fintype ι] in
@[simp] theorem qX_smul (t : ℝ) (f : ι → ℝ) : qX (fun i => t*f i)=t • qX f := by
  funext i
  change (⟨0,0,0,t*f i⟩ : Quaternion ℝ) = t • (⟨0,0,0,f i⟩ : Quaternion ℝ)
  ext <;> simp
omit [Fintype ι] in
theorem bracket_zy (c d : ι → ℝ) : qZ c*qY d-qY d*qZ c=(2:ℝ) • qX (fun i => c i*d i) := by
  funext i
  change (⟨0,c i,0,0⟩ : Quaternion ℝ) * (⟨0,0,d i,0⟩ : Quaternion ℝ) -
    (⟨0,0,d i,0⟩ : Quaternion ℝ) * (⟨0,c i,0,0⟩ : Quaternion ℝ) =
    (2:ℝ) • (⟨0,0,0,c i*d i⟩ : Quaternion ℝ)
  ext <;> simp; ring
omit [Fintype ι] in
theorem bracket_zx (c f : ι → ℝ) : qZ c*qX f-qX f*qZ c=qY (fun i => -2*c i*f i) := by
  funext i
  change (⟨0,c i,0,0⟩ : Quaternion ℝ) * (⟨0,0,0,f i⟩ : Quaternion ℝ) -
    (⟨0,0,0,f i⟩ : Quaternion ℝ) * (⟨0,c i,0,0⟩ : Quaternion ℝ) =
    (⟨0,0,-2*c i*f i,0⟩ : Quaternion ℝ)
  ext <;> simp; ring
omit [Fintype ι] in
theorem bracket_yx (d f : ι → ℝ) : qY d*qX f-qX f*qY d=qZ (fun i => 2*d i*f i) := by
  funext i
  change (⟨0,0,d i,0⟩ : Quaternion ℝ) * (⟨0,0,0,f i⟩ : Quaternion ℝ) -
    (⟨0,0,0,f i⟩ : Quaternion ℝ) * (⟨0,0,d i,0⟩ : Quaternion ℝ) =
    (⟨0,2*d i*f i,0,0⟩ : Quaternion ℝ)
  ext <;> simp; ring
omit [Fintype ι] in
theorem double_zx (c f : ι → ℝ) :
    qZ c*(qZ c*qX f-qX f*qZ c)-(qZ c*qX f-qX f*qZ c)*qZ c=(-4:ℝ) • qX (fun i => c i^2*f i) := by
  rw [bracket_zx,bracket_zy]
  rw [← qX_smul, ← qX_smul]
  congr 1
  funext i
  ring

theorem weighted_mem (c d : ι → ℝ) : qX (fun i => c i*d i) ∈ tang c d := by
  have h := bracket_actualTangents (gen c d) true false
  change qZ c*qY d-qY d*qZ c ∈ tang c d at h
  rw [bracket_zy] at h
  have hh := (tang c d).smul_mem (1/2 : ℝ) h
  simpa only [smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul] using hh

theorem weighted_sq_mem {c d f : ι → ℝ} (hf : qX f ∈ tang c d) :
    qX (fun i => c i^2*f i) ∈ tang c d := by
  have h := bracket_closed_actualTangents (gen c d) true (bracket_closed_actualTangents (gen c d) true hf)
  change qZ c*(qZ c*qX f-qX f*qZ c)-(qZ c*qX f-qX f*qZ c)*qZ c ∈ tang c d at h
  rw [double_zx] at h
  have hh := (tang c d).smul_mem (-1/4 : ℝ) h
  simpa only [smul_smul,show (-1/4:ℝ)*(-4)=1 by norm_num,one_smul] using hh

theorem weighted_power_mem (c d : ι → ℝ) (k : ℕ) :
    qX (fun i => c i*d i*(c i^2)^k) ∈ tang c d := by
  induction k with
  | zero => simpa using weighted_mem c d
  | succ k ih =>
    convert weighted_sq_mem ih using 1
    congr 1; funext i; ring

theorem weighted_polynomial_mem (c d : ι → ℝ) (P : Polynomial ℝ) :
    qX (fun i => c i*d i*P.eval (c i^2)) ∈ tang c d := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simpa [Polynomial.eval_add,mul_add] using (tang c d).add_mem hp hq
  | monomial k r =>
    convert (tang c d).smul_mem r (weighted_power_mem c d k) using 1
    rw [← qX_smul]
    congr 1; funext i; simp [Polynomial.eval_monomial]; ring

theorem all_X_mem (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (hi : Function.Injective (fun i => c i^2)) (f : ι → ℝ) : qX f ∈ tang c d := by
  obtain ⟨P,hP⟩ := SeedControl.interpolate_finite_fibers (fun i => c i^2) (fun i => f i/(c i*d i))
    (fun i j h => by rw [hi h])
  convert weighted_polynomial_mem c d P using 1
  congr 1; funext i
  rw [hP i]
  exact (mul_div_cancel₀ _ (hn i)).symm

theorem all_Y_mem (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (hi : Function.Injective (fun i => c i^2)) (f : ι → ℝ) : qY f ∈ tang c d := by
  have h := bracket_closed_actualTangents (gen c d) true (all_X_mem c d hn hi (fun i => f i/(-2*c i)))
  change qZ c*qX _-qX _*qZ c ∈ tang c d at h
  rw [bracket_zx] at h
  convert h using 1
  congr 1; funext i
  have hc : c i ≠ 0 := (mul_ne_zero_iff.mp (hn i)).1
  field_simp

theorem all_Z_mem (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (hi : Function.Injective (fun i => c i^2)) (f : ι → ℝ) : qZ f ∈ tang c d := by
  have h := bracket_closed_actualTangents (gen c d) false (all_X_mem c d hn hi (fun i => f i/(2*d i)))
  change qY d*qX _-qX _*qY d ∈ tang c d at h
  rw [bracket_yx] at h
  convert h using 1
  congr 1; funext i
  have hd : d i ≠ 0 := (mul_ne_zero_iff.mp (hn i)).2
  field_simp

end QuaternionControl

namespace QuaternionControl
open PulseControl ExactPulseControl
variable {ι : Type*} [Fintype ι]
local instance : NormedAlgebra ℚ (QField ι) := NormedAlgebra.restrictScalars ℚ ℝ (QField ι)

 
def imagProj : QField ι →L[ℝ] (ι → Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q i => ![(q i).imI,(q i).imJ,(q i).imK]
      map_add' := by intro q r; ext i j; fin_cases j <;> rfl
      map_smul' := by intro t q; ext i j; fin_cases j <;> rfl }

@[simp] theorem imagProj_apply (q : QField ι) (i : ι) :
    imagProj q i = ![(q i).imI,(q i).imJ,(q i).imK] := rfl

@[simp] theorem imagProj_one : imagProj (1 : QField ι) = 0 := by
  ext i j; fin_cases j <;> rfl

omit [Fintype ι] in
theorem gen_skew (c d : ι → ℝ) (a : Bool) : gen c d a ∈ skewAdjoint (QField ι) := by
  rw [skewAdjoint.mem_iff]
  funext i
  change star (gen c d a i : Quaternion ℝ) = -(gen c d a i : Quaternion ℝ)
  cases a <;> change star (⟨0,_,_,0⟩ : Quaternion ℝ) = -(⟨0,_,_,0⟩ : Quaternion ℝ) <;> ext <;> simp

theorem tangent_projection_surjective (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (hi : Function.Injective (fun i => c i^2)) (r : ι → Fin 3 → ℝ) :
    ∃ X ∈ actualTangents (gen c d), imagProj X=r := by
  refine ⟨qZ (fun i => r i 0)+qY (fun i => r i 1)+qX (fun i => r i 2),
    (tang c d).add_mem ((tang c d).add_mem (all_Z_mem c d hn hi _) (all_Y_mem c d hn hi _))
      (all_X_mem c d hn hi _),?_⟩
  rw [map_add,map_add]
  ext i j
  fin_cases j <;> simp [imagProj,qZ,qY,qX]

theorem positive_re_nhds : {q : QField ι | ∀ i, 0 < (q i).re} ∈ 𝓝 1 := by
  have h (i : ι) : ∀ᶠ q : QField ι in 𝓝 1, 0 < (q i).re :=
    (Quaternion.continuous_re.comp (continuous_apply i)).continuousAt.eventually (eventually_gt_nhds (by change (0 : ℝ) < 1; norm_num : (0 : ℝ) < (1 : Quaternion ℝ).re))
  exact Filter.eventually_all.mpr h

theorem normSq_of_reachable (c d : ι → ℝ) {q : QField ι} (hq : q ∈ zeroClockWords (gen c d)) (i : ι) :
    Quaternion.normSq (q i)=1 := by
  have hU := zeroClockWords_le_unitary (gen c d) (gen_skew c d) hq
  have h := congrFun (Unitary.star_mul_self_of_mem hU) i
  change star (q i)*q i=1 at h
  rw [Quaternion.star_mul_self] at h
  exact congrArg QuaternionAlgebra.re h

theorem unit_positive_imag_injective {p q : Quaternion ℝ} (hp : Quaternion.normSq p=1)
    (hq : Quaternion.normSq q=1) (hp0 : 0<p.re) (hq0 : 0<q.re)
    (hi : p.imI=q.imI) (hj : p.imJ=q.imJ) (hk : p.imK=q.imK) : p=q := by
  have hr : p.re=q.re := by
    rw [Quaternion.normSq_def'] at hp hq
    rw [hi,hj,hk] at hp
    nlinarith
  exact QuaternionAlgebra.ext hr hi hj hk

theorem locally_exact (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (hi : Function.Injective (fun i => c i^2)) :
    ∀ᶠ q : QField ι in 𝓝 1,
      (∀ i, Quaternion.normSq (q i)=1) → q ∈ zeroClockWords (gen c d) := by
  have h := surjective_tangents_reachable_nhds (gen c d) imagProj
    (tangent_projection_surjective c d hn hi) _ positive_re_nhds
  have hh : ∀ᶠ q : QField ι in 𝓝 1,
      ∃ r ∈ zeroClockWords (gen c d), (∀ i, 0<(r i).re) ∧ imagProj r=imagProj q :=
    imagProj.continuous.continuousAt h
  filter_upwards [hh,positive_re_nhds (ι := ι)] with q ⟨r,hr,hr0,he⟩ hq0 hq
  have hre : r=q := by
    funext i
    exact unit_positive_imag_injective (normSq_of_reachable c d hr i) (hq i) (hr0 i) (hq0 i)
      (congrFun (congrFun he i) 0) (congrFun (congrFun he i) 1) (congrFun (congrFun he i) 2)
  simpa [hre] using hr

 
theorem exact_imaginary (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (hi : Function.Injective (fun i => c i^2)) (X : QField ι) (hX : ∀ i, (X i).re=0) :
    NormedSpace.exp X ∈ zeroClockWords (gen c d) := by
  have hs : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) • X) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    convert! ht.smul_const X using 1
    simp
  have he : Tendsto (fun n : ℕ => NormedSpace.exp (((n : ℝ)⁻¹) • X)) atTop (𝓝 1) := by
    convert! NormedSpace.exp_continuous.continuousAt.tendsto.comp hs using 1
    simp
  have hm := he.eventually (locally_exact c d hn hi)
  obtain ⟨n,hnpos,hmem⟩ := (eventually_gt_atTop 0 |>.and hm).exists
  have hnorm (i : ι) : Quaternion.normSq ((NormedSpace.exp (((n : ℝ)⁻¹) • X)) i)=1 := by
    have heval : (NormedSpace.exp (((n : ℝ)⁻¹) • X)) i =
        NormedSpace.exp (((n : ℝ)⁻¹) • X i) := by
      convert! NormedSpace.map_exp (Pi.evalRingHom (fun _ : ι => Quaternion ℝ) i) (continuous_apply i) (((n : ℝ)⁻¹) • X)
    rw [heval,Quaternion.normSq_exp,Quaternion.re_smul,hX,smul_zero]
    simp
  have hr := (zeroClockWords (gen c d)).pow_mem (hmem hnorm) n
  convert hr using 1
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hnpos)),one_smul]

end QuaternionControl

namespace PulseControl
variable {A B κ : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [NormedRing B] [NormedAlgebra ℝ B] [DecidableEq κ]
  [CompleteSpace A] [CompleteSpace B]
local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
local instance : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B

omit [DecidableEq κ] [CompleteSpace B] in
theorem pulseValue_map (F : A →ₐ[ℝ] B) (hF : Continuous F) (G : κ → A) (w : List (κ × ℝ)) :
    F (pulseValue G w) = pulseValue (F ∘ G) w := by
  induction w with
  | nil => simp
  | cons p w ih =>
    simp only [pulseValue,List.map_cons,List.prod_cons] at ih ⊢
    rw [map_mul,ih]
    congr 1
    convert! NormedSpace.map_exp F.toRingHom hF (p.2 • G p.1) using 1
    change NormedSpace.exp (p.2 • F (G p.1)) = NormedSpace.exp (F (p.2 • G p.1))
    rw [map_smul]

omit [CompleteSpace B] in
theorem zeroClock_map (F : A →ₐ[ℝ] B) (hF : Continuous F) (G : κ → A) {U : A}
    (hU : U ∈ zeroClockWords G) : F U ∈ zeroClockWords (F ∘ G) := by
  obtain ⟨w,hw,he⟩ := hU
  exact ⟨w,hw,by rw [← pulseValue_map F hF G w,he]⟩
end PulseControl

namespace QuaternionControl
open PulseControl
variable {ι : Type*} [Fintype ι]
local instance : NormedAlgebra ℚ (QField ι) := NormedAlgebra.restrictScalars ℚ ℝ (QField ι)

 
def flipIJ : Quaternion ℝ →ₐ[ℝ] Quaternion ℝ where
  toFun q := ⟨q.re,-q.imI,-q.imJ,q.imK⟩
  map_one' := by change (⟨1, -0, -0, 0⟩ : Quaternion ℝ) = 1; ext <;> simp
  map_zero' := by change (⟨0, -0, -0, 0⟩ : Quaternion ℝ) = 0; ext <;> simp
  map_add' q r := by
    change (⟨(q+r).re,-(q+r).imI,-(q+r).imJ,(q+r).imK⟩ : Quaternion ℝ) =
      (⟨q.re,-q.imI,-q.imJ,q.imK⟩ : Quaternion ℝ)+(⟨r.re,-r.imI,-r.imJ,r.imK⟩ : Quaternion ℝ)
    ext <;> simp <;> ring
  map_mul' q r := by
    change (⟨(q*r).re,-(q*r).imI,-(q*r).imJ,(q*r).imK⟩ : Quaternion ℝ) =
      (⟨q.re,-q.imI,-q.imJ,q.imK⟩ : Quaternion ℝ)*(⟨r.re,-r.imI,-r.imJ,r.imK⟩ : Quaternion ℝ)
    ext <;> simp <;> ring
  commutes' r := by ext <;> simp

theorem flipIJ_apply (q : Quaternion ℝ) : flipIJ q = ⟨q.re,-q.imI,-q.imJ,q.imK⟩ := rfl

 
def expand {κ : Type*} (key : ι → κ) (sgn : ι → Bool) : QField κ →ₐ[ℝ] QField ι where
  toFun q i := if sgn i then flipIJ (q (key i)) else q (key i)
  map_one' := by
    funext i
    change (if sgn i then flipIJ (1 : Quaternion ℝ) else (1 : Quaternion ℝ)) = 1
    split_ifs <;> simp
  map_zero' := by
    funext i
    change (if sgn i then flipIJ (0 : Quaternion ℝ) else (0 : Quaternion ℝ)) = 0
    split_ifs <;> simp
  map_add' q r := by
    funext i
    change (if sgn i then flipIJ (q (key i)+r (key i)) else q (key i)+r (key i)) =
      (if sgn i then flipIJ (q (key i)) else q (key i))+(if sgn i then flipIJ (r (key i)) else r (key i))
    split_ifs <;> simp
  map_mul' q r := by
    funext i
    change (if sgn i then flipIJ (q (key i)*r (key i)) else q (key i)*r (key i)) =
      (if sgn i then flipIJ (q (key i)) else q (key i))*(if sgn i then flipIJ (r (key i)) else r (key i))
    split_ifs <;> simp
  commutes' r := by
    funext i
    change (if sgn i then flipIJ (algebraMap ℝ (Quaternion ℝ) r) else algebraMap ℝ (Quaternion ℝ) r) =
      algebraMap ℝ (Quaternion ℝ) r
    split_ifs
    · exact flipIJ.commutes r
    · rfl

omit [Fintype ι] in
theorem expand_gen {κ : Type*} (key : ι → κ) (sgn : ι → Bool)
    (c d : ι → ℝ) (C D : κ → ℝ)
    (hc : ∀ i, c i = if sgn i then -C (key i) else C (key i))
    (hd : ∀ i, d i = if sgn i then -D (key i) else D (key i)) :
    (expand key sgn) ∘ gen C D = gen c d := by
  funext a i
  cases a
  · change (if sgn i then flipIJ (⟨0,0,D (key i),0⟩ : Quaternion ℝ) else (⟨0,0,D (key i),0⟩ : Quaternion ℝ)) =
      (⟨0,0,d i,0⟩ : Quaternion ℝ)
    rw [hd i]
    cases h : sgn i
    · rfl
    · change (⟨0,-(0:ℝ),-D (key i),0⟩ : Quaternion ℝ) = ⟨0,0,-D (key i),0⟩
      simp only [neg_zero]
  · change (if sgn i then flipIJ (⟨0,C (key i),0,0⟩ : Quaternion ℝ) else (⟨0,C (key i),0,0⟩ : Quaternion ℝ)) =
      (⟨0,c i,0,0⟩ : Quaternion ℝ)
    rw [hc i]
    cases h : sgn i
    · rfl
    · change (⟨0,-C (key i),-(0:ℝ),0⟩ : Quaternion ℝ) = ⟨0,-C (key i),0,0⟩
      simp only [neg_zero]

omit [Fintype ι] in
theorem expand_qX {κ : Type*} (key : ι → κ) (sgn : ι → Bool) (t : ℝ) :
    expand key sgn (qX (fun _ => t)) = qX (fun _ => t) := by
  funext i
  change (if sgn i then flipIJ (⟨0,0,0,t⟩ : Quaternion ℝ) else (⟨0,0,0,t⟩ : Quaternion ℝ)) =
    (⟨0,0,0,t⟩ : Quaternion ℝ)
  cases h : sgn i
  · rfl
  · change (⟨0,-(0:ℝ),-(0:ℝ),t⟩ : Quaternion ℝ) = ⟨0,0,0,t⟩
    simp only [neg_zero]

 
theorem common_X_exact (c d : ι → ℝ) (hn : ∀ i, c i*d i ≠ 0)
    (heq : ∀ i j, c i^2=c j^2 → (c i=c j ∧ d i=d j) ∨ (c i= -c j ∧ d i= -d j))
    (t : ℝ) : NormedSpace.exp (qX (fun _ => t)) ∈ zeroClockWords (gen c d) := by
  classical
  let κ := Set.range (fun i => c i^2)
  let : Fintype κ := Fintype.ofFinite κ
  let key : ι → κ := fun i => ⟨c i^2,⟨i,rfl⟩⟩
  let rep : κ → ι := fun k => Classical.choose k.property
  have hre (k : κ) : c (rep k)^2=k.val := Classical.choose_spec k.property
  let C : κ → ℝ := c ∘ rep
  let D : κ → ℝ := d ∘ rep
  have hC : Function.Injective (fun k => C k^2) := by
    intro k l h
    apply Subtype.ext
    simpa only [C,Function.comp_apply,hre] using h
  have hCD (k : κ) : C k*D k≠0 := hn (rep k)
  let sgn : ι → Bool := fun i => decide (c i ≠ C (key i))
  have hcases (i : ι) := heq i (rep (key i)) (hre (key i)).symm
  have hc (i : ι) : c i = if sgn i then -C (key i) else C (key i) := by
    simp only [sgn, decide_eq_true_eq, ne_eq,ite_not]
    split_ifs with h
    · exact h
    · exact ((hcases i).resolve_left (fun hh => h hh.1)).1
  have hd (i : ι) : d i = if sgn i then -D (key i) else D (key i) := by
    simp only [sgn, decide_eq_true_eq, ne_eq,ite_not]
    split_ifs with h
    · rcases hcases i with hh | hh
      · exact hh.2
      · exfalso
        have hz := (mul_ne_zero_iff.mp (hn i)).1
        apply hz
        dsimp [C,Function.comp_apply] at h
        linarith [hh.1]
    · exact ((hcases i).resolve_left (fun hh => h hh.1)).2
  have hreach := exact_imaginary C D hCD hC (qX (fun _ => t)) (fun _ => rfl)
  let F := expand key sgn
  have hF : Continuous F := F.toLinearMap.continuous_of_finiteDimensional
  have hmap := zeroClock_map F hF (gen C D) hreach
  rw [show F ∘ gen C D = gen c d from expand_gen key sgn c d C D hc hd] at hmap
  have hExp : F (NormedSpace.exp (qX (fun _ : κ => t))) =
      NormedSpace.exp (qX (fun _ : ι => t)) := by
    convert! NormedSpace.map_exp F.toRingHom hF (qX (fun _ : κ => t)) using 1
    change NormedSpace.exp (qX (fun _ : ι => t)) = NormedSpace.exp (expand key sgn (qX (fun _ : κ => t)))
    rw [expand_qX]
  rwa [hExp] at hmap
end QuaternionControl

open scoped Matrix Matrix.Norms.L2Operator
namespace QuaternionControl

def rotateIJ (a b : ℝ) (h : a^2+b^2=1) : Quaternion ℝ →ₐ[ℝ] Quaternion ℝ where
  toFun q := ⟨q.re,a*q.imI-b*q.imJ,b*q.imI+a*q.imJ,q.imK⟩
  map_zero' := by
    change (⟨0,a*0-b*0,b*0+a*0,0⟩ : Quaternion ℝ) = 0
    ext <;> simp
  map_one' := by
    change (⟨1,a*0-b*0,b*0+a*0,0⟩ : Quaternion ℝ) = 1
    ext <;> simp
  map_add' q r := by
    change (⟨(q+r).re,a*(q+r).imI-b*(q+r).imJ,b*(q+r).imI+a*(q+r).imJ,(q+r).imK⟩ : Quaternion ℝ) =
      (⟨q.re,a*q.imI-b*q.imJ,b*q.imI+a*q.imJ,q.imK⟩ : Quaternion ℝ)+
      (⟨r.re,a*r.imI-b*r.imJ,b*r.imI+a*r.imJ,r.imK⟩ : Quaternion ℝ)
    ext <;> simp <;> ring
  map_mul' q r := by
    change (⟨(q*r).re,a*(q*r).imI-b*(q*r).imJ,b*(q*r).imI+a*(q*r).imJ,(q*r).imK⟩ : Quaternion ℝ) =
      (⟨q.re,a*q.imI-b*q.imJ,b*q.imI+a*q.imJ,q.imK⟩ : Quaternion ℝ)*
      (⟨r.re,a*r.imI-b*r.imJ,b*r.imI+a*r.imJ,r.imK⟩ : Quaternion ℝ)
    ext <;> simp
    · nlinarith [h, congrArg (fun x => x*(q.imI*r.imI+q.imJ*r.imJ)) h]
    · ring
    · ring
    · nlinarith [h, congrArg (fun x => x*(q.imI*r.imJ-q.imJ*r.imI)) h]
  commutes' r := by
    change (⟨r,a*0-b*0,b*0+a*0,0⟩ : Quaternion ℝ) = algebraMap ℝ (Quaternion ℝ) r
    ext <;> simp

 
def toPauli : Quaternion ℝ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun q := !![(q.re:ℂ)-Complex.I*q.imI, -(q.imJ:ℂ)+Complex.I*q.imK;
    (q.imJ:ℂ)+Complex.I*q.imK, (q.re:ℂ)+Complex.I*q.imI]
  map_zero' := by
    change !![(0:ℂ)-Complex.I*0,-0+Complex.I*0;0+Complex.I*0,0+Complex.I*0] = 0
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_one' := by
    change !![(1:ℂ)-Complex.I*0,-0+Complex.I*0;0+Complex.I*0,1+Complex.I*0] = 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' q r := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_mul' q r := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  commutes' r := by
    change !![(r:ℂ)-Complex.I*0,-0+Complex.I*0;0+Complex.I*0,(r:ℂ)+Complex.I*0] = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) r
    ext i j; fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one]

end QuaternionControl

end

end OAI
