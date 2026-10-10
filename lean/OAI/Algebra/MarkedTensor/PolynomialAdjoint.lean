import Mathlib
import OAI.Algebra.MarkedTensor.AdjointCoordinates

namespace OAI

/-! Nine polynomial conjugators spanning every adjoint-coordinate endomorphism. -/

noncomputable section
open scoped BigOperators commutatorElement
open Matrix

namespace MarkedTensor
namespace Adjoint

variable {K : Type*} [Field K]

abbrev Mat₂ (K : Type*) := Matrix (Fin 2) (Fin 2) K
abbrev Mat₃ (K : Type*) := Matrix (Fin 3) (Fin 3) K
abbrev Vec₃ (K : Type*) := Fin 3 → K

abbrev mat (g : SpecialLinearGroup (Fin 2) K) : Mat₂ K := g

 
def traceless (v : Vec₃ K) : Mat₂ K := !![v 1, v 0; v 2, -v 1]

def extract (A : Mat₂ K) : Vec₃ K := ![A 0 1, A 0 0, A 1 0]

def tracelessLM : Vec₃ K →ₗ[K] Mat₂ K where
  toFun := traceless
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [traceless, add_comm]
  map_smul' c x := by ext i j; fin_cases i <;> fin_cases j <;> simp [traceless]

def extractLM : Mat₂ K →ₗ[K] Vec₃ K where
  toFun := extract
  map_add' x y := by ext i; fin_cases i <;> simp [extract]
  map_smul' c x := by ext i; fin_cases i <;> simp [extract]

def conjugationLM (g : SpecialLinearGroup (Fin 2) K) : Mat₂ K →ₗ[K] Mat₂ K where
  toFun A := mat g * A * mat g⁻¹
  map_add' A B := by simp only [mul_add, add_mul]
  map_smul' c A := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

 
def adjoint (g : SpecialLinearGroup (Fin 2) K) : Vec₃ K →ₗ[K] Vec₃ K :=
  extractLM ∘ₗ conjugationLM g ∘ₗ tracelessLM

lemma traceless_extract (v : Vec₃ K) : extract (traceless v) = v := by
  ext i; fin_cases i <;> simp [extract, traceless]

lemma extract_traceless (A : Mat₂ K) (hA : Matrix.trace A = 0) :
    traceless (extract A) = A := by
  have hdiag : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using hA
  ext i j; fin_cases i <;> fin_cases j <;> simp [traceless, extract]
  exact neg_eq_of_add_eq_zero_right hdiag

lemma traceless_adjoint (g : SpecialLinearGroup (Fin 2) K) (v : Vec₃ K) :
    traceless (adjoint g v) = mat g * traceless v * mat g⁻¹ := by
  apply extract_traceless
  change Matrix.trace (mat g * traceless v * mat g⁻¹) = 0
  rw [Matrix.trace_mul_cycle]
  have hi : mat g⁻¹ * mat g = 1 :=
    congrArg mat (inv_mul_cancel g)
  rw [hi, one_mul]
  simp [Matrix.trace, Fin.sum_univ_two, traceless]

 
def conjugator (x y : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1 + x*y, x; y, 1], by simp [Matrix.det_fin_two]⟩

lemma conjugator_inv (x y : K) :
    mat (conjugator x y)⁻¹ =
      !![1, -x; -y, 1 + x*y] := by
  change Matrix.adjugate (!![1 + x*y, x; y, 1] : Mat₂ K) = _
  rw [Matrix.adjugate_fin_two]
  rfl

 
def adjointMatrix (x y : K) : Mat₃ K :=
  !![(1 + x*y)^2, -2*x*(1 + x*y), -x^2;
     -y*(1 + x*y), 1 + 2*x*y, x;
     -y^2, 2*y, 1]

lemma toMatrix_adjoint (x y : K) :
    LinearMap.toMatrix' (adjoint (conjugator x y)) = adjointMatrix x y := by
  ext i j
  change extract (mat (conjugator x y) * traceless (Pi.single j 1) *
    mat (conjugator x y)⁻¹) i = adjointMatrix x y i j
  rw [conjugator_inv]
  fin_cases i <;> fin_cases j <;>
    simp [extract, traceless, mat, conjugator, adjointMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

 
def coefficient : Fin 3 → Fin 3 → Mat₃ K := ![
  ![1, !![0,0,0; -1,0,0; 0,2,0], !![0,0,0; 0,0,0; -1,0,0]],
  ![!![0,-2,0; 0,0,1; 0,0,0], !![2,0,0; 0,2,0; 0,0,0],
    !![0,0,0; -1,0,0; 0,0,0]],
  ![!![0,0,-1; 0,0,0; 0,0,0], !![0,-2,0; 0,0,0; 0,0,0],
    !![1,0,0; 0,0,0; 0,0,0]]]

@[simp] lemma coefficient00 : coefficient (K := K) 0 0 = 1 := rfl
@[simp] lemma coefficient01 : coefficient (K := K) 0 1 =
    !![0,0,0; -1,0,0; 0,2,0] := rfl
@[simp] lemma coefficient02 : coefficient (K := K) 0 2 =
    !![0,0,0; 0,0,0; -1,0,0] := rfl
@[simp] lemma coefficient10 : coefficient (K := K) 1 0 =
    !![0,-2,0; 0,0,1; 0,0,0] := rfl
@[simp] lemma coefficient11 : coefficient (K := K) 1 1 =
    !![2,0,0; 0,2,0; 0,0,0] := rfl
@[simp] lemma coefficient12 : coefficient (K := K) 1 2 =
    !![0,0,0; -1,0,0; 0,0,0] := rfl
@[simp] lemma coefficient20 : coefficient (K := K) 2 0 =
    !![0,0,-1; 0,0,0; 0,0,0] := rfl
@[simp] lemma coefficient21 : coefficient (K := K) 2 1 =
    !![0,-2,0; 0,0,0; 0,0,0] := rfl
@[simp] lemma coefficient22 : coefficient (K := K) 2 2 =
    !![1,0,0; 0,0,0; 0,0,0] := rfl

def quadratic {V : Type*} [AddCommGroup V] [Module K V] (a b c : V) (t : K) : V :=
  a + t • b + t^2 • c

lemma quadratic_coefficients_mem [CharZero K] {V : Type*} [AddCommGroup V] [Module K V]
    (W : Submodule K V) (a b c : V) {s : K} (hs : s ≠ 0)
    (h0 : quadratic a b c (0 : K) ∈ W) (h1 : quadratic a b c s ∈ W)
    (h2 : quadratic a b c (2*s) ∈ W) : a ∈ W ∧ b ∈ W ∧ c ∈ W := by
  have ha : a ∈ W := by simpa [quadratic] using h0
  have he : quadratic a b c (2*s) - (2 : K) • quadratic a b c s + a =
      (2*s^2) • c := by unfold quadratic; module
  have hc' : (2*s^2) • c ∈ W := he ▸ W.add_mem (W.sub_mem h2 (W.smul_mem 2 h1)) ha
  have hc : c ∈ W := by
    have h := W.smul_mem (2*s^2)⁻¹ hc'
    simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero (by norm_num : (2 : K) ≠ 0)
      (pow_ne_zero 2 hs)), one_smul] using h
  have hb' : s • b ∈ W := by
    convert W.sub_mem (W.sub_mem h1 ha) (W.smul_mem (s^2) hc) using 1
    unfold quadratic
    module
  have hb : b ∈ W := by
    have h := W.smul_mem s⁻¹ hb'
    simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using h
  exact ⟨ha, hb, hc⟩

def rowPolynomial (p : Fin 3) (y : K) : Mat₃ K :=
  quadratic (coefficient p 0) (coefficient p 1) (coefficient p 2) y

lemma expansion (x y : K) : adjointMatrix x y =
    quadratic (rowPolynomial 0 y) (rowPolynomial 1 y) (rowPolynomial 2 y) x := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [adjointMatrix, quadratic, rowPolynomial, coefficient] <;> ring

variable [CharZero K]

lemma coefficients_mem {W : Submodule K (Mat₃ K)} {s : K} (hs : s ≠ 0)
    (h : ∀ a b : Fin 3, adjointMatrix ((a : K)*s) ((b : K)*s) ∈ W)
    (p q : Fin 3) : coefficient (K := K) p q ∈ W := by
  have hr (b : Fin 3) : ∀ p : Fin 3, rowPolynomial p ((b : K)*s) ∈ W := by
    have hh := quadratic_coefficients_mem W
      (rowPolynomial 0 ((b : K)*s)) (rowPolynomial 1 ((b : K)*s))
      (rowPolynomial 2 ((b : K)*s)) hs
      (by simpa only [← expansion, Fin.val_zero, Nat.cast_zero, zero_mul] using h 0 b)
      (by simpa only [← expansion, Fin.val_one, Nat.cast_one, one_mul] using h 1 b)
      (by simpa only [← expansion, Fin.val_two, Nat.cast_ofNat] using h 2 b)
    intro p; fin_cases p
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2
  have hh := quadratic_coefficients_mem W (coefficient p 0) (coefficient p 1)
    (coefficient p 2) hs
    (by simpa only [rowPolynomial, Fin.val_zero, Nat.cast_zero, zero_mul] using hr 0 p)
    (by simpa only [rowPolynomial, Fin.val_one, Nat.cast_one, one_mul] using hr 1 p)
    (by simpa only [rowPolynomial, Fin.val_two, Nat.cast_ofNat] using hr 2 p)
  fin_cases q
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

lemma span_eq_top_of_coefficients {W : Submodule K (Mat₃ K)}
    (h : ∀ p q : Fin 3, coefficient p q ∈ W) : W = ⊤ := by
  have hu (i j : Fin 3) : Matrix.single i j (1 : K) ∈ W := by
    fin_cases i <;> fin_cases j
    · convert h 2 2 using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.smul_mem (-1/2 : K) (h 2 1) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.neg_mem (h 2 0) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.neg_mem (h 1 2) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.sub_mem (W.smul_mem (1/2 : K) (h 1 1)) (h 2 2) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.sub_mem (h 1 0) (h 2 1) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.neg_mem (h 0 2) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.smul_mem (1/2 : K) (W.sub_mem (h 0 1) (h 1 2)) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
    · convert W.sub_mem (h 0 0) (W.smul_mem (1/2 : K) (h 1 1)) using 1
      ext row column
      fin_cases row <;> fin_cases column <;> norm_num [Matrix.single]
  apply top_unique
  intro B _
  rw [Matrix.matrix_eq_sum_single B]
  apply W.sum_mem; intro i _
  apply W.sum_mem; intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using W.smul_mem (B i j) (hu i j)

 
lemma nine_matrix_span {s : K} (hs : s ≠ 0) :
    Submodule.span K (Set.range (fun ab : Fin 3 × Fin 3 =>
      adjointMatrix ((ab.1 : K)*s) ((ab.2 : K)*s))) = ⊤ := by
  apply span_eq_top_of_coefficients
  apply coefficients_mem hs
  intro a b
  exact Submodule.subset_span ⟨(a,b), rfl⟩

 

theorem vertex_adjoint_span {s : K} (hs : s ≠ 0) :
    Submodule.span K (Set.range (fun ab : Fin 3 × Fin 3 =>
      adjoint (conjugator ((ab.1 : K)*s) ((ab.2 : K)*s)))) = ⊤ := by
  have ht : Submodule.span K (Set.range (fun ab : Fin 3 × Fin 3 =>
      LinearMap.toMatrix' (adjoint (conjugator ((ab.1 : K)*s) ((ab.2 : K)*s))))) = ⊤ := by
    simpa only [toMatrix_adjoint] using nine_matrix_span hs
  have hh := congrArg (Submodule.map Matrix.toLin'.toLinearMap) ht
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    LinearEquiv.range, Function.comp_def, LinearEquiv.coe_coe,
    Matrix.toLin'_toMatrix'] using hh

end Adjoint
end MarkedTensor
end

end OAI
