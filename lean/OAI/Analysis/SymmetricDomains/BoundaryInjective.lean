import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

open Set Metric Complex
open scoped Topology
noncomputable section
namespace Release061.Wiener
open scoped BigOperators ComplexConjugate Topology
open Set Filter

abbrev Poly := AddMonoidAlgebra ℂ ℤ

noncomputable def weight (n : ℤ) : ℝ := 1+|(n : ℝ)|
lemma weight_pos (n : ℤ) : 0 < weight n := by dsimp [weight]; positivity
lemma one_le_weight (n : ℤ) : 1 ≤ weight n := by simp [weight]
lemma weight_add_le (n m : ℤ) : weight (n+m) ≤ weight n*weight m := by
  dsimp [weight]
  rw [Int.cast_add]
  have h := abs_add_le (n : ℝ) (m : ℝ)
  have hnm : 0 ≤ |(n : ℝ)| * |(m : ℝ)| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

noncomputable def wnorm (p : Poly) : ℝ := p.coeff.sum (fun n z => weight n*‖z‖)

lemma wnorm_eq_sum (p : Poly) {s : Finset ℤ} (hs : p.coeff.support ⊆ s) :
    wnorm p = ∑ n ∈ s, weight n*‖p.coeff n‖ :=
  Finsupp.sum_of_support_subset p.coeff hs _ (by simp)

lemma wnorm_nonneg (p : Poly) : 0 ≤ wnorm p := by
  unfold wnorm Finsupp.sum
  exact Finset.sum_nonneg fun n _ => mul_nonneg (weight_pos n).le (norm_nonneg _)

lemma wnorm_zero : wnorm 0 = 0 := by simp [wnorm]

lemma wnorm_add_le (p q : Poly) : wnorm (p+q) ≤ wnorm p+wnorm q := by
  classical
  let s := p.coeff.support ∪ q.coeff.support
  have hp : p.coeff.support ⊆ s := Finset.subset_union_left
  have hq : q.coeff.support ⊆ s := Finset.subset_union_right
  have hpq : (p+q).coeff.support ⊆ s := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  rw [wnorm_eq_sum _ hpq,wnorm_eq_sum _ hp,wnorm_eq_sum _ hq,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply]
  calc weight n*‖p.coeff n+q.coeff n‖ ≤ weight n*(‖p.coeff n‖+‖q.coeff n‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (weight_pos n).le
    _ = _ := by ring

lemma wnorm_neg (p : Poly) : wnorm (-p) = wnorm p := by
  simp [wnorm,Finsupp.sum_neg_index]

lemma wnorm_eq_zero {p : Poly} (hp : wnorm p = 0) : p = 0 := by
  classical
  have hz : ∀ n ∈ p.coeff.support, weight n*‖p.coeff n‖ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun n _ => mul_nonneg (weight_pos n).le (norm_nonneg _))).mp hp
  apply AddMonoidAlgebra.ext
  ext n
  by_cases hn : n ∈ p.coeff.support
  · exact norm_eq_zero.mp ((mul_eq_zero.mp (hz n hn)).resolve_left (weight_pos n).ne')
  · simpa using Finsupp.notMem_support_iff.mp hn

lemma wnorm_single (n : ℤ) (z : ℂ) : wnorm (.single n z) = weight n*‖z‖ := by
  unfold wnorm
  rw [AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)

lemma wnorm_sum_le {ι : Type*} (s : Finset ι) (p : ι → Poly) :
    wnorm (∑ i ∈ s, p i) ≤ ∑ i ∈ s, wnorm (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (wnorm_add_le _ _).trans (add_le_add (le_refl _) ih)

lemma wnorm_mul_le (p q : Poly) : wnorm (p*q) ≤ wnorm p*wnorm q := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  calc
    _ ≤ ∑ n ∈ p.coeff.support,
        ∑ m ∈ q.coeff.support, wnorm (.single (n+m) (p.coeff n*q.coeff m)) :=
      (wnorm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => wnorm_sum_le _ _)
    _ ≤ ∑ n ∈ p.coeff.support,
        ∑ m ∈ q.coeff.support, (weight n*‖p.coeff n‖)*(weight m*‖q.coeff m‖) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro m _
      rw [wnorm_single,norm_mul]
      calc _ ≤ (weight n*weight m)*(‖p.coeff n‖*‖q.coeff m‖) :=
              mul_le_mul_of_nonneg_right (weight_add_le n m) (by positivity)
        _ = _ := by ring
    _ = wnorm p*wnorm q := by simp only [wnorm,Finsupp.sum,Finset.sum_mul_sum]

noncomputable def ringNorm : RingNorm Poly where
  toFun := wnorm
  map_zero' := wnorm_zero
  add_le' := wnorm_add_le
  neg' := wnorm_neg
  mul_le' := wnorm_mul_le
  eq_zero_of_map_eq_zero' := fun _ => wnorm_eq_zero

noncomputable instance : NormedCommRing Poly where
  toNormedRing := ringNorm.toNormedRing
  mul_comm := mul_comm

lemma norm_def (p : Poly) : ‖p‖ = wnorm p := rfl

lemma wnorm_smul (c : ℂ) (p : Poly) : wnorm (c • p) = ‖c‖*wnorm p := by
  unfold wnorm
  rw [AddMonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (by simp)]
  simp only [norm_mul,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

noncomputable instance : NormedAlgebra ℂ Poly where
  toAlgebra := inferInstance
  norm_smul_le c p := (wnorm_smul c p).le

noncomputable instance : NormOneClass Poly where
  norm_one := by
    change wnorm (1 : Poly) = 1
    rw [AddMonoidAlgebra.one_def,wnorm_single]
    simp [weight]

abbrev Space := UniformSpace.Completion Poly

example : NormedCommRing Space := inferInstance
example : NormedAlgebra ℂ Space := inferInstance
example : CompleteSpace Space := inferInstance

section Modes
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

def modesLinear (v : ℤ → F) : Poly →ₗ[ℂ] F :=
  (Finsupp.linearCombination ℂ v).comp (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

lemma modesLinear_apply (v : ℤ → F) (p : Poly) :
    modesLinear v p = p.coeff.sum (fun n z => z • v n) := rfl

lemma modesLinear_bound (v : ℤ → F) {C : ℝ} (hv : ∀ n, ‖v n‖ ≤ C*weight n)
    (p : Poly) : ‖modesLinear v p‖ ≤ C*‖p‖ := by
  simp only [modesLinear_apply,norm_def,wnorm,Finsupp.sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [norm_smul]
  calc ‖p.coeff n‖*‖v n‖ ≤ ‖p.coeff n‖*(C*weight n) :=
        mul_le_mul_of_nonneg_left (hv n) (norm_nonneg _)
    _ = _ := by ring

def modesCLM (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) : Poly →L[ℂ] F :=
  (modesLinear v).mkContinuous C (modesLinear_bound v hv)

variable [CompleteSpace F]
def fromModes (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) : Space →L[ℂ] F :=
  (modesCLM v C hv).extend UniformSpace.Completion.toComplL

lemma fromModes_coe (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) (p : Poly) :
    fromModes v C hv (p : Space) = p.coeff.sum (fun n z => z • v n) :=
  (modesCLM v C hv).extend_eq UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe Poly) p

lemma fromModes_bound (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n) (f : Space) :
    ‖fromModes v C hv f‖ ≤ C*‖f‖ := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih p =>
    rw [fromModes_coe,UniformSpace.Completion.norm_coe]
    exact modesLinear_bound v hv p

lemma fromModes_single (v : ℤ → F) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C*weight n)
    (n : ℤ) (z : ℂ) :
    fromModes v C hv ((AddMonoidAlgebra.single n z : Poly) : Space) = z • v n := by
  rw [fromModes_coe,AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (by simp)
end Modes

instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev Circle := AddCircle (1 : ℝ)

def boundary : Space →L[ℂ] C(Circle,ℂ) :=
  fromModes (fun n => fourier n) 1 (fun n => by simpa only [fourier_norm,one_mul] using one_le_weight n)

lemma boundary_coe (p : Poly) :
    boundary (p : Space) = p.coeff.sum (fun n z => z • fourier n) :=
  fromModes_coe _ _ _ _

lemma boundary_single (n : ℤ) (z : ℂ) :
    boundary ((AddMonoidAlgebra.single n z : Poly) : Space) = z • fourier n :=
  fromModes_single _ _ _ _ _

lemma boundary_norm_le (f : Space) : ‖boundary f‖ ≤ ‖f‖ := by
  simpa only [boundary,one_mul] using fromModes_bound (fun n => (fourier n : C(Circle,ℂ))) 1 (fun n => by simpa only [fourier_norm,one_mul] using one_le_weight n) f

lemma boundary_one : boundary 1 = 1 := by
  rw [← UniformSpace.Completion.coe_one]
  change boundary ((AddMonoidAlgebra.single 0 1 : Poly) : Space) = 1
  rw [boundary_single,one_smul]
  ext; exact fourier_zero

lemma boundary_poly_mul (p q : Poly) : boundary ((p*q : Poly) : Space) =
    boundary (p : Space)*boundary (q : Space) := by
  classical
  rw [AddMonoidAlgebra.mul_def]
  simp only [Finsupp.sum]
  change boundary ((UniformSpace.Completion.toComplL : Poly →L[ℂ] Space) (∑ a ∈ p.coeff.support,
    ∑ b ∈ q.coeff.support, AddMonoidAlgebra.single (a+b) (p.coeff a*q.coeff b))) = _
  simp only [map_sum]
  change (∑ a ∈ p.coeff.support, ∑ b ∈ q.coeff.support,
    boundary ((AddMonoidAlgebra.single (a+b) (p.coeff a*q.coeff b) : Poly) : Space)) = _
  simp_rw [boundary_single]
  rw [boundary_coe,boundary_coe]
  simp only [Finsupp.sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  ext θ
  simp only [ContinuousMap.smul_apply,smul_eq_mul,ContinuousMap.mul_apply,fourier_add]
  ring

lemma boundary_mul (f g : Space) : boundary (f*g) = boundary f*boundary g := by
  induction f,g using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p q => simpa only [← UniformSpace.Completion.coe_mul] using boundary_poly_mul p q

def boundaryAlgHom : Space →ₐ[ℂ] C(Circle,ℂ) where
  toFun := boundary
  map_one' := boundary_one
  map_mul' := boundary_mul
  map_zero' := map_zero boundary
  map_add' := map_add boundary
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one,map_smul,boundary_one]

lemma poly_expansion (p : Poly) :
    (p : Space) = ∑ n ∈ p.coeff.support, ((AddMonoidAlgebra.single n (p.coeff n) : Poly) : Space) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  change (UniformSpace.Completion.toComplL : Poly →L[ℂ] Space) (∑ n ∈ p.coeff.support,
    AddMonoidAlgebra.single n (p.coeff n)) = _
  exact map_sum _ _ _

lemma continuous_eq_of_single {F : Type*} [TopologicalSpace F] [T2Space F]
    {f g : Space → F} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p : Poly, f (p : Space) = g (p : Space)) : f = g := by
  ext x
  exact UniformSpace.Completion.denseRange_coe.induction_on x (isClosed_eq hf hg) h

def conjPoly : Poly →ₗ[ℝ] Poly :=
  (AddMonoidAlgebra.coeffLinearEquiv ℝ).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℝ (fun n : ℤ => -n)).comp
      ((Finsupp.mapRange.linearMap Complex.conjCLE.toLinearMap).comp
        (AddMonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap))

lemma conjPoly_coeff (p : Poly) :
    (conjPoly p).coeff = (p.coeff.mapRange (starRingEnd ℂ) (map_zero _)).mapDomain (fun n => -n) := rfl

lemma conjPoly_single (n : ℤ) (z : ℂ) :
    conjPoly (.single n z) = .single (-n) (conj z) := by
  apply AddMonoidAlgebra.ext
  rw [conjPoly_coeff]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.mapRange_single,Finsupp.mapDomain_single]

lemma conjPoly_norm (p : Poly) : ‖conjPoly p‖ = ‖p‖ := by
  change wnorm (conjPoly p) = wnorm p
  unfold wnorm
  rw [conjPoly_coeff,Finsupp.sum_mapDomain_index_inj (neg_injective : Function.Injective (fun n : ℤ => -n)),
    Finsupp.sum_mapRange_index (by simp)]
  simp [weight]

def conjugate : Space →L[ℝ] Space :=
  ((UniformSpace.Completion.toComplL : Poly →L[ℝ] Space).comp
    (conjPoly.mkContinuous 1 (by intro p; simp [conjPoly_norm]))).extend
      UniformSpace.Completion.toComplL

lemma conjugate_coe (p : Poly) : conjugate (p : Space) = (conjPoly p : Space) := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe Poly) p

lemma conjugate_single (n : ℤ) (z : ℂ) :
    conjugate ((AddMonoidAlgebra.single n z : Poly) : Space) =
      ((AddMonoidAlgebra.single (-n) (conj z) : Poly) : Space) := by
  rw [conjugate_coe,conjPoly_single]

lemma conjugate_norm (f : Space) : ‖conjugate f‖ = ‖f‖ := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p => rw [conjugate_coe,UniformSpace.Completion.norm_coe,UniformSpace.Completion.norm_coe,conjPoly_norm]

lemma conjugate_involutive : Function.Involutive conjugate := by
  intro f
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) continuous_id
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,neg_neg,starRingEnd_self_apply]

lemma boundary_conjugate (f : Space) (θ : Circle) :
    boundary (conjugate f) θ = conj (boundary f θ) := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,boundary_single,ContinuousMap.sum_apply,
      ContinuousMap.smul_apply,smul_eq_mul,map_mul]
    apply Finset.sum_congr rfl
    intro _ _
    rw [fourier_neg]

def multiplier (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) : Space →L[ℂ] Space :=
  fromModes (fun n => ((AddMonoidAlgebra.single n (σ n) : Poly) : Space)) C (by
    intro n
    rw [UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
    calc weight n*‖σ n‖ ≤ weight n*C := mul_le_mul_of_nonneg_left (hσ n) (weight_pos n).le
      _ = C*weight n := mul_comm _ _)

lemma multiplier_single (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) (n : ℤ) (z : ℂ) :
    multiplier σ C hσ ((AddMonoidAlgebra.single n z : Poly) : Space) =
      ((AddMonoidAlgebra.single n (z*σ n) : Poly) : Space) := by
  rw [multiplier,fromModes_single]
  rw [← UniformSpace.Completion.coe_smul]
  congr 1
  apply AddMonoidAlgebra.ext
  ext m
  simp only [AddMonoidAlgebra.coeff_smul,AddMonoidAlgebra.coeff_single,Finsupp.smul_apply,
    Finsupp.single_apply,smul_eq_mul]
  split_ifs <;> simp_all

lemma multiplier_bound (σ : ℤ → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C) (f : Space) :
    ‖multiplier σ C hσ f‖ ≤ C*‖f‖ := fromModes_bound _ _ _ _

def hilbertSymbol (n : ℤ) : ℂ := if 0 < n then Complex.I else if n < 0 then -Complex.I else 0

lemma hilbertSymbol_bound (n : ℤ) : ‖hilbertSymbol n‖ ≤ 1 := by
  unfold hilbertSymbol
  split_ifs <;> simp

lemma hilbertSymbol_neg (n : ℤ) : hilbertSymbol (-n) = conj (hilbertSymbol n) := by
  unfold hilbertSymbol
  split_ifs <;> simp_all
  all_goals omega

def hilbert : Space →L[ℂ] Space := multiplier hilbertSymbol 1 hilbertSymbol_bound

lemma hilbert_norm (f : Space) : ‖hilbert f‖ ≤ ‖f‖ := by
  simpa only [hilbert,one_mul] using multiplier_bound hilbertSymbol 1 hilbertSymbol_bound f

lemma hilbert_conjugate (f : Space) : hilbert (conjugate f) = conjugate (hilbert f) := by
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,conjugate_single,hilbert,multiplier_single]
    apply Finset.sum_congr rfl
    intro _ _
    rw [hilbertSymbol_neg,map_mul]

def realSubspace : Submodule ℝ Space := LinearMap.ker (conjugate.toLinearMap-LinearMap.id)

lemma mem_realSubspace {f : Space} : f ∈ realSubspace ↔ conjugate f = f := by
  simp [realSubspace,sub_eq_zero]

lemma realSubspace_closed : IsClosed (realSubspace : Set Space) := by
  change IsClosed {f : Space | conjugate f - f = 0}
  exact isClosed_eq (by fun_prop) continuous_const

instance : CompleteSpace realSubspace := realSubspace_closed.completeSpace_coe

lemma real_boundary {f : Space} (hf : f ∈ realSubspace) (θ : Circle) : (boundary f θ).im = 0 := by
  have h := boundary_conjugate f θ
  rw [mem_realSubspace.mp hf] at h
  exact (Complex.conj_eq_iff_im).mp h.symm

lemma hilbert_real {f : Space} (hf : f ∈ realSubspace) : hilbert f ∈ realSubspace := by
  rw [mem_realSubspace,← hilbert_conjugate,mem_realSubspace.mp hf]

abbrev ClosedDisc := Metric.closedBall (0 : ℂ) 1

def schwarzMode (n : ℤ) (z : ℂ) : ℂ :=
  if 0 < n then Complex.I * (2*z^n.toNat-1) else Complex.I

lemma schwarzMode_continuous (n : ℤ) : Continuous (schwarzMode n) := by
  unfold schwarzMode
  split_ifs <;> fun_prop

lemma schwarzMode_differentiable (n : ℤ) : Differentiable ℂ (schwarzMode n) := by
  unfold schwarzMode
  split_ifs <;> fun_prop

lemma schwarzMode_bound (n : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖schwarzMode n z‖ ≤ 3 := by
  unfold schwarzMode
  split_ifs
  · rw [norm_mul,Complex.norm_I,one_mul]
    calc ‖2*z^n.toNat-1‖ ≤ ‖2*z^n.toNat‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2*‖z‖^n.toNat+1 := by simp
      _ ≤ 3 := by have := (pow_le_one₀ (n := n.toNat) (norm_nonneg z) hz); linarith
  · simp

def schwarzModeC (n : ℤ) : C(ClosedDisc,ℂ) :=
  ⟨fun z => schwarzMode n z,(schwarzMode_continuous n).comp continuous_subtype_val⟩

def schwarz : Space →L[ℂ] C(ClosedDisc,ℂ) :=
  fromModes schwarzModeC 3 (by
    intro n
    apply ((schwarzModeC n).norm_le (mul_nonneg (by norm_num) (weight_pos n).le)).mpr
    intro z
    apply (schwarzMode_bound n (by simpa only [ClosedDisc,Metric.mem_closedBall,dist_zero_right] using z.property)).trans
    simpa using (mul_le_mul_of_nonneg_left (one_le_weight n) (by norm_num : (0:ℝ) ≤ 3)))

lemma schwarz_coe (p : Poly) :
    schwarz (p : Space) = p.coeff.sum (fun n z => z • schwarzModeC n) := fromModes_coe _ _ _ _

lemma schwarz_norm (f : Space) : ‖schwarz f‖ ≤ 3*‖f‖ := fromModes_bound _ _ _ _

lemma schwarz_single (n : ℤ) (c : ℂ) :
    schwarz ((AddMonoidAlgebra.single n c : Poly) : Space) = c • schwarzModeC n :=
  fromModes_single _ _ _ _ _

def discValue (f : Space) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ ClosedDisc then schwarz f ⟨z,hz⟩ else 0

lemma discValue_eq (f : Space) {z : ℂ} (hz : z ∈ ClosedDisc) :
    discValue f z = schwarz f ⟨z,hz⟩ := dite_eq_left hz

lemma discValue_continuousOn (f : Space) : ContinuousOn (discValue f) ClosedDisc := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert (schwarz f).continuous using 1
  ext z
  exact discValue_eq f z.property

lemma exists_poly_seq (f : Space) : ∃ p : ℕ → Poly, Tendsto (fun j => (p j : Space)) atTop (𝓝 f) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (UniformSpace.Completion.denseRange_coe f)
  choose p hp using hs
  exact ⟨p,by simpa only [hp] using ht⟩

def polyDisc (p : Poly) (z : ℂ) : ℂ := p.coeff.sum (fun n c => c*schwarzMode n z)

lemma polyDisc_eq (p : Poly) {z : ℂ} (hz : z ∈ ClosedDisc) :
    polyDisc p z = discValue (p : Space) z := by
  rw [discValue_eq _ hz,schwarz_coe]
  simp only [polyDisc,Finsupp.sum,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
  rfl

lemma polyDisc_differentiable (p : Poly) : Differentiable ℂ (polyDisc p) := by
  unfold polyDisc Finsupp.sum
  apply Differentiable.fun_sum
  intro n _
  exact (differentiable_const _).mul (schwarzMode_differentiable n)

lemma polyDisc_tendsto_uniformly {p : ℕ → Poly} {f : Space}
    (h : Tendsto (fun j => (p j : Space)) atTop (𝓝 f)) :
    TendstoUniformlyOn (fun j => polyDisc (p j)) (discValue f) atTop ClosedDisc := by
  have ht := ContinuousMap.tendsto_iff_tendstoUniformly.mp (schwarz.continuous.tendsto f |>.comp h)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp ht ε hε] with j hj
  intro z hz
  rw [polyDisc_eq _ hz,discValue_eq _ hz,discValue_eq _ hz]
  exact hj ⟨z,hz⟩

lemma discValue_analytic (f : Space) : AnalyticOnNhd ℂ (discValue f) (Metric.ball 0 1) := by
  obtain ⟨p,hp⟩ := exists_poly_seq f
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  exact ((polyDisc_tendsto_uniformly hp).mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun j => (polyDisc_differentiable (p j)).differentiableOn) Metric.isOpen_ball

lemma fourier_nat (j : ℕ) (θ : Circle) : fourier (j : ℤ) θ = (fourier 1 θ)^j := by
  induction j with
  | zero => simp only [Nat.cast_zero,fourier_zero,pow_zero]
  | succ j hj => rw [Nat.cast_add,Nat.cast_one,fourier_add,hj,pow_succ]

lemma schwarzMode_boundary (n : ℤ) (θ : Circle) :
    schwarzMode n (fourier 1 θ) =
      hilbertSymbol n * fourier n θ - hilbertSymbol n + Complex.I * fourier n θ := by
  by_cases hn : 0 < n
  · rw [schwarzMode,ite_eq_left hn,← fourier_nat,Int.toNat_of_nonneg hn.le,
      hilbertSymbol,ite_eq_left hn]
    ring
  · by_cases hn' : n < 0
    · rw [schwarzMode,ite_eq_right hn,hilbertSymbol,ite_eq_right hn,ite_eq_left hn']
      ring
    · have : n = 0 := by omega
      subst n
      simp [schwarzMode,hilbertSymbol]

lemma schwarz_boundary (f : Space) (θ : Circle) :
    discValue f (fourier 1 θ) = boundary (hilbert f) θ - boundary (hilbert f) 0 +
      Complex.I * boundary f θ := by
  have hz : fourier 1 θ ∈ ClosedDisc := by simpa only [ClosedDisc,Metric.mem_closedBall,dist_zero_right] using (show ‖fourier 1 θ‖ ≤ 1 by simpa only [fourier_one] using (_root_.Circle.norm_coe (AddCircle.toCircle θ)).le)
  rw [discValue_eq _ hz]
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    rw [poly_expansion p]
    simp only [map_sum,schwarz_single,hilbert,multiplier_single,boundary_single,
      ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
      Finset.mul_sum]
    rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    change _ * schwarzMode n (fourier 1 θ) = _
    rw [schwarzMode_boundary,fourier_eval_zero]
    ring

lemma discValue_at_one (f : Space) : discValue f 1 = Complex.I * boundary f 0 := by
  have h := schwarz_boundary f 0
  simpa only [fourier_eval_zero,sub_self,zero_add] using h

lemma schwarz_has_real_part (f : realSubspace) (θ : Circle) :
    (discValue f (fourier 1 θ)).re = (boundary (hilbert f) θ).re - (boundary (hilbert f) 0).re := by
  rw [schwarz_boundary]
  simp [Complex.mul_re,real_boundary f.property θ]

lemma schwarz_has_imag_part (f : realSubspace) (θ : Circle) :
    (discValue f (fourier 1 θ)).im = (boundary f θ).re := by
  rw [schwarz_boundary]
  simp [Complex.mul_im,real_boundary (hilbert_real f.property) θ,
    real_boundary (hilbert_real f.property) 0]

lemma single_mul (n m : ℤ) (z w : ℂ) :
    ((AddMonoidAlgebra.single n z : Poly) : Space) *
      ((AddMonoidAlgebra.single m w : Poly) : Space) =
        ((AddMonoidAlgebra.single (n+m) (z*w) : Poly) : Space) := by
  rw [← UniformSpace.Completion.coe_mul,AddMonoidAlgebra.single_mul_single]

lemma conjugate_mul (f g : Space) : conjugate (f*g) = conjugate f*conjugate g := by
  induction f,g using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p q =>
    rw [poly_expansion p,poly_expansion q]
    simp only [Finset.sum_mul_sum,map_sum,conjugate_single,single_mul]
    apply Finset.sum_congr rfl
    intro _ _
    apply Finset.sum_congr rfl
    intro _ _
    rw [neg_add,map_mul]

lemma conjugate_one : conjugate (1 : Space) = 1 := by
  rw [← UniformSpace.Completion.coe_one]
  change conjugate ((AddMonoidAlgebra.single 0 1 : Poly) : Space) =
    ((AddMonoidAlgebra.single 0 1 : Poly) : Space)
  rw [conjugate_single,neg_zero,map_one]

lemma conjugate_real (r : ℝ) : conjugate (algebraMap ℝ Space r) = algebraMap ℝ Space r := by
  rw [Algebra.algebraMap_eq_smul_one,map_smul,conjugate_one]

def realAlgebra : Subalgebra ℝ Space where
  carrier := {f | conjugate f = f}
  mul_mem' hf hg := by rw [Set.mem_ofPred_eq,conjugate_mul,hf,hg]
  add_mem' hf hg := by rw [Set.mem_ofPred_eq,map_add,hf,hg]
  algebraMap_mem' := conjugate_real
  zero_mem' := map_zero _
  one_mem' := conjugate_one

lemma realAlgebra_closed : IsClosed (realAlgebra : Set Space) := by
  change IsClosed {f | conjugate f = f}
  exact isClosed_eq conjugate.continuous continuous_id

instance : CompleteSpace realAlgebra := realAlgebra_closed.completeSpace_coe

noncomputable instance : NormOneClass Space where
  norm_one := by
    rw [← UniformSpace.Completion.coe_one Poly,UniformSpace.Completion.norm_coe]
    exact norm_one

noncomputable instance : NormOneClass realAlgebra where
  norm_one := by change ‖(1 : Space)‖ = 1; exact norm_one

lemma realAlgebra_mem_subspace (f : realAlgebra) : (f : Space) ∈ realSubspace :=
  mem_realSubspace.mpr f.property

lemma realAlgebra_boundary_im (f : realAlgebra) (θ : Circle) : (boundary f θ).im = 0 :=
  real_boundary (realAlgebra_mem_subspace f) θ

def realEvaluation (θ : Circle) : realAlgebra →ₐ[ℝ] ℝ where
  toFun f := (boundary f θ).re
  map_zero' := by simp
  map_one' := by simp [boundary_one]
  map_add' f g := by simp
  map_mul' f g := by simp [boundary_mul,Complex.mul_re,realAlgebra_boundary_im]
  commutes' r := by
    change (boundary (algebraMap ℝ Space r) θ).re = r
    rw [Algebra.algebraMap_eq_smul_one]
    have hb : boundary (r • (1 : Space)) = r • (1 : C(Circle,ℂ)) := by
      have h := (boundary.restrictScalars ℝ).map_smul r 1
      change boundary (r • (1 : Space)) = r • boundary 1 at h
      simpa only [boundary_one] using h
    rw [hb]
    simp

lemma realEvaluation_bound (θ : Circle) (f : realAlgebra) : |realEvaluation θ f| ≤ ‖f‖ := by
  exact (Complex.abs_re_le_norm _).trans
    (((boundary (f : Space)).norm_coe_le_norm θ).trans (boundary_norm_le f))

def realEvaluationCLM (θ : Circle) : realAlgebra →L[ℝ] ℝ :=
  (realEvaluation θ).toLinearMap.mkContinuous 1 (by
    intro f
    change |realEvaluation θ f| ≤ 1*‖f‖
    simpa only [one_mul] using realEvaluation_bound θ f)

def realHilbert : realAlgebra →L[ℝ] realAlgebra :=
  ({ toFun f := ⟨hilbert f,by
        change conjugate (hilbert f) = hilbert f
        rw [← hilbert_conjugate,f.property]⟩
     map_add' f g := by ext; exact map_add hilbert _ _
     map_smul' c f := by ext; exact (hilbert.restrictScalars ℝ).map_smul c f } :
    realAlgebra →ₗ[ℝ] realAlgebra).mkContinuous 1 (by
      intro f
      change ‖hilbert (f : Space)‖ ≤ 1*‖(f : Space)‖
      simpa only [one_mul] using hilbert_norm (f : Space))

def constantReal : ℝ →L[ℝ] realAlgebra :=
  (Algebra.linearMap ℝ realAlgebra).mkContinuous 1 (by
    intro r
    simp [Algebra.linearMap_apply,Algebra.algebraMap_eq_smul_one])

def normalizedHilbert : realAlgebra →L[ℝ] realAlgebra :=
  realHilbert-constantReal.comp ((realEvaluationCLM 0).comp realHilbert)

lemma normalizedHilbert_bound (f : realAlgebra) : ‖normalizedHilbert f‖ ≤ 2*‖f‖ := by
  change ‖realHilbert f-constantReal (realEvaluationCLM 0 (realHilbert f))‖ ≤ _
  apply (norm_sub_le _ _).trans
  have hh : ‖realHilbert f‖ ≤ ‖f‖ := hilbert_norm f
  have hc : ‖constantReal (realEvaluationCLM 0 (realHilbert f))‖ ≤ ‖realHilbert f‖ := by
    change ‖algebraMap ℝ realAlgebra (realEvaluation 0 (realHilbert f))‖ ≤ _
    rw [Algebra.algebraMap_eq_smul_one,norm_smul,norm_one,mul_one,Real.norm_eq_abs]
    exact realEvaluation_bound _ _
  linarith

lemma normalizedHilbert_eval_zero (f : realAlgebra) :
    realEvaluation 0 (normalizedHilbert f) = 0 := by
  change realEvaluation 0 (realHilbert f-algebraMap ℝ realAlgebra (realEvaluation 0 (realHilbert f))) = 0
  rw [map_sub,AlgHom.commutes]
  simp

open MeasureTheory

def fourierCLM (n : ℤ) : C(Circle,ℂ) →L[ℂ] ℂ :=
  ({ toFun f := fourierCoeff f n
     map_add' f g := by
       exact congrFun (fourierCoeff.add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
         (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) n
     map_smul' c f := fourierCoeff.const_smul f c n } : C(Circle,ℂ) →ₗ[ℂ] ℂ).mkContinuous 1 (by
      intro f
      have h : ∀ᵐ t ∂AddCircle.haarAddCircle, ‖fourier (-n) t • f t‖ ≤ ‖f‖ := by
        filter_upwards [] with t
        rw [norm_smul,fourier_apply,Circle.norm_coe,one_mul]
        exact f.norm_coe_le_norm t
      change ‖fourierCoeff f n‖ ≤ 1*‖f‖
      simpa [fourierCoeff] using norm_integral_le_of_norm_le_const h)

def coeff (n : ℤ) : Space →L[ℂ] ℂ := (fourierCLM n).comp boundary

lemma coeff_single (n m : ℤ) (z : ℂ) :
    coeff n ((AddMonoidAlgebra.single m z : Poly) : Space) = if m = n then z else 0 := by
  classical
  change fourierCLM n (boundary _) = _
  rw [boundary_single,map_smul]
  change z • fourierCoeff (fourier m) n = _
  rw [fourierCoeff_fourier]
  by_cases h : m = n <;> simp [h]

lemma coeff_coe (n : ℤ) (p : Poly) : coeff n (p : Space) = p.coeff n := by
  classical
  rw [poly_expansion p,map_sum]
  simp only [coeff_single]
  by_cases hn : p.coeff n = 0 <;> simp [hn]

def cutoff (s : Finset ℤ) : Space →L[ℂ] Space :=
  fromModes (fun n => if n ∈ s then ((AddMonoidAlgebra.single n 1 : Poly) : Space) else 0) 1 (by
    intro n
    split_ifs
    · rw [UniformSpace.Completion.norm_coe,norm_def,wnorm_single]
      simp
    · simpa only [norm_zero,one_mul] using (weight_pos n).le)

lemma cutoff_bound (s : Finset ℤ) (f : Space) : ‖cutoff s f‖ ≤ ‖f‖ := by
  simpa only [cutoff,one_mul] using fromModes_bound _ 1 _ f

lemma cutoff_eq (s : Finset ℤ) (f : Space) :
    cutoff s f = ∑ n ∈ s, coeff n f • ((AddMonoidAlgebra.single n 1 : Poly) : Space) := by
  classical
  induction f using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih p =>
    change fromModes _ _ _ (p : Space) = _
    rw [fromModes_coe]
    simp only [coeff_coe,Finsupp.sum,smul_ite,smul_zero]
    exact Finset.sum_bij_ne_zero (fun n _ _ => n)
      (by intro _ _ hz; by_contra hs; simp [hs] at hz)
      (by intro a _ _ b _ _ h; exact h)
      (by
        intro n hn hz
        have hc : p.coeff n ≠ 0 := fun h => hz (by rw [h,zero_smul])
        exact ⟨n,Finsupp.mem_support_iff.mpr hc,by simpa only [ite_eq_left hn] using hz,rfl⟩)
      (by
        intro n _ hz
        have hs : n ∈ s := by by_contra h; simp [h] at hz
        rw [ite_eq_left hs])

lemma cutoff_coe_self (p : Poly) : cutoff p.coeff.support (p : Space) = p := by
  rw [cutoff_eq]
  simp only [coeff_coe]
  conv_rhs => rw [poly_expansion p]
  apply Finset.sum_congr rfl
  intro _ _
  rw [← UniformSpace.Completion.coe_smul]
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one]

lemma boundary_injective : Function.Injective boundary := by
  suffices ∀ f : Space, boundary f = 0 → f = 0 by
    intro f g h
    exact sub_eq_zero.mp (this (f-g) (by rw [map_sub,h,sub_self]))
  intro f hf
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨p,hp⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt f (half_pos hε)
  have hz : cutoff p.coeff.support f = 0 := by
    rw [cutoff_eq]
    apply Finset.sum_eq_zero
    intro n _
    have hc : coeff n f = 0 := by change fourierCLM n (boundary f) = 0; rw [hf,map_zero]
    rw [hc,zero_smul]
  have hpc : ‖(p : Space)‖ ≤ ‖(p : Space)-f‖ := by
    have h := cutoff_bound p.coeff.support ((p : Space)-f)
    rw [map_sub,cutoff_coe_self,hz,sub_zero] at h
    exact h
  have hd : ‖f-(p : Space)‖ < ε/2 := by simpa only [dist_eq_norm] using hp
  have hn := norm_add_le (f-(p : Space)) (p : Space)
  rw [sub_add_cancel,norm_sub_rev] at hn
  rw [norm_sub_rev] at hd
  linarith

end Release061.Wiener

end

end OAI
