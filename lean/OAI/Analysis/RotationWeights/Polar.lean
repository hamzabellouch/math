import OAI.Analysis.RotationWeights.ProjectionFields

namespace OAI

noncomputable section

namespace CirclePolar

universe uH

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set

open Set
open scoped ComplexInnerProductSpace
section
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Op := H →L[ℂ] H

def absOp (A : Op (H := H)) : Op (H := H) := CFC.sqrt (star A * A)

lemma absOp_selfAdjoint (A : Op (H := H)) : IsSelfAdjoint (absOp A) :=
  IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

lemma absOp_square (A : Op (H := H)) : absOp A * absOp A = star A * A :=
  CFC.sqrt_mul_sqrt_self _

lemma norm_absOp (A : Op (H := H)) (x : H) : ‖absOp A x‖ = ‖A x‖ := by
  have he : inner ℂ (absOp A x) (absOp A x) = inner ℂ (A x) (A x) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ x ((star (absOp A) * absOp A) x) = inner ℂ x ((star A * A) x)
    rw [(absOp_selfAdjoint A).star_eq,absOp_square]
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at he
  have h : ‖absOp A x‖^2 = ‖A x‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (absOp A x),norm_nonneg (A x)]

def closedRange (A : Op (H := H)) : Submodule ℂ H := A.toLinearMap.range.topologicalClosure

instance (A : Op (H := H)) : CompleteSpace (closedRange A) :=
  inferInstanceAs (CompleteSpace A.toLinearMap.range.topologicalClosure)

def intoRange (A : Op (H := H)) : H →ₗ[ℂ] closedRange A :=
  A.toLinearMap.codRestrict _ (fun x ↦ A.toLinearMap.range.le_topologicalClosure ⟨x,rfl⟩)

omit [CompleteSpace H] in
lemma intoRange_dense (A : Op (H := H)) : DenseRange (intoRange A) := by
  intro x
  rw [closure_subtype]
  change x.val ∈ closure (Subtype.val '' Set.range (intoRange A))
  rw [← Set.range_comp]
  exact x.property

def polarCore (A : Op (H := H)) : closedRange (absOp A) →L[ℂ] H :=
  A.toLinearMap.extendOfNorm (intoRange (absOp A))

lemma polarCore_abs (A : Op (H := H)) (x : H) :
    polarCore A (intoRange (absOp A) x) = A x := by
  apply LinearMap.extendOfNorm_eq (intoRange_dense _)
  refine ⟨1,fun x ↦ ?_⟩
  change ‖A x‖ ≤ 1*‖absOp A x‖
  rw [one_mul,norm_absOp]

lemma polarCore_norm (A : Op (H := H)) (x : closedRange (absOp A)) :
    ‖polarCore A x‖ = ‖x‖ := by
  refine (intoRange_dense (absOp A)).induction_on (p := fun x ↦ ‖polarCore A x‖ = ‖x‖) x
    (isClosed_eq ((polarCore A).continuous.norm) continuous_norm) ?_
  intro y
  rw [polarCore_abs]
  exact (norm_absOp A y).symm

def polar (A : Op (H := H)) : Op (H := H) :=
  (polarCore A).comp (closedRange (absOp A)).orthogonalProjectionOnto

lemma polar_abs (A : Op (H := H)) : polar A * absOp A = A := by
  ext x
  change polarCore A ((closedRange (absOp A)).orthogonalProjectionOnto (absOp A x)) = A x
  have h := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (intoRange (absOp A) x)
  rw [show (closedRange (absOp A)).orthogonalProjectionOnto (absOp A x) = intoRange (absOp A) x from h]
  exact polarCore_abs A x

lemma polar_norm (A : Op (H := H)) (x : H) :
    ‖polar A x‖ = ‖(closedRange (absOp A)).starProjection x‖ := by
  change ‖polarCore A ((closedRange (absOp A)).orthogonalProjectionOnto x)‖ = _
  rw [polarCore_norm]
  rfl

def polarCoreIsometry (A : Op (H := H)) : closedRange (absOp A) →ₗᵢ[ℂ] H where
  toLinearMap := (polarCore A).toLinearMap
  norm_map' := polarCore_norm A

lemma polar_star_mul (A : Op (H := H)) :
    star (polar A) * polar A = (closedRange (absOp A)).starProjection := by
  ext x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((ContinuousLinearMap.adjoint (polar A)) (polar A x)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (polarCoreIsometry A ((closedRange (absOp A)).orthogonalProjectionOnto y))
    (polarCoreIsometry A ((closedRange (absOp A)).orthogonalProjectionOnto x)) = _
  rw [(polarCoreIsometry A).inner_map_map]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := closedRange (absOp A))
    ((closedRange (absOp A)).orthogonalProjectionOnto x) y

lemma ker_absOp (A : Op (H := H)) : (absOp A).ker = A.ker := by
  ext x
  change absOp A x=0 ↔ A x=0
  simpa only [norm_eq_zero] using (show ‖absOp A x‖=0 ↔ ‖A x‖=0 by rw [norm_absOp])

lemma closedRange_absOp (A : Op (H := H)) : closedRange (absOp A) = A.kerᗮ := by
  rw [← ker_absOp A,ContinuousLinearMap.orthogonal_ker]
  have hs : ContinuousLinearMap.adjoint (absOp A) = absOp A := (absOp_selfAdjoint A).star_eq
  rw [hs]
  rfl

lemma polar_eq_zero_iff (A : Op (H := H)) (x : H) : polar A x=0 ↔ A x=0 := by
  rw [← norm_eq_zero,polar_norm,norm_eq_zero,Submodule.starProjection_apply_eq_zero_iff,
    closedRange_absOp,Submodule.orthogonal_orthogonal]
  rfl

lemma commute_absOp {A B : Op (H := H)} (h : Commute A B) (hs : Commute (star A) B) :
    Commute (absOp A) B := by
  exact (hs.mul_left h).cfcₙ_nnreal NNReal.sqrt

lemma commute_polar {A B : Op (H := H)} (h : Commute A B) (hs : Commute (star A) B) :
    Commute (polar A) B := by
  have hS := commute_absOp h hs
  have hg (x : H) (hx : x ∈ closedRange (absOp A)) : polar A (B x) = B (polar A x) := by
    apply closure_minimal (s := Set.range (absOp A)) _
      (isClosed_eq ((polar A).continuous.comp B.continuous) (B.continuous.comp (polar A).continuous)) hx
    rintro _ ⟨y,rfl⟩
    have h1 := DFunLike.congr_fun hS.eq y
    have h2 := DFunLike.congr_fun h.eq y
    have h3 z := DFunLike.congr_fun (polar_abs A) z
    change polar A (B (absOp A y)) = B (polar A (absOp A y))
    change absOp A (B y)=B (absOp A y) at h1
    change A (B y)=B (A y) at h2
    change ∀ z, polar A (absOp A z)=A z at h3
    rw [← h1,h3,h3,h2]
  have hk (x : H) (hx : x ∈ (closedRange (absOp A))ᗮ) : polar A (B x)=B (polar A x) := by
    rw [closedRange_absOp,Submodule.orthogonal_orthogonal] at hx
    change A x=0 at hx
    have hb : A (B x)=0 := by
      have he := DFunLike.congr_fun h.eq x
      change A (B x)=B (A x) at he
      rw [he,hx,map_zero]
    rw [(polar_eq_zero_iff A _).mpr hb,(polar_eq_zero_iff A _).mpr hx,map_zero]
  change polar A*B=B*polar A
  ext x
  let P := (closedRange (absOp A)).starProjection
  have hd : x=P x+(x-P x) := by abel
  change polar A (B x)=B (polar A x)
  conv_lhs => rw [hd]
  conv_rhs => rw [hd]
  simp only [map_add]
  rw [hg _ (Submodule.starProjection_apply_mem _ _),
    hk _ (Submodule.sub_starProjection_mem_orthogonal (K := closedRange (absOp A)) _)]


lemma polar_norm_le (A : Op (H := H)) (x : H) : ‖polar A x‖ ≤ ‖x‖ := by
  rw [polar_norm]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

lemma polar_opNorm_le (A : Op (H := H)) : ‖polar A‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa using polar_norm_le A

lemma polar_range (A : Op (H := H)) (x : H) : polar A x ∈ closedRange A := by
  have hwithin (y : H) (hy : y ∈ closedRange (absOp A)) : polar A y ∈ closedRange A := by
    apply closure_minimal (s := Set.range (absOp A)) _
      ((Submodule.isClosed_topologicalClosure _).preimage (polar A).continuous) hy
    rintro _ ⟨z,rfl⟩
    change (polar A * absOp A) z ∈ closedRange A
    rw [polar_abs]
    exact A.toLinearMap.range.le_topologicalClosure ⟨z,rfl⟩
  let P := (closedRange (absOp A)).starProjection
  have hk : A (x-P x)=0 := by
    have hh := Submodule.sub_starProjection_mem_orthogonal (K := closedRange (absOp A)) x
    change x-P x ∈ (closedRange (absOp A))ᗮ at hh
    rw [closedRange_absOp,Submodule.orthogonal_orthogonal] at hh
    exact hh
  have he := (polar_eq_zero_iff A (x-P x)).mpr hk
  rw [map_sub,sub_eq_zero] at he
  rw [he]
  exact hwithin _ (Submodule.starProjection_apply_mem _ _)

lemma polar_range_le {A : Op (H := H)} {K : Submodule ℂ H} (hK : IsClosed (K : Set H))
    (hA : ∀ x, A x ∈ K) (x : H) : polar A x ∈ K := by
  have hle : closedRange A ≤ K := by
    apply Submodule.topologicalClosure_minimal _ _ hK
    rintro _ ⟨z,rfl⟩
    exact hA z
  exact hle (polar_range A x)

lemma polar_adjoint_annihilates {A : Op (H := H)} {K : Submodule ℂ H}
    (hK : IsClosed (K : Set H)) (hA : ∀ x, A x ∈ K) {z : H} (hz : z ∈ Kᗮ) :
    (star (polar A)) z = 0 := by
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y ((ContinuousLinearMap.adjoint (polar A)) z) = inner ℂ y 0
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right]
  exact (Submodule.mem_orthogonal _ _).mp hz _ (polar_range_le hK hA y)

end
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma disjoint_norm_bound (P E : Submodule ℂ H) [CompleteSpace P] [CompleteSpace E]
    (v : H) (hd : Disjoint P E)
    (htrace : ‖(star (polar (Eᗮ.starProjection * P.starProjection))) v‖ =
      ‖polar (Eᗮ.starProjection * P.starProjection) v‖) :
    ‖P.starProjection v‖ ≤ ‖Eᗮ.starProjection v‖ := by
  let A := Eᗮ.starProjection * P.starProjection
  have hker : A.ker = Pᗮ := by
    ext x
    change Eᗮ.starProjection (P.starProjection x)=0 ↔ x∈Pᗮ
    rw [Submodule.starProjection_apply_eq_zero_iff,Submodule.orthogonal_orthogonal]
    constructor
    · intro hx
      have hp := (Submodule.disjoint_def.mp hd) _ (P.starProjection_apply_mem x) hx
      exact (P.starProjection_apply_eq_zero_iff).mp hp
    · intro hx
      rw [(P.starProjection_apply_eq_zero_iff).mpr hx]
      exact E.zero_mem
  have hr : closedRange (absOp A) = P := by
    rw [closedRange_absOp,hker,Submodule.orthogonal_orthogonal]
  have hA (x : H) : A x ∈ Eᗮ := Eᗮ.starProjection_apply_mem _
  have hzero : (star (polar A)) (E.starProjection v)=0 :=
    polar_adjoint_annihilates E.isClosed_orthogonal hA (by
      rw [Submodule.orthogonal_orthogonal]
      exact E.starProjection_apply_mem v)
  have hid : (star (polar A)) v = (star (polar A)) (Eᗮ.starProjection v) := by
    rw [E.starProjection_orthogonal]
    simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,hzero,sub_zero]
  have hnorm : ‖polar A v‖ = ‖P.starProjection v‖ := by
    rw [polar_norm]
    congr 1
    simp only [hr]
  calc
    _ = ‖polar A v‖ := hnorm.symm
    _ = ‖(star (polar A)) v‖ := htrace.symm
    _ = ‖(star (polar A)) (Eᗮ.starProjection v)‖ := congrArg norm hid
    _ ≤ ‖star (polar A)‖ * ‖Eᗮ.starProjection v‖ := (star (polar A)).le_opNorm _
    _ ≤ 1 * ‖Eᗮ.starProjection v‖ := by rw [norm_star]; gcongr; exact polar_opNorm_le A
    _ = _ := one_mul _

lemma exists_intersection_of_norm_lt (P E : Submodule ℂ H) [CompleteSpace P] [CompleteSpace E]
    (v : H) (htrace : ‖(star (polar (Eᗮ.starProjection * P.starProjection))) v‖ =
      ‖polar (Eᗮ.starProjection * P.starProjection) v‖)
    (hlt : ‖Eᗮ.starProjection v‖ < ‖P.starProjection v‖) :
    ∃ x : H, x∈P ∧ x∈E ∧ x≠0 := by
  by_contra! h
  have hd : Disjoint P E := Submodule.disjoint_def.mpr h
  exact (not_lt_of_ge (disjoint_norm_bound P E v hd htrace)) hlt



end CirclePolar

end

end OAI
