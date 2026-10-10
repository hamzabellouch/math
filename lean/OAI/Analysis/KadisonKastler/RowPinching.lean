import OAI.Analysis.KadisonKastler.RowReplication

namespace OAI

/-! Projection rows give completely contractive idempotent averages. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def projectionRow (p : A) : Bool → A := fun b => if b then 1 - p else p

theorem projectionRow_normalized {p : A} (hp : IsStarProjection p) :
    ∑ b, projectionRow p b * star (projectionRow p b) = 1 := by
  simp [projectionRow, hp.isSelfAdjoint.star_eq, hp.one_sub.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.eq, hp.one_sub.isIdempotentElem.eq]

def projectionAverage (p : A) : (A →ₗ[ℂ] A) →ₗ[ℂ] (A →ₗ[ℂ] A) :=
  finiteRightAverage (projectionRow p)

theorem projectionAverage_apply {p : A} (hp : IsStarProjection p)
    (F : A →ₗ[ℂ] A) (x : A) :
    projectionAverage p F x = F (x * p) * p + F (x * (1 - p)) * (1 - p) := by
  simp [projectionAverage, projectionRow, finiteRightAverage_apply,
    hp.isSelfAdjoint.star_eq, hp.one_sub.isSelfAdjoint.star_eq, add_comm]

theorem projectionAverage_module {p : A} (hp : IsStarProjection p)
    (F : A →ₗ[ℂ] A) (x : A) :
    projectionAverage p F (x * p) = projectionAverage p F x * p := by
  rw [projectionAverage_apply hp, projectionAverage_apply hp]
  simp only [mul_assoc, hp.isIdempotentElem.eq, hp.mul_one_sub_self,
    hp.one_sub_mul_self, mul_zero, map_zero, zero_mul, add_zero, add_mul]

theorem projectionAverage_fixed_iff {p : A} (hp : IsStarProjection p)
    (F : A →ₗ[ℂ] A) :
    projectionAverage p F = F ↔ ∀ x, F (x * p) = F x * p := by
  constructor
  · intro h x
    simpa only [h] using projectionAverage_module hp F x
  · intro h
    apply LinearMap.ext
    intro x
    rw [projectionAverage_apply hp, h]
    have hc : F (x * (1 - p)) = F x * (1 - p) := by
      simp only [mul_sub, mul_one, map_sub, h]
    rw [hc]
    simp only [mul_assoc, hp.isIdempotentElem.eq, hp.one_sub.isIdempotentElem.eq]
    rw [← mul_add, add_sub_cancel]
    exact mul_one _

theorem projectionAverage_idempotent {p : A} (hp : IsStarProjection p)
    (F : A →ₗ[ℂ] A) : projectionAverage p (projectionAverage p F) = projectionAverage p F :=
  (projectionAverage_fixed_iff hp _).2 (projectionAverage_module hp F)

theorem projectionAverage_fixed_one_sub {p : A} (hp : IsStarProjection p)
    (F : A →ₗ[ℂ] A) : projectionAverage (1 - p) F = projectionAverage p F := by
  apply LinearMap.ext
  intro x
  rw [projectionAverage_apply hp.one_sub, projectionAverage_apply hp, sub_sub_cancel]
  exact add_comm _ _

theorem finiteRightAverage_commute {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → A) (s : κ → A) (hc : ∀ i j, r i * s j = s j * r i)
    (F : A →ₗ[ℂ] A) :
    finiteRightAverage r (finiteRightAverage s F) =
      finiteRightAverage s (finiteRightAverage r F) := by
  apply LinearMap.ext
  intro x
  simp only [finiteRightAverage_apply, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have hs : star (s j) * star (r i) = star (r i) * star (s j) := by
    simpa only [star_mul] using congrArg star (hc i j)
  rw [hc i j, hs]

variable [PartialOrder A] [StarOrderedRing A]

theorem CompletelyBoundedBy.projectionAverage {F : A →ₗ[ℂ] A} {c : ℝ}
    (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c) {p : A} (hp : IsStarProjection p) :
    CompletelyBoundedBy (projectionAverage p F) c :=
  hF.finiteRightAverage hc (projectionRow p) (projectionRow_normalized hp)

end

end KadisonKastler

end OAI
