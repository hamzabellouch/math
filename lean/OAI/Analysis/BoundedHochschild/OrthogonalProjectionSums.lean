import OAI.Analysis.BoundedHochschild.ProjectionSequenceLimits
import OAI.Analysis.BoundedHochschild.ProjectionJoinComparison

namespace OAI

/-! Arbitrary orthogonal projection sums and their weak-star convergence. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

universe u v

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {I : Type v}

omit [PartialOrder M] [StarOrderedRing M] in
lemma orthogonal_projection_finset_sum (p : I → M)
    (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) (s : Finset I) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      apply (hp i).add ih
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i j (fun hij => his (hij ▸ hj))

/-- The net of finite partial sums of any orthogonal family converges
weak-star to its projection supremum. -/
theorem exists_orthogonal_projection_sum (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i ≠ j → p i * p j = 0) :
    ∃ P : M, IsStarProjection P ∧ (∀ i, p i ≤ P) ∧
      (∀ r : M, IsStarProjection r → (∀ i, p i ≤ r) → P ≤ r) ∧
      PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P := by
  classical
  let f (s : Finset I) : M := ∑ i ∈ s, p i
  have hf (s : Finset I) : IsStarProjection (f s) := orthogonal_projection_finset_sum p hp horth s
  have hfm : Monotone f := by
    intro s t hst
    exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  obtain ⟨P, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e f hfm
    1 zero_le_one (fun s => (hf s).norm_le _)
  have hfixed (s : Finset I) : f s * P = f s := by
    have hm := HochschildSakai.predual_tendsto_mul_left e (f s) ht
    have heq : (fun t => f s * f t) =ᶠ[atTop] (fun _ => f s) := by
      filter_upwards [eventually_ge_atTop s] with t hst
      exact ((hf s).le_iff_mul_eq_left (hf t)).mp (hfm hst)
    apply predual_tendsto_unique e hm
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hP : IsStarProjection P := by
    constructor
    · have hm := HochschildSakai.predual_tendsto_mul_right e P ht
      have heq : (fun s => f s * P) = f := funext hfixed
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
    · have hm := HochschildSakai.predual_tendsto_star e ht
      have heq : (fun s => star (f s)) = f := funext fun s => (hf s).isSelfAdjoint.star_eq
      rw [heq] at hm
      exact predual_tendsto_unique e hm ht
  refine ⟨P, hP, ?_, ?_, ht⟩
  · intro i
    have h := hlub.1 (Set.mem_range_self ({i} : Finset I))
    simpa only [f, Finset.sum_singleton] using h
  · intro r hr hpr
    apply hlub.2
    rintro _ ⟨s, rfl⟩
    apply ((hf s).le_iff_mul_eq_right hr).mpr
    change r * (∑ i ∈ s, p i) = ∑ i ∈ s, p i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact ((hp i).le_iff_mul_eq_right hr).mp (hpr i)

/-- Common right annihilators are retained by the full orthogonal sum. -/
lemma orthogonal_projection_sum_annihilator (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : I → M) (a P : M)
    (ht : PredualTendsto e (fun s : Finset I => ∑ i ∈ s, p i) atTop P)
    (hpa : ∀ i, p i * a = 0) : P * a = 0 := by
  classical
  have hm := HochschildSakai.predual_tendsto_mul_right e a ht
  have heq : (fun s : Finset I => (∑ i ∈ s, p i) * a) = fun _ => (0 : M) := by
    funext s
    rw [Finset.sum_mul]
    simp only [hpa, Finset.sum_const_zero]
  rw [heq] at hm
  exact predual_tendsto_unique e hm (predual_tendsto_const e 0 atTop)

end KadisonRingrose
end BoundedHochschild

end

end OAI
