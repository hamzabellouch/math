import OAI.Analysis.BoundedHochschild.ProjectionChainSuprema

namespace OAI

/-! Sequential projection suprema and infima with their actual weak-star limits. -/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- An increasing sequence of projections converges weak-star to its supremum. -/
theorem exists_increasing_projection_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : ℕ → M) (hp : ∀ n, IsStarProjection (p n)) (hm : Monotone p) :
    ∃ s : M, IsStarProjection s ∧ IsLUB (Set.range p) s ∧
      PredualTendsto e p atTop s := by
  obtain ⟨s, _, hlub, ht⟩ := HochschildSakai.exists_monotone_predual_limit e p hm
    1 zero_le_one (fun n => (hp n).norm_le _)
  have hfixed (n : ℕ) : p n * s = p n := by
    have hm' := HochschildSakai.predual_tendsto_mul_left e (p n) ht
    have heq : (fun m => p n * p m) =ᶠ[atTop] (fun _ => p n) := by
      filter_upwards [eventually_ge_atTop n] with m hnm
      exact ((hp n).le_iff_mul_eq_left (hp m)).mp (hm hnm)
    apply predual_tendsto_unique e hm'
    intro x
    exact tendsto_const_nhds.congr' (heq.mono fun _ h =>
      congrArg (fun a : M => e.symm a x) h.symm)
  have hmul : s * s = s := by
    have hs := HochschildSakai.predual_tendsto_mul_right e s ht
    have heq : (fun n => p n * s) = p := funext hfixed
    rw [heq] at hs
    exact predual_tendsto_unique e hs ht
  have hstar : star s = s := by
    have hs := HochschildSakai.predual_tendsto_star e ht
    have heq : (fun n => star (p n)) = p := funext fun n => (hp n).isSelfAdjoint.star_eq
    rw [heq] at hs
    exact predual_tendsto_unique e hs ht
  exact ⟨s, ⟨hmul, hstar⟩, hlub, ht⟩

/-- A decreasing sequence of projections converges weak-star to its infimum. -/
theorem exists_decreasing_projection_limit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (p : ℕ → M) (hp : ∀ n, IsStarProjection (p n)) (hm : Antitone p) :
    ∃ s : M, IsStarProjection s ∧ IsGLB (Set.range p) s ∧
      PredualTendsto e p atTop s := by
  obtain ⟨s, hs, _, ht⟩ := exists_increasing_projection_limit e (fun n => 1 - p n)
    (fun n => (hp n).one_sub) (fun i j hij => sub_le_sub_left (hm hij) 1)
  have ht' : PredualTendsto e p atTop (1 - s) := by
    have hh := predual_tendsto_sub e (predual_tendsto_const e 1 atTop) ht
    simpa only [sub_sub_cancel] using hh
  exact ⟨1 - s, hs.one_sub,
    HochschildSakai.isGLB_of_antitone_predual_limit e p hm ht' 1 zero_le_one
      (fun n => (hp n).norm_le _), ht'⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
