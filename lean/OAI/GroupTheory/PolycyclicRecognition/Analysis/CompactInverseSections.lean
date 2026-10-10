import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParametricInverseSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSubmersionFamily

namespace OAI

/-! # Finite continuous inverse sections on a compact parameter family

The common image ball is retained together with continuous amplitude
choices, rather than just existential preimages. This is the form needed
to sample endpoints measurably in a stationary volume argument.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {P E F J : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Finitely many actual schemes admit bounded continuous inverse sections
on one common ball, uniformly over the compact parameter set. -/
theorem exists_finite_uniform_inverse_sections
    (f : J → P × E → F) {K : Set P} (hK : IsCompact K)
    (h : ∀ p ∈ K, ∃ j, ContDiffAt ℝ 1 (f j) (p, 0) ∧ f j (p, 0) = 0 ∧
      Function.Bijective (fun v : E => fderiv ℝ (f j) (p, 0) (0, v)))
    {R : ℝ} (hR : 0 < R) :
    ∃ (S : Finset J) (ε : ℝ), 0 < ε ∧ ∀ p ∈ K, ∃ j ∈ S,
      ∃ s : F → E, ContinuousOn s (ball 0 ε) ∧
        ∀ y ∈ ball (0 : F) ε, f j (p, s y) = y ∧ ‖s y‖ < R := by
  classical
  choose j hc hz hb using (fun p : K => h p.val p.property)
  choose U hU hp r hr s hs hsection using (fun p : K =>
    exists_parametric_inverse_section (f (j p)) p.val (hc p) (hz p) (hb p) hR)
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover U hU (by
    intro p hpK
    exact mem_iUnion.mpr ⟨⟨p, hpK⟩, hp ⟨p, hpK⟩⟩)
  obtain ⟨ε, hε, hεr⟩ := finite_positive_lower_bound S r (fun p _ => hr p)
  refine ⟨S.image j, ε, hε, ?_⟩
  intro p hpK
  obtain ⟨q, hq, hpU⟩ := mem_iUnion₂.mp (hS hpK)
  refine ⟨j q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, fun y => s q (p, y), ?_, ?_⟩
  · apply (hs q).comp (continuous_const.prodMk continuous_id).continuousOn
    intro y hy
    exact ⟨hpU, ball_subset_ball (hεr q hq) hy⟩
  · intro y hy
    exact hsection q p hpU y (ball_subset_ball (hεr q hq) hy)

end PolycyclicRecognition

end

end OAI
