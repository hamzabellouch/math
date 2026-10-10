import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Basic

namespace OAI

namespace Yau.Probability
open Set MeasureTheory
open scoped ENNReal
noncomputable section
variable {Ω X F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]

lemma finite_small_ball_union (μ : Measure Ω) (t : Finset X) (Z : Ω → X → F)
    (r : ℝ) (p : ℝ≥0∞) (hp : ∀ x ∈ t, μ {ω | ‖Z ω x‖ ≤ r} ≤ p) :
    μ {ω | ∃ x ∈ t, ‖Z ω x‖ ≤ r} ≤ t.card*p := by
  have he : {ω | ∃ x ∈ t, ‖Z ω x‖ ≤ r} = ⋃ x ∈ t, {ω | ‖Z ω x‖ ≤ r} := by
    ext ω
    simp
  rw [he]
  exact (measure_biUnion_finset_le t _).trans (by
    simpa using Finset.sum_le_sum hp)

lemma net_failure_le (μ : Measure Ω) (t : Finset X) (E : Set X)
    (Z : Ω → X → F) (good : Set Ω) (r : ℝ) (p : ℝ≥0∞)
    (hp : ∀ x ∈ t, μ {ω | ‖Z ω x‖ ≤ 2*r} ≤ p)
    (happrox : ∀ ω ∈ good, ∀ x ∈ E, ∃ y ∈ t, ‖Z ω y-Z ω x‖ ≤ r) :
    μ {ω | ∃ x ∈ E, ‖Z ω x‖ < r} ≤ μ goodᶜ+t.card*p := by
  have hsub : {ω | ∃ x ∈ E, ‖Z ω x‖ < r} ⊆
      goodᶜ ∪ {ω | ∃ y ∈ t, ‖Z ω y‖ ≤ 2*r} := by
    intro ω hω
    by_cases hg : ω ∈ good
    · obtain ⟨x,hx,hsmall⟩ := hω
      obtain ⟨y,hy,hd⟩ := happrox ω hg x hx
      right
      refine ⟨y,hy,?_⟩
      have htri : ‖Z ω y‖ ≤ ‖Z ω y-Z ω x‖+‖Z ω x‖ := norm_le_norm_sub_add _ _
      linarith
    · exact Or.inl hg
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (finite_small_ball_union μ t Z (2*r) p hp)))

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℝ F]

lemma neighborhood_net_approximation (t : Finset X) (E : Set X) (Z : X → F)
    {δ R L r : ℝ} (hδ : 0 ≤ δ) (hδR : δ ≤ R) (hL : 0 ≤ L) (hLδ : L*δ ≤ r)
    (hnet : ∀ x ∈ E, ∃ y ∈ t, ‖x-y‖ ≤ δ)
    (hdiff : ∀ x ∈ E, ∀ z ∈ Metric.closedBall x R, DifferentiableAt ℝ Z z)
    (hderiv : ∀ x ∈ E, ∀ z ∈ Metric.closedBall x R, ‖fderiv ℝ Z z‖ ≤ L) :
    ∀ x ∈ E, ∃ y ∈ t, ‖Z y-Z x‖ ≤ r := by
  intro x hx
  obtain ⟨y,hy,hd⟩ := hnet x hx
  have hxball : x ∈ Metric.closedBall x R := Metric.mem_closedBall_self (hδ.trans hδR)
  have hyball : y ∈ Metric.closedBall x R := by
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
    exact hd.trans hδR
  have h := (convex_closedBall x R).norm_image_sub_le_of_norm_fderiv_le
    (hdiff x hx) (hderiv x hx) hxball hyball
  rw [norm_sub_rev y x] at h
  exact ⟨y,hy,h.trans ((mul_le_mul_of_nonneg_left hd hL).trans hLδ)⟩

end
end Yau.Probability

end OAI
