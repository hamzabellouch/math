import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredProfilePaths

namespace OAI

/-! # Centered image paths for the two probe sheets -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

section Topological

variable {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Center the image path at its actual initial image. -/
def centeredImagePath (f : X → G) (hf : Continuous f) {a b : X} (γ : Path a b) :
    Path (1 : G) ((f a)⁻¹ * f b) where
  toFun t := (f a)⁻¹ * f (γ t)
  continuous_toFun := continuous_const.mul (hf.comp γ.continuous)
  source' := by simp
  target' := by simp

end Topological

section Metric

variable {X G : Type*} [PseudoMetricSpace X] [Group G] [PseudoMetricSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]

/-- Quasi-isometry Lipschitz control transfers to the centered path with
the same scaling of both the speed and the additive error. -/
theorem centeredImagePath_metric_bound (f : X → G) {K : ℝ≥0} (hf : LipschitzWith K f)
    {a b : X} (γ : Path a b) {L κ : ℝ} (hγ : PathMetricBound γ L κ) :
    PathMetricBound (centeredImagePath f hf.continuous γ) (K * L) (K * κ) := by
  intro s t
  change dist ((f a)⁻¹ * f (γ s)) ((f a)⁻¹ * f (γ t)) ≤ _
  rw [dist_mul_left]
  calc
    _ ≤ K * dist (γ s) (γ t) := hf.dist_le_mul _ _
    _ ≤ K * (L * |(s : ℝ) - t| + κ) :=
      mul_le_mul_of_nonneg_left (hγ s t) K.coe_nonneg
    _ = _ := by ring

end Metric

variable {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The centered path has exactly the relative height required by the
factor-lifting theorem. The profile error at its start is retained. -/
theorem centeredImagePath_height_bound
    (f : X → G) (hf : Continuous f) (π : G →* Multiplicative W)
    {a b : X} (γ : Path a b) (center w₀ : W) (E : Set W) (r B B₀ : ℝ)
    (hstart : ‖(π (f a)).toAdd - center - r • w₀‖ ≤ B₀)
    (hpath : ∀ t, ∃ w ∈ E, ‖(π (f (γ t))).toAdd - center - r • w‖ ≤ B) :
    ∀ t, ∃ w ∈ (fun z => z - w₀) '' E,
      ‖(π (centeredImagePath f hf γ t)).toAdd - r • w‖ ≤ B + B₀ := by
  have hh := centered_path_height_bound γ (fun x => (π (f x)).toAdd)
    center w₀ E r B B₀ hstart hpath
  intro t
  obtain ⟨w, hw, he⟩ := hh t
  refine ⟨w, hw, ?_⟩
  change ‖(π ((f a)⁻¹ * f (γ t))).toAdd - r • w‖ ≤ _
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he

end PolycyclicRecognition

end

end OAI
