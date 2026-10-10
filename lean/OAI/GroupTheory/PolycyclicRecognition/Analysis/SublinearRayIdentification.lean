import OAI.GroupTheory.PolycyclicRecognition.Geometry.GlobalHeight

namespace OAI

/-! # Identifying bounded trace errors along linearly growing height rays -/

noncomputable section
namespace PolycyclicRecognition

/-- A metric sublinear error restricts to a sublinear error on every ray of
at most linear metric growth. The additive constant may depend on the ray. -/
theorem sublinear_error_on_linear_ray
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W]
    (base : X) (error : X → W) (ray : ℝ → X)
    (herror : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ x,
      ‖error x‖ ≤ ε * dist base x + B)
    {L C : ℝ} (hL : 0 ≤ L)
    (hmetric : ∀ t : ℝ, 0 ≤ t → dist base (ray t) ≤ L * t + C) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ t : ℝ, R ≤ t → 0 ≤ t →
      ‖error (ray t)‖ ≤ ε * t := by
  intro ε hε
  let δ := ε / (2 * (L + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (2 * (L + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hδL : δ * L ≤ ε / 2 := by nlinarith
  obtain ⟨B, hB⟩ := herror δ hδ
  refine ⟨2 * (δ * C + B) / ε, ?_⟩
  intro t ht ht0
  have hconst : 2 * (δ * C + B) ≤ t * ε := (div_le_iff₀ hε).mp ht
  have hslope := mul_le_mul_of_nonneg_right hδL ht0
  calc
    ‖error (ray t)‖ ≤ δ * dist base (ray t) + B := hB _
    _ ≤ δ * (L * t + C) + B := add_le_add (mul_le_mul_of_nonneg_left (hmetric t ht0) hδ.le) le_rfl
    _ ≤ ε * t := by nlinarith

/-- Averaging gives bounded trace errors with the source character. A
sublinear comparison along height rays identifies each source character
with the corresponding target character composed with the affine label. -/
theorem uniform_transversal_affine_bound_of_ray_traces
    {P G D W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α β : I → Module.Dual ℝ W)
    (hsep : ∀ w, (∀ i, β i w = 0) → w = 0)
    (height : G → W) (η : P → G → W) (A : P → W →ₗ[ℝ] W)
    (d : D → G) (j₀ : D) (ray : W → ℝ → D)
    (hray : ∀ w t, height (d (ray w t)) = t • w)
    {B : ℝ} (hB : 0 ≤ B)
    (htrace : ∀ p j i,
      |β i (η p (d j) - η p (d j₀)) - α i (height (d j))| ≤ B)
    (hsub : ∀ p w ε, 0 < ε → ∃ R : ℝ, ∀ t, R ≤ t → 0 ≤ t →
      ‖(η p (d (ray w t)) - η p (d j₀)) - t • A p w‖ ≤ ε * t) :
    (∀ p i, α i = (β i).comp (A p)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p j,
        ‖η p (d j) - (η p (d j₀) + A p (height (d j)))‖ ≤ C := by
  have hcoeff (p : P) (i : I) : α i = (β i).comp (A p) := by
    apply trace_eq_of_bounded_and_sublinear (α i) (β i) (A p)
      (fun w t => η p (d (ray w t)) - η p (d j₀)) B
    · intro w t ht
      have h := htrace p (ray w t) i
      simpa only [hray, map_smul, smul_eq_mul] using h
    · exact hsub p
  refine ⟨hcoeff, ?_⟩
  obtain ⟨C, hC, hbound⟩ := exists_bound_of_separating_forms β hsep
  refine ⟨C * B, mul_nonneg hC.le hB, ?_⟩
  intro p j
  apply hbound _ B hB
  intro i
  have h := htrace p j i
  rw [hcoeff p i] at h
  simpa only [map_sub, map_add, LinearMap.comp_apply, sub_add_eq_sub_sub] using h

end PolycyclicRecognition

end

end OAI
