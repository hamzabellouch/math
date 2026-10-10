import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.TopDualPairing
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace OAI

/-! # Polar templates and their exact vanishing directions

The compact unit slice of the negative polar has support zero on the cone
and strictly positive support at every functional outside the cone. These
are the widths used in the cone-ideal covering argument.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric
open scoped Pointwise

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- The unit-ball slice of the negative polar of the closed weight cone. -/
def conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) : Set W :=
  {x | ‖x‖ ≤ 1 ∧ ∀ β ∈ C, β x ≤ 0}

omit [FiniteDimensional ℝ W] in
theorem zero_mem_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    (0 : W) ∈ conePolarTemplate C := by
  simp [conePolarTemplate]

theorem isCompact_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    IsCompact (conePolarTemplate C) := by
  have hc : IsClosed {x : W | ∀ β ∈ C, β x ≤ 0} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun β => isClosed_iInter fun _ =>
      isClosed_le β.continuous continuous_const
  exact (isCompact_closedBall (0 : W) 1).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter hc) (fun x hx => by
      simpa only [mem_closedBall, dist_zero_right] using hx.1)

omit [FiniteDimensional ℝ W] in
theorem convex_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W)) :
    Convex ℝ (conePolarTemplate C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · calc
      ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx.1 ha)
        (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = 1 := by linarith
  · intro β hβ
    simpa only [map_add, map_smul, smul_eq_mul, add_zero] using
      add_le_add (mul_nonpos_of_nonneg_of_nonpos ha (hx.2 β hβ))
        (mul_nonpos_of_nonneg_of_nonpos hb (hy.2 β hβ))

/-- Separation and rescaling supply a point with strictly positive evaluation. -/
theorem exists_pos_on_conePolarTemplate (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∉ C) :
    ∃ x ∈ conePolarTemplate C, 0 < β x := by
  obtain ⟨f, hf, hneg⟩ := C.hyperplane_separation_point hβ
  obtain ⟨w, hw⟩ := (topDualPairing ℝ W).flip.toContPerfPair.surjective f
  have heval (α : StrongDual ℝ W) : α w = f α := congrArg (fun g => g α) hw
  let c : ℝ := (‖w‖ + 1)⁻¹
  have hden : 0 < ‖w‖ + 1 := by positivity
  have hc : 0 < c := inv_pos.mpr hden
  refine ⟨c • (-w), ⟨?_, ?_⟩, ?_⟩
  · rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos hc]
    change (‖w‖ + 1)⁻¹ * ‖w‖ ≤ 1
    exact (inv_mul_le_iff₀ hden).mpr (by linarith)
  · intro α hα
    rw [map_smul, map_neg, smul_eq_mul, heval]
    exact mul_nonpos_of_nonneg_of_nonpos hc.le (neg_nonpos.mpr (hf α hα))
  · rw [map_smul, map_neg, smul_eq_mul, heval]
    exact mul_pos hc (neg_pos.mpr hneg)

def conePolarWidth (C : ProperCone ℝ (StrongDual ℝ W)) (β : StrongDual ℝ W) : ℝ :=
  sSup (β '' conePolarTemplate C)

theorem conePolarWidth_nonneg (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) : 0 ≤ conePolarWidth C β := by
  apply le_csSup ((isCompact_conePolarTemplate C).image β.continuous).bddAbove
  exact ⟨0, zero_mem_conePolarTemplate C, β.map_zero⟩

theorem conePolarWidth_eq_zero (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∈ C) : conePolarWidth C β = 0 := by
  apply le_antisymm _ (conePolarWidth_nonneg C β)
  change sSup (β '' conePolarTemplate C) ≤ 0
  have hne : (β '' conePolarTemplate C).Nonempty :=
    ⟨β 0, 0, zero_mem_conePolarTemplate C, rfl⟩
  apply csSup_le hne
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2 β hβ

theorem conePolarWidth_pos (C : ProperCone ℝ (StrongDual ℝ W))
    {β : StrongDual ℝ W} (hβ : β ∉ C) : 0 < conePolarWidth C β := by
  obtain ⟨x, hx, hpos⟩ := exists_pos_on_conePolarTemplate C hβ
  exact hpos.trans_le (le_csSup
    ((isCompact_conePolarTemplate C).image β.continuous).bddAbove ⟨x, hx, rfl⟩)

theorem conePolarWidth_eq_zero_iff (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) : conePolarWidth C β = 0 ↔ β ∈ C := by
  exact ⟨fun h => by_contra fun hn => (ne_of_gt (conePolarWidth_pos C hn)) h,
    conePolarWidth_eq_zero C⟩

/-- Dilating the polar template multiplies every supporting width by the
same scalar, so a maximizing word basis works for every positive radius. -/
theorem conePolarWidth_smul (C : ProperCone ℝ (StrongDual ℝ W))
    (β : StrongDual ℝ W) {a : ℝ} (ha : 0 ≤ a) :
    sSup (β '' ((fun x : W => a • x) '' conePolarTemplate C)) =
      a * conePolarWidth C β := by
  have hcompact := isCompact_conePolarTemplate C
  have hne : (conePolarTemplate C).Nonempty := ⟨0, zero_mem_conePolarTemplate C⟩
  obtain ⟨x, hx, heq⟩ := hcompact.exists_sSup_image_eq hne β.continuous.continuousOn
  have him := hcompact.image (show Continuous (fun x : W => a • x) from continuous_const.smul continuous_id)
  apply le_antisymm
  · apply csSup_le ((hne.image _).image β)
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [map_smul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (hcompact.image β.continuous).bddAbove ⟨y, hy, rfl⟩) ha
  · change a * sSup (β '' conePolarTemplate C) ≤ _
    rw [heq]
    exact le_csSup (him.image β.continuous).bddAbove
      ⟨a • x, ⟨x, hx, rfl⟩, by simp⟩

end PolycyclicRecognition

end

end OAI
