import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSweep
open Set MeasureTheory Filter
open scoped Topology

lemma abs_scalar_le_bound (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    |D.lam t| ≤ scalarBound D := by
  exact le_csSup (isCompact_Icc.bddAbove_image D.scalar_continuous.abs) ⟨t, ht, rfl⟩

lemma scalarBound_nonneg (D : Data) : 0 ≤ scalarBound D := by
  exact (abs_nonneg (D.lam D.α)).trans
    (abs_scalar_le_bound D ⟨le_rfl, D.interval_nonempty.le⟩)

lemma radialError_nonneg (D : Data) : 0 ≤ radialError D :=
  mul_nonneg D.length_pos.le (scalarBound_nonneg D)

lemma collar_pos (D : Data) : 0 < collar D := by
  dsimp [collar]
  linarith [radialError_nonneg D]

lemma leftTip_lt_rightEdge (D : Data) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    leftTip D N < rightEdge D N i := by
  have hd := RadialRiemann.step_pos D.interval_nonempty hN
  have hR := RadialRiemann.capMax_nonneg D.interval_nonempty D.cap_continuous D.cap_nonneg i
  have hA := radialError_nonneg D
  have hC := collar_pos D
  have hm := mul_pos hC hd
  have hn := mul_nonneg hA hd.le
  dsimp [leftTip, rightEdge]
  linarith

lemma kappa_nonneg (D : Data) : 0 ≤ kappa D := Real.sqrt_nonneg _

lemma frozenArea_nonneg (D : Data) {N : ℕ} (tag : Fin N → ℝ) (i : Fin N) :
    0 ≤ frozenArea D N tag i := by
  have hN := Nat.zero_lt_of_lt i.isLt
  have hd := (RadialRiemann.step_pos D.interval_nonempty hN).le
  unfold frozenArea
  exact div_nonneg (mul_nonneg (mul_nonneg (kappa_nonneg D) hd) (sq_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem frozenArea_tendsto (D : Data) (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged D.α D.β N (tag N)) :
    Tendsto (fun N => ∑ i : Fin N, frozenArea D N (tag N) i) atTop
      (𝓝 (weightedArea D)) := by
  exact RadialRiemann.physical_collar_tendsto D.interval_nonempty
    D.cap_continuous D.velocity_continuous (radialError D + collar D) (kappa D) tag htag

lemma weightedArea_nonneg (D : Data) : 0 ≤ weightedArea D := by
  unfold weightedArea
  apply mul_nonneg (kappa_nonneg D)
  apply intervalIntegral.integral_nonneg D.interval_nonempty.le
  intro t _
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

lemma frozenArea_eventually_lt (D : Data) (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged D.α D.β N (tag N))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, (∑ i : Fin N, frozenArea D N (tag N) i) < weightedArea D + ε :=
  (frozenArea_tendsto D tag htag).eventually_lt_const (lt_add_of_pos_right _ hε)

end CylinderCovering.RadialSweep

end

end OAI
