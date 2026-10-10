import OAI.Probability.SLE.Gauge.SerpentineInfiniteArray
import OAI.Probability.SLE.Geometry.RoundedConnectorGeometry

namespace OAI

/-! Arclength gluing of the low rounded connector and the upward-continued
serpentine array. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

lemma arraySpine_zero (m j : ℕ) :
    arraySpine m j 0 = ((-100 * (m : ℝ) : ℝ) : ℂ) +
      ((-100 * (m : ℝ) : ℝ) : ℂ) * Complex.I := by
  induction j with
  | zero => simp [arraySpine, straightPiece, side]
  | succ j ih =>
    have hb : (0 : ℝ) ≤ columnEntry 0 m (j + 1) := by unfold columnEntry; positivity
    have ha : (0 : ℝ) ≤ columnEntry 0 m j + 200 * m := by unfold columnEntry; positivity
    simpa only [arraySpine, curveJoin_of_le hb, curveJoin_of_le ha] using ih

lemma arrayTangent_zero (m j : ℕ) : arrayTangent m j 0 = Complex.I := by
  induction j with
  | zero => simp [arrayTangent, straightTangent, side]
  | succ j ih =>
    have hb : (0 : ℝ) ≤ columnEntry 0 m (j + 1) := by unfold columnEntry; positivity
    have ha : (0 : ℝ) ≤ columnEntry 0 m j + 200 * m := by unfold columnEntry; positivity
    simpa only [arrayTangent, curveJoin_of_le hb, curveJoin_of_le ha] using ih

lemma lowConnector_after {H r X t : ℝ}
    (ht : connectorFourth H r X < t) :
    lowConnector H r X t = connectorTail H r X t ∧
      lowConnectorTangent H r X t = Complex.I := by
  simp only [lowConnector, lowConnectorTangent, curveJoin_of_gt ht, and_self]

def connectorEntry (H r X Y : ℝ) : ℝ := connectorFourth H r X + Y - H - 2 * r

def arrayCenter (m : ℕ) (X Y : ℝ) : ℂ :=
  ((X + 100 * m : ℝ) : ℂ) + ((Y + 100 * m : ℝ) : ℂ) * Complex.I

def completeSpine (m : ℕ) (H r X Y : ℝ) : ℝ → ℂ :=
  curveJoin (connectorEntry H r X Y) (lowConnector H r X)
    (fun t => arrayCenter m X Y + arraySpine m (2 * m) (t - connectorEntry H r X Y))

def completeTangent (m : ℕ) (H r X Y : ℝ) : ℝ → ℂ :=
  curveJoin (connectorEntry H r X Y) (lowConnectorTangent H r X)
    (fun t => arrayTangent m (2 * m) (t - connectorEntry H r X Y))

lemma completeSpine_hasDerivAt {H r X Y : ℝ} (m : ℕ) (hr : 0 < r)
    (hX : 2 * r < X) (hY : H + 2 * r < Y) (t : ℝ) :
    HasDerivAt (completeSpine m H r X Y) (completeTangent m H r X Y t) t := by
  have hentry : connectorFourth H r X < connectorEntry H r X Y := by
    unfold connectorEntry
    linarith
  have hp : lowConnector H r X (connectorEntry H r X Y) =
      arrayCenter m X Y + arraySpine m (2 * m)
        (connectorEntry H r X Y - connectorEntry H r X Y) := by
    rw [(lowConnector_after hentry).1, sub_self, arraySpine_zero]
    simp only [connectorTail, connectorEntry, arrayCenter]
    push_cast
    ring
  have hT : lowConnectorTangent H r X (connectorEntry H r X Y) =
      arrayTangent m (2 * m) (connectorEntry H r X Y - connectorEntry H r X Y) := by
    rw [(lowConnector_after hentry).2, sub_self, arrayTangent_zero]
  exact curveJoin_hasDerivAt _ _ _ _ _ (lowConnector_hasDerivAt hr hX)
    (translate_curve_hasDerivAt _ _ (arraySpine_hasDerivAt m (2 * m)) _ _) hp hT t

lemma completeTangent_norm (m : ℕ) (H r X Y t : ℝ) : ‖completeTangent m H r X Y t‖ = 1 := by
  unfold completeTangent curveJoin
  split
  · exact lowConnectorTangent_norm _ _ _ _
  · exact arrayTangent_norm _ _ _

lemma completeTangent_lipschitz {H r X Y : ℝ} (m : ℕ) (hr : 50 ≤ r)
    (hX : 2 * r < X) (hY : H + 2 * r < Y) :
    LipschitzWith (1 / 50) (completeTangent m H r X Y) := by
  have hr0 : 0 < r := by linarith
  have hentry : connectorFourth H r X < connectorEntry H r X Y := by
    unfold connectorEntry
    linarith
  apply curveJoin_lipschitz (lowConnectorTangent_lipschitz hr hX)
    (shifted_lipschitz (arrayTangent_lipschitz m (2 * m)) _)
  rw [(lowConnector_after hentry).2, sub_self, arrayTangent_zero]

lemma complete_normal_patch_bounds {H r X Y : ℝ} (m : ℕ) (hr : 50 ≤ r)
    (hX : 2 * r < X) (hY : H + 2 * r < Y) (k : ℝ) :
    LipschitzOnWith 2 (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y))
      (RibbonCoordinates.ribbonStepPatch k) ∧
    ∀ z ∈ RibbonCoordinates.ribbonStepPatch k,
      ∀ w ∈ RibbonCoordinates.ribbonStepPatch k,
        dist z w ≤ 2 * dist (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) z)
          (normalRibbon (completeSpine m H r X Y) (completeTangent m H r X Y) w) := by
  have hr0 : 0 < r := by linarith
  have hbound z (hz : z ∈ RibbonCoordinates.ribbonStepPatch k)
      w (hw : w ∈ RibbonCoordinates.ribbonStepPatch k) :=
    normalRibbon_patch_bounds (completeSpine m H r X Y) (completeTangent m H r X Y) (k - 1) (k + 3)
      (by ring_nf; norm_num)
      (fun t _ => (completeSpine_hasDerivAt m hr0 hX hY t).hasDerivWithinAt)
      (fun t _ => completeTangent_norm m H r X Y t)
      (completeTangent_lipschitz m hr hX hY).lipschitzOnWith
      z w ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  exact ⟨lipschitzOnWith_iff_dist_le_mul.mpr (fun z hz w hw => (hbound z hz w hw).1),
    fun z hz w hw => (hbound z hz w hw).2⟩

end SLEExactGauge.Serpentine

end

end OAI
