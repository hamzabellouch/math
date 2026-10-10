import OAI.Probability.SLE.Geometry.RoundedConnector

namespace OAI

/-! The actual arclength connector from zero to a distant vertical column:
vertical, quarter-circle, horizontal, quarter-circle, then vertical. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

lemma translate_curve_hasDerivAt (f df : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (df t) t) (v : ℂ) (a t : ℝ) :
    HasDerivAt (fun u => v + f (u - a)) (df (t - a)) t := by
  have hh : HasDerivAt (fun u => f (u - a)) (df (t - a)) t := by
    convert (hf (t - a)).scomp t ((hasDerivAt_id t).sub_const a) using 1 <;>
      first | rfl | simp only [one_smul]
  exact hh.const_add v

lemma linear_curve_hasDerivAt (v d : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => v + (u : ℂ) * d) d t := by
  convert ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const d).const_add v using 1 <;>
    first | rfl | simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]

def connectorSecond (H r : ℝ) : ℝ := H + quarterLength r

def connectorThird (H r X : ℝ) : ℝ := connectorSecond H r + X - 2 * r

def connectorFourth (H r X : ℝ) : ℝ := connectorThird H r X + quarterLength r

def connectorInitial (t : ℝ) : ℂ := (t : ℂ) * Complex.I

def connectorFirstTurn (H r t : ℝ) : ℂ :=
  (H : ℂ) * Complex.I + quarterBend r (t - H)

def connectorHorizontal (H r t : ℝ) : ℂ :=
  (r : ℂ) + ((H + r : ℝ) : ℂ) * Complex.I + ((t - connectorSecond H r : ℝ) : ℂ)

def connectorLastTurn (H r X t : ℝ) : ℂ :=
  ((X - r : ℝ) : ℂ) + ((H + r : ℝ) : ℂ) * Complex.I +
    upperQuarter r (t - connectorThird H r X)

def connectorTail (H r X t : ℝ) : ℂ :=
  (X : ℂ) + ((H + 2 * r + (t - connectorFourth H r X) : ℝ) : ℂ) * Complex.I

def lowConnector (H r X : ℝ) : ℝ → ℂ :=
  curveJoin (connectorFourth H r X)
    (curveJoin (connectorThird H r X)
      (curveJoin (connectorSecond H r)
        (curveJoin H connectorInitial (connectorFirstTurn H r))
        (connectorHorizontal H r))
      (connectorLastTurn H r X))
    (connectorTail H r X)

def lowConnectorTangent (H r X : ℝ) : ℝ → ℂ :=
  curveJoin (connectorFourth H r X)
    (curveJoin (connectorThird H r X)
      (curveJoin (connectorSecond H r)
        (curveJoin H (fun _ => Complex.I) (fun t => quarterTangent r (t - H)))
        (fun _ => 1))
      (fun t => upperQuarterTangent r (t - connectorThird H r X)))
    (fun _ => Complex.I)

lemma connector_cuts {H r X : ℝ} (hr : 0 < r) (hX : 2 * r < X) :
    H < connectorSecond H r ∧ connectorSecond H r < connectorThird H r X ∧
      connectorThird H r X < connectorFourth H r X := by
  have hq : 0 < quarterLength r := by unfold quarterLength; positivity
  dsimp [connectorSecond, connectorThird, connectorFourth]
  constructor
  · linarith
  constructor <;> linarith

lemma connector_position_matches {H r X : ℝ} (hr : 0 < r) :
    connectorInitial H = connectorFirstTurn H r H ∧
    connectorFirstTurn H r (connectorSecond H r) = connectorHorizontal H r (connectorSecond H r) ∧
    connectorHorizontal H r (connectorThird H r X) = connectorLastTurn H r X (connectorThird H r X) ∧
    connectorLastTurn H r X (connectorFourth H r X) = connectorTail H r X (connectorFourth H r X) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [connectorInitial, connectorFirstTurn, quarterBend_zero]
  · simp only [connectorFirstTurn, connectorSecond, add_sub_cancel_left, quarterBend_end hr,
      connectorHorizontal, sub_self, Complex.ofReal_zero, add_zero]
    push_cast
    ring
  · simp only [connectorHorizontal, connectorLastTurn, sub_self, upperQuarter_zero hr, add_zero]
    dsimp only [connectorThird]
    push_cast
    ring
  · have he : connectorFourth H r X - connectorThird H r X = quarterLength r := by
      dsimp [connectorFourth]; ring
    simp only [connectorLastTurn, connectorTail, he, upperQuarter_end, sub_self, add_zero]
    push_cast
    ring

lemma lowConnector_hasDerivAt {H r X : ℝ} (hr : 0 < r) (hX : 2 * r < X) (t : ℝ) :
    HasDerivAt (lowConnector H r X) (lowConnectorTangent H r X t) t := by
  obtain ⟨hc1, hc2, hc3⟩ := connector_cuts (H := H) hr hX
  obtain ⟨hp1, hp2, hp3, hp4⟩ := connector_position_matches (H := H) (X := X) hr
  have hd0 (u : ℝ) : HasDerivAt connectorInitial Complex.I u := by
    change HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I u
    simpa only [zero_add] using linear_curve_hasDerivAt 0 Complex.I u
  have hd1 (u : ℝ) : HasDerivAt (connectorFirstTurn H r) (quarterTangent r (u - H)) u :=
    translate_curve_hasDerivAt _ _ (quarterBend_hasDerivAt hr) _ _ _
  have hd2 (u : ℝ) : HasDerivAt (connectorHorizontal H r) 1 u := by
    have hh := translate_curve_hasDerivAt (fun v : ℝ => (v : ℂ)) (fun _ => 1)
      (fun v => by simpa only [zero_add, mul_one] using linear_curve_hasDerivAt 0 1 v)
      ((r : ℂ) + ((H + r : ℝ) : ℂ) * Complex.I) (connectorSecond H r) u
    exact hh
  have hd3 (u : ℝ) : HasDerivAt (connectorLastTurn H r X)
      (upperQuarterTangent r (u - connectorThird H r X)) u :=
    translate_curve_hasDerivAt _ _ (upperQuarter_hasDerivAt hr) _ _ _
  have hd4 (u : ℝ) : HasDerivAt (connectorTail H r X) Complex.I u := by
    have hh := linear_curve_hasDerivAt
      ((X : ℂ) + ((H + 2 * r - connectorFourth H r X : ℝ) : ℂ) * Complex.I) Complex.I u
    convert hh using 1
    funext v
    simp only [connectorTail]
    push_cast
    ring
  have hj1 := curveJoin_hasDerivAt H _ _ _ _ hd0 hd1 hp1
    (by simp [quarterTangent_zero])
  have hp2' : curveJoin H connectorInitial (connectorFirstTurn H r) (connectorSecond H r) =
      connectorHorizontal H r (connectorSecond H r) := by
    rw [curveJoin_of_gt hc1]; exact hp2
  have hj2 := curveJoin_hasDerivAt (connectorSecond H r) _ _ _ _ hj1 hd2 hp2'
    (by rw [curveJoin_of_gt hc1]; simp [connectorSecond, quarterTangent_end hr])
  have hp3' : curveJoin (connectorSecond H r)
      (curveJoin H connectorInitial (connectorFirstTurn H r)) (connectorHorizontal H r)
      (connectorThird H r X) = connectorLastTurn H r X (connectorThird H r X) := by
    rw [curveJoin_of_gt hc2]; exact hp3
  have hj3 := curveJoin_hasDerivAt (connectorThird H r X) _ _ _ _ hj2 hd3 hp3'
    (by rw [curveJoin_of_gt hc2]; simp [upperQuarterTangent_zero hr])
  have hp4' : curveJoin (connectorThird H r X)
      (curveJoin (connectorSecond H r)
        (curveJoin H connectorInitial (connectorFirstTurn H r)) (connectorHorizontal H r))
      (connectorLastTurn H r X) (connectorFourth H r X) = connectorTail H r X (connectorFourth H r X) := by
    rw [curveJoin_of_gt hc3]; exact hp4
  exact curveJoin_hasDerivAt (connectorFourth H r X) _ _ _ _ hj3 hd4 hp4'
    (by rw [curveJoin_of_gt hc3]; simp [connectorFourth, upperQuarterTangent_end]) t

lemma lowConnectorTangent_norm (H r X t : ℝ) : ‖lowConnectorTangent H r X t‖ = 1 := by
  unfold lowConnectorTangent curveJoin
  split
  · split
    · split
      · split
        · exact Complex.norm_I
        · exact quarterTangent_norm _ _
      · exact norm_one
    · exact upperQuarterTangent_norm _ _
  · exact Complex.norm_I

end SLEExactGauge.Serpentine

end

end OAI
