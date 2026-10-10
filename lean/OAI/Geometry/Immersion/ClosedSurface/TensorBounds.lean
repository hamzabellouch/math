import OAI.Geometry.Immersion.ClosedSurface.MetricTensors

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma contDiffOn_realDot {n : ℕ} {U : Set Base} {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (fun p => X p ⬝ᵥ Y p) U := by
  exact ContDiffOn.sum fun i _ => (contDiffOn_pi.mp hX i).mul (contDiffOn_pi.mp hY i)

lemma contDiffOn_realMetricTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X : RField n}
    (hX : ContDiffOn ℝ ∞ X U) : ContDiffOn ℝ ∞ (realMetricTensor X) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realMetricTensor_apply, realMetric]
  exact contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hX _)

lemma contDiffOn_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (realLinearizedTensor X Y) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realLinearizedTensor_apply, realLinearized]
  exact (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hY _)).add
    (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
      (contDiffOn_coordDeriv_vector hU hY _))

lemma weighted_realMetricTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {X : RField n} {τ C : ℝ} {m : ℕ} (hτ : 0 < τ) (hC : 0 ≤ C)
    (hX : ContDiffOn ℝ ∞ X U) (hb : WeightedBound U τ (m + 1) C X) :
    WeightedBound U τ m ((n : ℝ) * (2 ^ m * (C / τ) * (C / τ))) (realMetricTensor X) := by
  have hd (v : Base) (hv : ‖v‖ ≤ 1) : WeightedBound U τ m (C / τ) (coordDeriv v X) := by
    exact (hb.directional hU hτ hX v).mono_const
      (mul_le_of_le_one_left (div_nonneg hC hτ.le) hv)
  apply WeightedBound.pi hU.uniqueDiffOn hτ (by positivity)
  · exact contDiffOn_pi.mp (contDiffOn_realMetricTensor hU hX)
  · intro i
    simpa only [realMetricTensor_apply, realMetric, Fintype.card_fin] using
      (hd _ (norm_firstDirection i)).dot_real hU.uniqueDiffOn hτ.le (by positivity) (by positivity)
        (contDiffOn_coordDeriv_vector hU hX _) (contDiffOn_coordDeriv_vector hU hX _)
        (hd _ (norm_secondDirection i))

lemma weighted_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {X Y : RField n} {τ C D : ℝ} {m : ℕ} (hτ : 0 < τ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbX : WeightedBound U τ (m + 1) C X) (hbY : WeightedBound U τ (m + 1) D Y) :
    WeightedBound U τ m (2 * (n : ℝ) * (2 ^ m * (C / τ) * (D / τ)))
      (realLinearizedTensor X Y) := by
  have hdX (v : Base) (hv : ‖v‖ ≤ 1) : WeightedBound U τ m (C / τ) (coordDeriv v X) := by
    exact (hbX.directional hU hτ hX v).mono_const
      (mul_le_of_le_one_left (div_nonneg hC hτ.le) hv)
  have hdY (v : Base) (hv : ‖v‖ ≤ 1) : WeightedBound U τ m (D / τ) (coordDeriv v Y) := by
    exact (hbY.directional hU hτ hY v).mono_const
      (mul_le_of_le_one_left (div_nonneg hD hτ.le) hv)
  have hdot (v w : Base) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :=
    (hdX v hv).dot_real hU.uniqueDiffOn hτ.le (by positivity) (by positivity)
      (contDiffOn_coordDeriv_vector hU hX v) (contDiffOn_coordDeriv_vector hU hY w) (hdY w hw)
  apply WeightedBound.pi hU.uniqueDiffOn hτ (by positivity)
  · exact contDiffOn_pi.mp (contDiffOn_realLinearizedTensor hU hX hY)
  · intro i
    have ha := (hdot _ _ (norm_firstDirection i) (norm_secondDirection i)).add
      hU.uniqueDiffOn hτ.le
      (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _) (contDiffOn_coordDeriv_vector hU hY _))
      (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _) (contDiffOn_coordDeriv_vector hU hY _))
      (hdot _ _ (norm_secondDirection i) (norm_firstDirection i))
    simp only [Fintype.card_fin] at ha
    have he : (n : ℝ) * (2 ^ m * (C / τ) * (D / τ)) +
        (n : ℝ) * (2 ^ m * (C / τ) * (D / τ)) =
        2 * (n : ℝ) * (2 ^ m * (C / τ) * (D / τ)) := by ring
    rw [he] at ha
    simpa only [realLinearizedTensor_apply, realLinearized] using ha



theorem weighted_cubic_remainder {n : ℕ} {U : Set Base} (hU : IsOpen U)
    {X Y : RField n} {τ δ A B : ℝ} {m : ℕ} (hτ : 0 < τ) (hδ : 0 ≤ δ) (hδτ : δ ≤ τ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hbX : WeightedBound U τ (m + 1) (A * δ * τ) X)
    (hbY : WeightedBound U τ (m + 1) (B * δ ^ 2) Y) :
    WeightedBound U τ m ((n : ℝ) * 2 ^ m * (2 * A * B + B ^ 2) * (δ ^ 3 / τ))
      (fun p => realLinearizedTensor X Y p + realMetricTensor Y p) := by
  have hc := weighted_realLinearizedTensor hU hτ (by positivity) (by positivity) hX hY hbX hbY
  have hq := weighted_realMetricTensor hU hτ (by positivity) hY hbY
  have hb := hc.add hU.uniqueDiffOn hτ.le (contDiffOn_realLinearizedTensor hU hX hY)
    (contDiffOn_realMetricTensor hU hY) hq
  apply hb.mono_const
  have he : 2 * (n : ℝ) * (2 ^ m * (A * δ * τ / τ) * (B * δ ^ 2 / τ)) +
      (n : ℝ) * (2 ^ m * (B * δ ^ 2 / τ) * (B * δ ^ 2 / τ)) =
      (n : ℝ) * 2 ^ m * (2 * A * B + B ^ 2 * (δ / τ)) * (δ ^ 3 / τ) := by
    field_simp
  rw [he]
  gcongr
  exact mul_le_of_le_one_right (sq_nonneg B) ((div_le_one hτ).2 hδτ)

end ClosedSurfaceR4.RealModes

end

end OAI
