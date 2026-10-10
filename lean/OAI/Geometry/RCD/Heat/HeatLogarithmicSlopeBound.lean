import OAI.Geometry.RCD.Heat.HeatHamiltonPositive
import OAI.Geometry.RCD.Heat.LocalLogarithmicGradient

namespace OAI

/-! # Hamilton's bound for actual local Sobolev logarithms -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_logarithmic_slope_bound
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {T : ℝ} (hT : 0<T)
    (v : SobolevSpace (hausdorff n X) hX.quadratic) {Ω : Set X}
    (hpos : ∀ᵐ x ∂(hausdorff n X).restrict Ω, 0<heatAt (hausdorff n X) hX.quadratic T f x)
    (hchain : ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
      localGamma (hausdorff n X) hX.quadratic v w =ᵐ[(hausdorff n X).restrict Ω] fun x =>
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic T hT f) w x /
          heatAt (hausdorff n X) hX.quadratic T f x) :
    ∀ᵐ x ∂(hausdorff n X).restrict Ω, T*Real.exp (-2*|K| * T)*
      (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic v x)^2 ≤
      Real.log A-Real.log (heatAt (hausdorff n X) hX.quadratic T f x) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let u := heatSobolev μ Q T hT f
  have hp : ∀ᵐ x ∂μ.restrict Ω, 0<SobolevSpace.toLp μ Q u x := by
    simpa only [u,heatSobolev_toLp] using hpos
  have hc : ∀ w, localGamma μ Q v w =ᵐ[μ.restrict Ω] fun x =>
      localGamma μ Q u w x/SobolevSpace.toLp μ Q u x := by
    simpa only [u,heatSobolev_toLp] using hchain
  have hs := local_logarithmic_minimalSlope μ Q u v hp hc
  filter_upwards [hs,hpos,ae_restrict_of_ae (hX.heat_hamilton_positive hn p f hf0 A hf hT)] with x hs hp hh
  rw [hs,heatSobolev_toLp]
  have hb := hh hp
  calc
    _ = (T*Real.exp (-2*|K| * T)*(SobolevSpace.minimalSlope μ Q u x)^2)/
        (heatAt μ Q T f x)^2 := by rw [div_pow,mul_div_assoc]
    _ ≤ _ := (div_le_iff₀ (sq_pos_of_pos hp)).mpr (by nlinarith only [hb])

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
