import OAI.Analysis.CircleDomains.Sobolev.SobolevLinePayment

namespace OAI

/-! Vanishing global Sobolev energy excludes a positive measure family of
coordinate crossings. The crossing locations may vary with every barrier. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem measure_zero_of_vanishing_sobolev_barriers
    {v : ℕ → EuclideanPlane → ℝ}
    (W : ∀ n, DeGiorgi.MemW1pWitness 2 (v n) univ)
    (hv : ∀ n, Continuous (v n)) {L : ℝ} (hL : 0 < L)
    (hs : ∀ n, tsupport (v n) ⊆ ball 0 L)
    (hE : Tendsto (fun n => ∫ x, ‖(W n).weakGrad x‖^2) atTop (𝓝 0))
    (i : Fin 2) {J : Set ℝ} (hJ : MeasurableSet J) (hJL : J ⊆ Icc (-L) L)
    (hcross : ∀ᶠ n in atTop, ∀ y ∈ J,
      ∃ c ∈ Icc (-L) L, v n (physicalCoordinateLine i y c) = 1) :
    volume J = 0 := by
  have hp : ∀ᶠ n in atTop, (volume J).toReal/(8*L) ≤
      ∫ x, ‖(W n).weakGrad x‖^2 := by
    filter_upwards [hcross] with n hn
    exact sobolev_coordinate_line_payment (hv n) (W n) hL (hs n) i hJ hJL hn
  have hz := ge_of_tendsto hE hp
  have hreal : (volume J).toReal = 0 := by
    have hmul := (div_le_iff₀ (by positivity : 0 < 8*L)).mp hz
    exact le_antisymm (by simpa only [zero_mul] using hmul) ENNReal.toReal_nonneg
  have hf : volume J ≠ ∞ := ne_of_lt ((measure_mono hJL).trans_lt measure_Icc_lt_top)
  exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hf

end CircleDomainRigidity

end

end OAI
