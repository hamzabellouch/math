import OAI.Analysis.KadisonKastler.L2Intertwining

namespace OAI

/-! # Intertwining the adjoint regular gauge -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compLp_regularGauge_star (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (f : RegularCoreHilbert H) :
    L.compLp ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f) =
      (star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K) (L.compLp f) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp ((star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularGauge_star_apply_ae U hU f,
    regularGauge_star_apply_ae V hV (L.compLp f), L.coeFn_compLp f]
    with t hl hu hv hf
  rw [hl, hu, hv, hf]
  have hu' := regularGroup_star_eq U t
  have hv' := regularGroup_star_eq V t
  change L ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) (f t)) =
    (star (V (Multiplicative.ofAdd t)) : K →L[ℂ] K) (L (f t))
  have huC : star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) :=
    congrArg (fun w : unitary (H →L[ℂ] H) => (w : H →L[ℂ] H)) hu'
  have hvC : star (V (Multiplicative.ofAdd t) : K →L[ℂ] K) =
      (V (Multiplicative.ofAdd (-t)) : K →L[ℂ] K) :=
    congrArg (fun w : unitary (K →L[ℂ] K) => (w : K →L[ℂ] K)) hv'
  rw [huC, hvC]
  exact hL (Multiplicative.ofAdd (-t)) (f t)

end

end KadisonKastler

end OAI
