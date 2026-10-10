import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTerminalUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorErrorField

namespace OAI

/-! The outgoing asymptotic expansion uniquely selects the free exterior solution. -/

open Set
namespace DefocusingNLS

theorem radialExteriorPhase_second_hasDerivAt (s t : ℝ) :
    HasDerivAt (radialExteriorPhase s)
      (Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPhase s t) t := by
  have he := ((((hasDerivAt_id t).const_mul 2).exp).sub_const
    (Real.exp (2*s))).div_const 4
  have hp := (he.ofReal_comp.const_mul Complex.I).cexp
  convert hp using 1
  · rfl
  · simp only [radialExteriorPhase,id_eq,mul_one]
    push_cast
    ring

theorem radialExterior_free_gauge_derivative (ν : ℂ) (Z : ℝ → ℂ × ℂ) (t : ℝ)
    (hZ : HasDerivAt Z ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
      radialExteriorErrorMatrix ν (Z t)) t) :
    HasDerivAt (fun s => radialExteriorPropagator 0 s (Z s))
      (radialExteriorPropagator 0 t (radialExteriorErrorMatrix ν (Z t))) t := by
  have h0 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZ
  have h1 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZ
  have h := h0.prodMk ((radialExteriorPhase_second_hasDerivAt 0 t).mul h1)
  convert h using 1
  · rfl
  · apply Prod.ext
    · simp [radialExteriorErrorMatrix,radialExteriorPropagator]
    · change radialExteriorPhase 0 t*(radialExteriorErrorMatrix ν (Z t)).2 =
        Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPhase 0 t*(Z t).2+
          radialExteriorPhase 0 t*(-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2+
            (radialExteriorErrorMatrix ν (Z t)).2)
      ring

theorem radialExterior_free_fast_decay_zero (ν : ℂ) (Z : ℝ → ℂ × ℂ)
    (κ C T : ℝ)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+radialExteriorErrorMatrix ν (Z t)) t)
    (hdec : ∀ t, T ≤ t → ‖Z t‖ ≤ C*Real.exp (-κ*t))
    (hκ : radialExteriorMatrixBound ν < κ) (t : ℝ) (ht : T ≤ t) : Z t=0 := by
  let Y : ℝ → ℂ × ℂ := fun s => radialExteriorPropagator 0 s (Z s)
  let Y' : ℝ → ℂ × ℂ := fun s => radialExteriorPropagator 0 s (radialExteriorErrorMatrix ν (Z s))
  have hd : ∀ s, T ≤ s → HasDerivAt Y (Y' s) s := by
    intro s hs
    exact radialExterior_free_gauge_derivative ν Z s (hZ s hs)
  have hc : ContinuousOn Y (Ici T) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hb : ∀ s, T ≤ s → ‖Y' s‖ ≤ radialExteriorMatrixBound ν*‖Y s‖ := by
    intro s _
    simpa only [Y',Y,radialExteriorPropagator_norm] using radialExteriorErrorMatrix_norm ν (Z s)
  have he := eq_zero_of_fast_exponential_decay Y Y' (radialExteriorMatrixBound ν) κ C T hc hd hb
    (fun s hs => by simpa only [Y,radialExteriorPropagator_norm] using hdec s hs) hκ t ht
  apply norm_eq_zero.mp
  rw [← radialExteriorPropagator_norm 0 t (Z t)]
  exact norm_eq_zero.mpr he

end DefocusingNLS

end OAI
