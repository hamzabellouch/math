import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFreeUniqueness
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUnweight
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialOddPowerBound

namespace OAI

/-! The full outgoing expansion uniquely selects a nonlinear exterior solution. -/

open Set
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExterior_forced_gauge_derivative (ν : ℂ) (Z : ℝ → ℂ × ℂ)
    (t : ℝ) (R : ℂ × ℂ)
    (hZ : HasDerivAt Z ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
      radialExteriorErrorMatrix ν (Z t)+R) t) :
    HasDerivAt (fun s => radialExteriorPropagator 0 s (Z s))
      (radialExteriorPropagator 0 t (radialExteriorErrorMatrix ν (Z t)+R)) t := by
  have h0 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZ
  have h1 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt t hZ
  have h := h0.prodMk ((radialExteriorPhase_second_hasDerivAt 0 t).mul h1)
  apply h.congr_deriv
  apply Prod.ext
  · simp [radialExteriorPropagator]
  · change Complex.I*(Real.exp (2*t)/2 : ℝ)*radialExteriorPhase 0 t*(Z t).2+
        radialExteriorPhase 0 t*((-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2+
          (radialExteriorErrorMatrix ν (Z t)).2)+R.2) =
      radialExteriorPhase 0 t*((radialExteriorErrorMatrix ν (Z t)).2+R.2)
    ring

theorem radialExterior_nonlinear_fast_decay_unique (ν : ℂ) (n : ℕ)
    (Z W : ℝ → ℂ × ℂ) (ρ κ C T : ℝ) (hρ : 0 ≤ ρ)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
        radialExteriorErrorMatrix ν (Z t)+(0,oddPowerNonlinearity n (Z t).1)) t)
    (hW : ∀ t, T ≤ t → HasDerivAt W
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(W t).2)+
        radialExteriorErrorMatrix ν (W t)+(0,oddPowerNonlinearity n (W t).1)) t)
    (hbZ : ∀ t, T ≤ t → ‖(Z t).1‖ ≤ ρ)
    (hbW : ∀ t, T ≤ t → ‖(W t).1‖ ≤ ρ)
    (hdec : ∀ t, T ≤ t → ‖Z t-W t‖ ≤ C*Real.exp (-κ*t))
    (hκ : radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*ρ^(2*n) < κ)
    (t : ℝ) (ht : T ≤ t) : Z t=W t := by
  let U : ℝ → ℂ × ℂ := fun s => Z s-W s
  let R : ℝ → ℂ × ℂ := fun s => (0,oddPowerNonlinearity n (Z s).1-
    oddPowerNonlinearity n (W s).1)
  let L : ℝ := (2*(n : ℝ)+1)*ρ^(2*n)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hd : ∀ s, T ≤ s → HasDerivAt U
      ((0,-Complex.I*(Real.exp (2*s)/2 : ℝ)*(U s).2)+
        radialExteriorErrorMatrix ν (U s)+R s) s := by
    intro s hs
    apply ((hZ s hs).sub (hW s hs)).congr_deriv
    apply Prod.ext
    · simp [U,R,radialExteriorErrorMatrix]
    · simp [U,R,radialExteriorErrorMatrix]
      ring
  let Y : ℝ → ℂ × ℂ := fun s => radialExteriorPropagator 0 s (U s)
  let Y' : ℝ → ℂ × ℂ := fun s =>
    radialExteriorPropagator 0 s (radialExteriorErrorMatrix ν (U s)+R s)
  have hdy : ∀ s, T ≤ s → HasDerivAt Y (Y' s) s := by
    intro s hs
    exact radialExterior_forced_gauge_derivative ν U s (R s) (hd s hs)
  have hR : ∀ s, T ≤ s → ‖R s‖ ≤ L*‖U s‖ := by
    intro s hs
    change max ‖(0 : ℂ)‖ ‖oddPowerNonlinearity n (Z s).1-
      oddPowerNonlinearity n (W s).1‖ ≤ _
    rw [norm_zero,max_eq_right (norm_nonneg _)]
    exact (radial_oddPower_difference n ρ hρ _ _ (hbZ s hs) (hbW s hs)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (U s)) hL)
  have hb : ∀ s, T ≤ s → ‖Y' s‖ ≤ (radialExteriorMatrixBound ν+L)*‖Y s‖ := by
    intro s hs
    dsimp [Y',Y]
    rw [radialExteriorPropagator_norm,radialExteriorPropagator_norm]
    exact (norm_add_le _ _).trans ((add_le_add
      (radialExteriorErrorMatrix_norm ν (U s)) (hR s hs)).trans_eq (by ring))
  have he := eq_zero_of_fast_exponential_decay Y Y'
    (radialExteriorMatrixBound ν+L) κ C T
    (fun s hs => (hdy s hs).continuousAt.continuousWithinAt) hdy hb
    (fun s hs => by simpa only [Y,U,radialExteriorPropagator_norm] using hdec s hs)
    hκ t ht
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← radialExteriorPropagator_norm 0 t (Z t-W t)]
  exact norm_eq_zero.mpr he

theorem radialExterior_same_expansion_unique (ν : ℂ) (n : ℕ)
    (Z W P : ℝ → ℂ × ℂ) (v w : ℝ →ᵇ ℂ × ℂ) (ρ κ T : ℝ) (hρ : 0 ≤ ρ)
    (hZ : ∀ t, T ≤ t → HasDerivAt Z
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
        radialExteriorErrorMatrix ν (Z t)+(0,oddPowerNonlinearity n (Z t).1)) t)
    (hW : ∀ t, T ≤ t → HasDerivAt W
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(W t).2)+
        radialExteriorErrorMatrix ν (W t)+(0,oddPowerNonlinearity n (W t).1)) t)
    (hbZ : ∀ t, T ≤ t → ‖(Z t).1‖ ≤ ρ)
    (hbW : ∀ t, T ≤ t → ‖(W t).1‖ ≤ ρ)
    (heZ : ∀ t, T ≤ t → Z t=P t+radialExteriorUnweight κ v t)
    (heW : ∀ t, T ≤ t → W t=P t+radialExteriorUnweight κ w t)
    (hκ : radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*ρ^(2*n) < κ)
    (t : ℝ) (ht : T ≤ t) : Z t=W t := by
  apply radialExterior_nonlinear_fast_decay_unique ν n Z W ρ κ (‖v‖+‖w‖) T
    hρ hZ hW hbZ hbW ?_ hκ t ht
  intro s hs
  rw [heZ s hs,heW s hs,add_sub_add_left_eq_sub]
  calc
    _ ≤ ‖radialExteriorUnweight κ v s‖+‖radialExteriorUnweight κ w s‖ := norm_sub_le _ _
    _ ≤ Real.exp (-κ*s)*‖v‖+Real.exp (-κ*s)*‖w‖ :=
      add_le_add (radialExteriorUnweight_norm κ s v ‖v‖ (v.norm_coe_le_norm s))
        (radialExteriorUnweight_norm κ s w ‖w‖ (w.norm_coe_le_norm s))
    _ = _ := by ring

end DefocusingNLS

end OAI
