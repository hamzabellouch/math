import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialStationaryReconstruction
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoupledLargePower

namespace OAI

/-! Genuine complex stationary solutions on the full inner ball for all sufficiently large powers. -/

open Set
namespace DefocusingNLS

theorem exists_radial_inner_stationary (R : ℝ) (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) :
    ∃ P : ℕ, 400 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ b : ℝ,
      b ∈ Icc (334/1000 : ℝ) (335/1000) → ∀ lo : ℝ,
      lo ∈ Icc (1-(1/10000 : ℝ)^2/5) (1-3*(1/10000 : ℝ)^2/20) →
      ∃ Q : ℝ → ℂ, Differentiable ℝ Q ∧ 0 < (Q 0).re ∧ (Q 0).im=0 ∧
        (∀ r ∈ Icc 0 R, ‖Q r‖ ∈ Icc lo 1 ∧ ‖Q r‖^(p-1) ≤ (1/2 : ℝ)) ∧
        (∀ r ∈ Ioo 0 R,
          deriv (deriv Q) r+(11/r : ℝ)*deriv Q r+
          Complex.I*((r/2 : ℝ)*deriv Q r+((1/((p-1 : ℕ) : ℝ) : ℝ) : ℂ)*Q r)+
          (b : ℂ)*Q r=(‖Q r‖^(p-1) : ℝ)*Q r) := by
  obtain ⟨P,hP,hProfile⟩ := exists_radial_coupled_large_power_uniform R hR hR2
  refine ⟨P,hP,?_⟩
  intro p hp b hb lo hlo
  have hp400 : 400 ≤ p := hP.trans hp
  let a : ℝ := 1/((p-1 : ℕ) : ℝ)
  have hn : (399 : ℝ) ≤ ((p-1 : ℕ) : ℝ) := by exact_mod_cast (show 399 ≤ p-1 by omega)
  have hn0 : (0 : ℝ) < ((p-1 : ℕ) : ℝ) := by linarith
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have ha : a ≤ (1/200 : ℝ) := (div_le_iff₀ hn0).2 (by linarith)
  have hc : 6-2*a ∈ Icc (599/100 : ℝ) 6 := ⟨by linarith,by linarith⟩
  obtain ⟨A,hA,hDA,hAR,hA0,hAI,hEq⟩ := hProfile p hp (6-2*a) b hc hb lo hlo
  have hlo0 : 0 < lo := by linarith [hlo.1]
  have hAP : ∀ r ∈ Icc 0 R, 0 < A r := fun r hr => hlo0.trans_le (hAI r hr).1.1
  let Q := radialInnerComplex R a A
  have hPhi : Differentiable ℝ (radialInnerPhase R a A) :=
    radialPhase_differentiable (6-2*a) (radialClampedAmplitude R A)
      (radialClampedAmplitude_continuous R A hA.continuous)
      (fun r => (hAP _ (radialClamp_mem R r (by linarith))).ne')
  have hNorm : ∀ r ∈ Icc 0 R, ‖Q r‖=A r :=
    fun r hr => radialInnerComplex_norm R a A r (hAP r hr).le
  refine ⟨Q,(fun r => (radialPolar_hasDerivAt A _ hA hPhi r).differentiableAt),?_,?_,?_,?_⟩
  · change 0 < (radialInnerComplex R a A 0).re
    rw [radialInnerComplex_origin,Complex.ofReal_re]
    exact hAP 0 ⟨le_rfl,by linarith⟩
  · change (radialInnerComplex R a A 0).im=0
    rw [radialInnerComplex_origin,Complex.ofReal_im]
  · intro r hr
    rw [hNorm r hr]
    exact hAI r hr
  · intro r hr
    rw [hNorm r ⟨hr.1.le,hr.2.le⟩]
    exact radialInnerComplex_stationary p (by omega) R a b (by linarith) A hA hAP hDA hEq r hr

end DefocusingNLS

end OAI
