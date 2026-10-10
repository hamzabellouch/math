import OAI.MathematicalPhysics.DefocusingNLS.Certificates.HighAngularFluxLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI

/-! The outgoing ray has strictly negative initial flux in high angular degree. -/

open Set Filter Topology
namespace DefocusingNLS

theorem highRayActualFlux_deriv_nonneg (q : ℂ) (M : ℕ) (Z h t : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hM : 9 ≤ M)
    (hσ : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-q).re)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) (ht : 0 ≤ t) :
    0 ≤ deriv (highRayActualFlux q M Z h) t := by
  rw [(hasDerivAt_highRayActualFlux q M Z h t hq hh hZ hZ' ht).deriv]
  have hL := (highRay_bounds Z t hZ hZ' ht).2.2.2.2
  have hV := highRayPotential_pos _ (M : ℝ) Z t hσ (by exact_mod_cast hM) hZ hZ' ht
  exact add_nonneg (mul_nonneg (by linarith) (Complex.normSq_nonneg _))
    (mul_nonneg hV.le (Complex.normSq_nonneg _))

theorem highRayActualFlux_monotoneOn (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hM : 9 ≤ M)
    (hσ : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-q).re)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    MonotoneOn (highRayActualFlux q M Z h) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro t ht
    exact (hasDerivAt_highRayActualFlux q M Z h t hq hh hZ hZ' ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hasDerivAt_highRayActualFlux q M Z h t hq hh hZ hZ'
      (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact highRayActualFlux_deriv_nonneg q M Z h t hq hh hM hσ hZ hZ' (interior_subset ht)

theorem highRayActualFlux_nonpos (q : ℂ) (M : ℕ) (Z h t : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hM : 9 ≤ M)
    (hσ : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-q).re)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) (ht : 0 ≤ t) :
    highRayActualFlux q M Z h t ≤ 0 := by
  apply ge_of_tendsto (highRayActualFlux_tendsto_zero q M Z h hq hh hZ hZ')
  filter_upwards [eventually_ge_atTop t] with s hs
  exact highRayActualFlux_monotoneOn q M Z h hq hh hM hσ hZ hZ' ht (ht.trans hs) hs

theorem highRayActualFlux_initial_neg (q : ℂ) (M : ℕ) (Z h : ℝ)
    (hq : -1 < q.re) (hh : h=1 ∨ h= -1) (hM : 9 ≤ M)
    (hσ : -(1/32 : ℝ) ≤ 3-(((M : ℂ)+1)/2-q).re)
    (hZ : 2704/1000 ≤ Z) (hZ' : Z ≤ 2706/1000) :
    highRayActualFlux q M Z h 0 < 0 := by
  by_contra hn
  have hzero : highRayActualFlux q M Z h 0 = 0 := le_antisymm
    (highRayActualFlux_nonpos q M Z h 0 hq hh hM hσ hZ hZ' le_rfl) (le_of_not_gt hn)
  have hz (t : ℝ) (ht : 0 ≤ t) : highRayActualFlux q M Z h t = 0 := by
    apply le_antisymm (highRayActualFlux_nonpos q M Z h t hq hh hM hσ hZ hZ' ht)
    rw [← hzero]
    exact highRayActualFlux_monotoneOn q M Z h hq hh hM hσ hZ hZ' (by simp only [mem_Ici, le_refl]) ht ht
  obtain ⟨R,hR,hH⟩ := regularizedSlowSolution_nonzero_at_large_norm q (M+1) hq
  let t : ℝ := 2*R+2
  have ht : 0 < t := by dsimp [t]; linarith
  have hx : 0 ≤ (highRayPoint Z h t).re := by
    rw [highRayPoint_re]
    dsimp [highRayU]
    positivity
  have hnR : R ≤ ‖highRayPoint Z h t‖ := by
    have hle := (le_abs_self (highRayPoint Z h t).re).trans (Complex.abs_re_le_norm _)
    rw [highRayPoint_re] at hle
    dsimp [highRayU,t] at hle
    linarith
  have hG : slowGauge M (highRayPoint Z h t) ≠ 0 := by
    unfold slowGauge
    apply mul_ne_zero (Complex.exp_ne_zero _)
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl (highRayPoint_ne_zero Z h t ht.le))
  have hU : highRayWave q M Z h t ≠ 0 := by
    change slowGauge M (highRayPoint Z h t)*regularizedSlowSolution q (M+1) (highRayPoint Z h t) ≠ 0
    exact mul_ne_zero hG (hH _ hx hnR)
  have hderiv : 0 < deriv (highRayActualFlux q M Z h) t := by
    rw [(hasDerivAt_highRayActualFlux q M Z h t hq hh hZ hZ' ht.le).deriv]
    have hL := (highRay_bounds Z t hZ hZ' ht.le).2.2.2.2
    have hV := highRayPotential_pos _ (M : ℝ) Z t hσ (by exact_mod_cast hM) hZ hZ' ht.le
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by linarith) (Complex.normSq_nonneg _))
      (mul_pos hV (Complex.normSq_pos.mpr hU))
  have he : highRayActualFlux q M Z h =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hz s hs.le
  have hd0 := he.deriv_eq
  rw [deriv_const] at hd0
  linarith

end DefocusingNLS

end OAI
