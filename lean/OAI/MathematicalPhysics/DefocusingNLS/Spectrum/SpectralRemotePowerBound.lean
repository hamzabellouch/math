import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEnergy
import Mathlib.Analysis.ODE.Gronwall

namespace OAI

/-! Uniform propagation in logarithmic radius; the large skew leading coefficient does not enter. -/

open Set
namespace DefocusingNLS

theorem spectralRemote_energy_growth
    (Y e : ℝ → SpectralRemoteSpace) (omega : ℝ → SpectralRemoteIndex → ℝ)
    (s t C : ℝ) (hst : s ≤ t) (hC : 0 ≤ C)
    (hY : ∀ u ∈ Icc s t, HasDerivAt Y (spectralRemoteSkew (omega u) (Y u)+e u) u)
    (he : ∀ u ∈ Icc s t, ‖e u‖ ≤ C*‖Y u‖) :
    spectralRemoteEnergy (Y t) ≤ spectralRemoteEnergy (Y s)*Real.exp (8*C*(t-s)) := by
  let E := fun u => spectralRemoteEnergy (Y u)
  let D := fun u => 2*spectralRemoteReal (Y u) (e u)
  have hd (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt E (D u) u ∧ |D u| ≤ 8*C*E u :=
    spectralRemoteEnergy_skew_bound Y (e u) (omega u) u C hC (hY u hu) (he u hu)
  have hcont : ContinuousOn E (Icc s t) := fun u hu => (hd u hu).1.continuousAt.continuousWithinAt
  have hnorm : ∀ u, ‖E u‖ = E u := fun u => Real.norm_of_nonneg (spectralRemoteEnergy_nonneg (Y u))
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le (f := E) (f' := D)
    (δ := E s) (K := 8*C) (ε := 0) hcont
    (fun u hu => (hd u ⟨hu.1,hu.2.le⟩).1.hasDerivWithinAt)
    (by rw [hnorm])
    (fun u hu => by simpa only [Real.norm_eq_abs,hnorm,add_zero] using (hd u ⟨hu.1,hu.2.le⟩).2)
    t ⟨hst,le_rfl⟩
  simpa only [hnorm,gronwallBound_ε0] using hb

theorem spectralRemote_norm_growth
    (Y e : ℝ → SpectralRemoteSpace) (omega : ℝ → SpectralRemoteIndex → ℝ)
    (s t C : ℝ) (hst : s ≤ t) (hC : 0 ≤ C)
    (hY : ∀ u ∈ Icc s t, HasDerivAt Y (spectralRemoteSkew (omega u) (Y u)+e u) u)
    (he : ∀ u ∈ Icc s t, ‖e u‖ ≤ C*‖Y u‖) :
    ‖Y t‖ ≤ 2*Real.exp (4*C*(t-s))*‖Y s‖ := by
  have hg := spectralRemote_energy_growth Y e omega s t C hst hC hY he
  have hupper := spectralRemoteEnergy_upper (Y s)
  have hlower := spectralRemoteEnergy_lower (Y t)
  have hexp : Real.exp (8*C*(t-s)) = (Real.exp (4*C*(t-s)))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hg
  have he0 := Real.exp_pos (4*C*(t-s))
  have hh := mul_le_mul_of_nonneg_right hupper (sq_nonneg (Real.exp (4*C*(t-s))))
  apply (sq_le_sq₀ (norm_nonneg (Y t)) (by positivity)).mp
  exact hlower.trans (hg.trans (hh.trans_eq (by ring)))

theorem spectralRemote_norm_growth_reverse
    (Y e : ℝ → SpectralRemoteSpace) (omega : ℝ → SpectralRemoteIndex → ℝ)
    (s t C : ℝ) (hst : s ≤ t) (hC : 0 ≤ C)
    (hY : ∀ u ∈ Icc s t, HasDerivAt Y (spectralRemoteSkew (omega u) (Y u)+e u) u)
    (he : ∀ u ∈ Icc s t, ‖e u‖ ≤ C*‖Y u‖) :
    ‖Y s‖ ≤ 2*Real.exp (4*C*(t-s))*‖Y t‖ := by
  have hmem (u : ℝ) (hu : u ∈ Icc (-t) (-s)) : -u ∈ Icc s t := by
    constructor <;> linarith [hu.1,hu.2]
  have hd (u : ℝ) (hu : u ∈ Icc (-t) (-s)) :
      HasDerivAt (fun x => Y (-x))
        (spectralRemoteSkew (fun i => -omega (-u) i) (Y (-u)) + -e (-u)) u := by
    have hh := (hY (-u) (hmem u hu)).scomp u (hasDerivAt_neg u)
    convert hh using 1
    · rfl
    · simp only [spectralRemoteSkew,neg_smul,one_smul,neg_add_rev,Prod.neg_mk,
        Complex.ofReal_neg,mul_neg,neg_mul]
      abel
  have hb (u : ℝ) (hu : u ∈ Icc (-t) (-s)) : ‖-e (-u)‖ ≤ C*‖Y (-u)‖ := by
    simpa only [norm_neg] using he (-u) (hmem u hu)
  have hh := spectralRemote_norm_growth (fun u => Y (-u)) (fun u => -e (-u))
    (fun u i => -omega (-u) i) (-t) (-s) C (by linarith) hC hd hb
  simpa only [neg_neg,neg_sub_neg] using hh

end DefocusingNLS

end OAI
