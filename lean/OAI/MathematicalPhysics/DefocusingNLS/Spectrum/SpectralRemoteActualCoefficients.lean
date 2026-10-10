import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteLeadingSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteReconstruction
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIndividualSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogCoefficients

namespace OAI

/-! Individual symbols and endpoint formulas for the actual angular,
spectral and odd-power coefficients. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_leading_endpoint (omega eta : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    spectralRemoteLeadingCoefficient omega eta n t =
      spectralRemoteEndpointCoefficient (omega n) (eta n) (Real.exp t) := by
  have h4 : eta n/(Real.exp t)^4 = eta n*Real.exp (-4*t) := by
    rw [div_eq_mul_inv,← Real.exp_nat_mul,← Real.exp_neg]
    congr 1
    norm_num
  funext i
  fin_cases i <;>
    norm_num [spectralRemoteLeadingCoefficient,spectralRemoteEndpointCoefficient,
      spectralRemote_exp_inv_sq,h4]

theorem spectralRemote_leading_individual (omega eta : ℕ → ℝ) (n : ℕ) :
    HasLogJetBound 0 (spectralRemoteLeadingCoefficient omega eta n) := by
  let v : Fin 2 → ℝ := fun i => (if i = 0 then 1 else -1)*omega n
  let w : Fin 2 → ℝ := fun _ => eta n
  have hv := (HasLogJetBound.exponential (-2) v).mono (by norm_num : (-2 : ℝ) ≤ 0)
  have hw := (HasLogJetBound.exponential (-4) w).mono (by norm_num : (-4 : ℝ) ≤ 0)
  convert hv.add hw using 1
  funext t i
  simp only [spectralRemoteLeadingCoefficient,Pi.add_apply,Pi.smul_apply,smul_eq_mul,v,w]
  ring

theorem spectralRemote_physical_bounded_individual
    (a b sigma : ℝ) (D C : ℝ → ℂ) (hD : HasLogJetBound 0 D) (hC : HasLogJetBound 0 C) :
    HasLogJetBound 0 (fun t => spectralRemotePhysicalBounded a b sigma (D t) (C t)) := by
  have hL : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  let M := |a|+|b|+|sigma|
  have hM : 0 ≤ M := by positivity
  have ha : ∀ᶠ j : ℕ in atTop, |(fun _ : ℕ => a) j| ≤ M :=
    Eventually.of_forall (fun _ => by dsimp only [M]; linarith [abs_nonneg b,abs_nonneg sigma])
  have hb : ∀ᶠ j : ℕ in atTop, |(fun _ : ℕ => b) j| ≤ M :=
    Eventually.of_forall (fun _ => by dsimp only [M]; linarith [abs_nonneg a,abs_nonneg sigma])
  have hs : ∀ᶠ j : ℕ in atTop, |(fun _ : ℕ => sigma) j| ≤ M :=
    Eventually.of_forall (fun _ => by dsimp only [M]; linarith [abs_nonneg a,abs_nonneg b])
  exact (spectralRemote_physical_bounded_symbol hM ha hb hs
    (HasUniformLogJetBound.of_single hD hL) (HasUniformLogJetBound.of_single hC hL)).to_single

theorem spectralRemote_oddPower_individual
    (a b sigma tau : ℝ) (m : ℕ) (hm : 1 ≤ m) (htau : 2*(m : ℝ)*tau = -2)
    (Q : ℝ → ℂ) (hQ : HasLogJetBound tau Q) :
    HasLogJetBound 0 (fun t => spectralRemotePhysicalBounded a b sigma
      (spectralDiagonalCoefficient m (Q t)) (spectralCrossCoefficient m (Q t))) := by
  have hD : HasLogJetBound (-2) (fun t => spectralDiagonalCoefficient m (Q t)) := by
    simpa only [htau] using hQ.spectralDiagonal m
  have hC : HasLogJetBound (-2) (fun t => spectralCrossCoefficient m (Q t)) := by
    simpa only [htau] using hQ.spectralCross m hm
  exact spectralRemote_physical_bounded_individual a b sigma _ _
    (hD.mono (by norm_num)) (hC.mono (by norm_num))

end DefocusingNLS

end OAI
