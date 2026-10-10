import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnBoundarySystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnSlopeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundaryBound

namespace OAI

/-! The actual no-turn Green system and its outgoing slope are selected
together. The normalized slope error tends to zero. -/

open Set Filter Topology
namespace DefocusingNLS

def SpectralNoTurnComparison {R E K : ℝ} (S : SpectralScalarBoundarySystem R E K)
    (J eps b eta omega gamma : ℝ) : Prop :=
  S.k = (fun r => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) b eta omega gamma r‖) ∧
  S.V = (fun r => (homogeneousSpectralLocalizationFrequency (-1) b eta omega r : ℂ)+
    Complex.I*(gamma : ℂ)) ∧
  S.beta = -Complex.I*(Real.sqrt
    (homogeneousSpectralLocalizationFrequency (-1) b eta omega E) : ℂ) ∧
  (∀ z : ℂ, ∀ r ∈ Icc R E, spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k R*‖z‖) ∧
  ‖((S.U R).2/(S.U R).1)/(Real.sqrt
    (homogeneousSpectralLocalizationFrequency (-1) b eta omega R) : ℂ)+Complex.I‖ ≤ eps

theorem SpectralNoTurnComparison.withBound {R E K : ℝ}
    {S : SpectralScalarBoundarySystem R E K} {J eps b eta omega gamma : ℝ}
    (hs : SpectralNoTurnComparison S J eps b eta omega gamma)
    (K' J' : ℝ) (hK : K ≤ K') (hJ : J ≤ J') :
    SpectralNoTurnComparison (S.withBound K' hK) J' eps b eta omega gamma := by
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro z r hr
  exact (hs.2.2.2.1 z r hr).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hJ
      (S.positive_k R ⟨le_rfl,hr.1.trans hr.2⟩).le) (norm_nonneg _))

theorem spectralNoTurn_comparisons
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ (K J : ℝ) (eps : ℕ → ℝ), 0 ≤ K ∧ 0 ≤ J ∧
      (∀ n, 0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∃ S : SpectralScalarBoundarySystem R (E n) K,
        SpectralNoTurnComparison S J (eps n) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) := by
  classical
  obtain ⟨K,J,hK,hJ,hsys⟩ := spectralNoTurn_boundary_systems ell b omega gamma E C R hC hR hCR hw hdata
  let P := fun n (S : SpectralScalarBoundarySystem R (E n) K) =>
    S.k = (fun r => Real.sqrt ‖spectralLiouvilleMomentum 1 (-1) (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) (gamma n) r‖) ∧
    S.V = (fun r => (homogeneousSpectralLocalizationFrequency (-1) (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) r : ℂ)+Complex.I*(gamma n : ℂ)) ∧
    S.beta = -Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1)
      (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)) : ℂ) ∧
    S.U (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
      (homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
    ∀ z : ℂ, ∀ r ∈ Icc R (E n), spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k R*‖z‖
  let q := fun n => if hn : ∃ S, P n S then (Classical.choose hn).U else fun _ => (0,0)
  have hchoose : ∀ᶠ n in atTop, ∃ S, P n S ∧ q n = S.U := by
    filter_upwards [hsys] with n hn
    change ∃ S, P n S at hn
    exact ⟨Classical.choose hn,Classical.choose_spec hn,by simp only [q,dite_eq_left hn]⟩
  have hq : ∀ᶠ n in atTop, ContinuousOn (q n) (Icc R (E n)) ∧
      q n (E n) = spectralOscillatoryData (-1) (Real.sqrt (Real.sqrt
        (homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) (E n)))) ∧
      ∀ r ∈ Ioo R (E n), HasDerivAt (q n) (spectralScalarField
        ((homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) r : ℂ)+
          Complex.I*(gamma n : ℂ)) (q n r)) r := by
    filter_upwards [hchoose] with n hn
    obtain ⟨S,hS,hqS⟩ := hn
    rw [hqS]
    refine ⟨S.continuous_U,hS.2.2.2.1,?_⟩
    intro r hr
    simpa only [hS.2.1] using S.ode_U r ⟨hr.1.le,hr.2.le⟩
  have hlim := (spectralNoTurn_outgoing_slope_limit ell b omega gamma E C R hC hR hCR hw hdata q hq).2
  let eps := fun n => ‖((q n R).2/(q n R).1)/(Real.sqrt
    (homogeneousSpectralLocalizationFrequency (-1) (b n) ((ell n : ℝ)*(ell n+10)) (omega n) R) : ℂ)+Complex.I‖
  have heps : Tendsto eps atTop (𝓝 0) := by
    simpa only [neg_add_cancel,norm_zero] using (hlim.add_const Complex.I).norm
  refine ⟨K,J,eps,hK,hJ,fun n => norm_nonneg _,heps,?_⟩
  filter_upwards [hchoose] with n hn
  obtain ⟨S,hS,hqS⟩ := hn
  refine ⟨S,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.2,?_⟩
  dsimp only [eps]
  rw [hqS]

end DefocusingNLS

end OAI
