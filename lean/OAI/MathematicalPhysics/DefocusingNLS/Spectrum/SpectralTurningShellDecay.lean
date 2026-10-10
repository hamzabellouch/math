import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralForbiddenDecay
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleNormPositive

namespace OAI

/-! The normalized turning comparison decays exponentially across any
fixed exterior shell in the frequency-dominated case. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralScalarMomentum_ratio (u : ℂ × ℂ) :
    spectralScalarMomentum u = (u.2/u.1).re*spectralScalarMass u := by
  by_cases hu : u.1 = 0
  · simp only [spectralScalarMomentum,spectralScalarMass,hu,star_zero,zero_mul,Complex.zero_re,
      Complex.normSq_zero,mul_zero]
  have hu : u.1 ≠ 0 := hu
  have hid (x y : ℂ) : (star x*(y*x)).re = y.re*Complex.normSq x := by
    simp only [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.conj_re,
      Complex.conj_im,Complex.normSq_apply]
    ring
  have he := hid u.1 (u.2/u.1)
  rw [div_mul_cancel₀ _ hu] at he
  exact he

theorem SpectralScalarBoundarySystem.extension_mass_bound {R E K : ℝ}
    (S : SpectralScalarBoundarySystem R E K) (B A : ℝ)
    (hbound : spectralScalarMass (S.U B) ≤ A*spectralScalarMass (S.U R)) (z : ℂ) :
    ‖(S.extension z B).1‖^2 ≤ A*‖z‖^2 := by
  have hn : ‖(S.U R).1‖ ≠ 0 := norm_ne_zero_iff.mpr S.left_U
  have hscale : ‖z/(S.U R).1‖^2*spectralScalarMass (S.U R) = ‖z‖^2 := by
    rw [spectralScalarMass,← Complex.sq_norm,norm_div]
    field_simp
  have he := mul_le_mul_of_nonneg_left hbound (sq_nonneg ‖z/(S.U R).1‖)
  change ‖(z/(S.U R).1)*(S.U B).1‖^2 ≤ _
  rw [norm_mul,mul_pow,Complex.sq_norm (S.U B).1]
  change ‖z/(S.U R).1‖^2*spectralScalarMass (S.U B) ≤ _
  calc
    _ ≤ ‖z/(S.U R).1‖^2*(A*spectralScalarMass (S.U R)) := he
    _ = A*‖z‖^2 := by rw [← mul_left_comm A,hscale]

theorem spectralTurning_comparison_shell_decay
    (ell : ℕ → ℕ) (b omega gamma r₀ d E : ℕ → ℝ) (R B : ℝ)
    (hR : 0 < R) (hRB : R ≤ B) (hw : Tendsto omega atTop atTop)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : SpectralTurningFamilyData ell 1 b omega gamma r₀ d E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop,
      ∀ K J : ℝ, ∀ S : SpectralScalarBoundarySystem R (E (φ n)) K,
      SpectralTurningComparison S J 1 (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
        (omega (φ n)) (gamma (φ n)) (d (φ n)) →
      spectralScalarMass (S.U B) ≤
        Real.exp (-(Real.sqrt (omega (φ n)/2)/24)*(B-R))*spectralScalarMass (S.U R) := by
  have hB : 0 < B := hR.trans_le hRB
  obtain ⟨φ,hφ,hin⟩ := spectralTurning_normalized_inward ell 1 b omega gamma r₀ d E B
    (by norm_num) hB hr₀ hdata
  refine ⟨φ,hφ,?_⟩
  filter_upwards [hin,hφ.tendsto_atTop.eventually hdata,
    (hw.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop (2*(B^2/16+1))),
    (hr₀.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop B)] with n hinn hdn hwn hrn
  dsimp only [Function.comp_def] at hwn hrn
  intro K J S hS
  have hw0 : 0 < omega (φ n) := by nlinarith [sq_nonneg B]
  have hBE : B ≤ E (φ n) := by
    change B ≤ r₀ (φ n) at hrn
    linarith [hdn.2.2.2.2.2.1]
  have hsub : Icc B (E (φ n)) ⊆ Icc R (E (φ n)) := Icc_subset_Icc hRB le_rfl
  have hi := hinn S.U (S.continuous_U.mono hsub)
    (fun r hr => by simpa only [hS.2.1] using S.ode_U r (hsub hr)) hS.2.2.2.2.2
  let F := homogeneousSpectralLocalizationFrequency 1 (b (φ n))
    ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n))
  have hF : ∀ r ∈ Icc R B, F r ≤ -omega (φ n)/2 := by
    intro r hr
    have hr0 : 0 < r := hR.trans_le hr.1
    have hr2 := pow_le_pow_left₀ hr0.le hr.2 2
    have hpot : 0 ≤ ((ell (φ n) : ℝ)*(ell (φ n)+10)+99/4)/r^2 := by positivity
    dsimp only [F,homogeneousSpectralLocalizationFrequency]
    nlinarith [hdn.2.2.2.1]
  have hFB := hF B ⟨hRB,le_rfl⟩
  have hp : Real.sqrt (omega (φ n)/2) ≤
      ‖spectralLiouvilleMomentum (-1) 1 (b (φ n))
        ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (gamma (φ n)) B‖ := by
    apply (Real.sqrt_le_sqrt (show omega (φ n)/2 ≤ |F B| from by
      rw [abs_of_nonpos (hFB.trans (by linarith))]; linarith)).trans
    exact spectralWKBSqrt_frequency_lower (-1) (F B) (gamma (φ n)) (by norm_num)
  let mu := Real.sqrt (omega (φ n)/2)/24
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hslope : ((S.U B).2/(S.U B).1).re ≤ -mu := by
    dsimp only [mu]
    linarith
  apply spectralForbidden_mass_decay R B mu hRB hmu S.U S.V
    (S.continuous_U.mono (Icc_subset_Icc le_rfl hBE))
    (fun r hr => S.ode_U r ⟨hr.1.le,hr.2.le.trans hBE⟩)
  · intro r hr
    have hf := hF r ⟨hr.1.le,hr.2.le⟩
    have hs := Real.sq_sqrt (show 0 ≤ omega (φ n)/2 by positivity)
    rw [hS.2.1]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero]
    dsimp only [mu]
    nlinarith
  · rw [spectralScalarMomentum_ratio (S.U B)]
    have hm := mul_le_mul_of_nonneg_right hslope (Complex.normSq_nonneg (S.U B).1)
    change 2*(((S.U B).2/(S.U B).1).re*spectralScalarMass (S.U B))+
      mu*spectralScalarMass (S.U B) ≤ 0
    have hmass : 0 ≤ spectralScalarMass (S.U B) := Complex.normSq_nonneg _
    nlinarith

end DefocusingNLS

end OAI
