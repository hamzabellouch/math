import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningInwardSystem
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralBoundaryBound

namespace OAI

/-! The comparison data needed by the actual two-channel argument. -/

open Set Filter Topology
namespace DefocusingNLS

def SpectralTurningComparison {R E K : ℝ} (S : SpectralScalarBoundarySystem R E K)
    (J h b eta omega gamma d : ℝ) : Prop :=
  S.k = spectralTurningRegularizedWeight h b eta omega gamma d ∧
  S.V = (fun r => (homogeneousSpectralLocalizationFrequency h b eta omega r : ℂ)+
    Complex.I*(gamma : ℂ)) ∧
  S.beta = (h : ℂ)*Complex.I*(Real.sqrt
    (homogeneousSpectralLocalizationFrequency h b eta omega E) : ℂ) ∧
  (∀ z : ℂ, ∀ r ∈ Icc R E, spectralShellNorm (S.k r) (S.extension z r) ≤ J*S.k R*‖z‖) ∧
  ((S.U R).2/(S.U R).1).re ≤ -(1/24 : ℝ)*(S.k R)^2 ∧
  S.U E = spectralOscillatoryData h (Real.sqrt (Real.sqrt
    (homogeneousSpectralLocalizationFrequency h b eta omega E)))

theorem SpectralTurningComparison.withBound {R E K : ℝ}
    {S : SpectralScalarBoundarySystem R E K} {J h b eta omega gamma d : ℝ}
    (hs : SpectralTurningComparison S J h b eta omega gamma d)
    (K' J' : ℝ) (hK : K ≤ K') (hJ : J ≤ J') :
    SpectralTurningComparison (S.withBound K' hK) J' h b eta omega gamma d := by
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_,hs.2.2.2.2⟩
  intro z r hr
  exact (hs.2.2.2.1 z r hr).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hJ
      (S.positive_k R ⟨le_rfl,hr.1.trans hr.2⟩).le) (norm_nonneg _))

def SpectralTurningFamilyData (ell : ℕ → ℕ) (h : ℝ)
    (b omega gamma r₀ d E : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ b n ∧ b n ≤ 1 ∧
    |gamma n| ≤ 8 ∧ 2*r₀ n ≤ E n ∧
    (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n) ∧
    homogeneousSpectralLocalizationFrequency h (b n)
      ((ell n : ℝ)*(ell n+10)) (omega n) (r₀ n) = 0 ∧
    spectralLiouvilleSlope ((ell n : ℝ)*(ell n+10)) (r₀ n)*(d n)^3 = 1

theorem spectralTurning_comparisons
    (ell : ℕ → ℕ) (h : ℝ) (b omega gamma r₀ d E : ℕ → ℝ) (R : ℝ)
    (hh : h^2 = 1) (hR : 0 < R) (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : SpectralTurningFamilyData ell h b omega gamma r₀ d E) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ), StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop,
      ∃ S : SpectralScalarBoundarySystem R (E (φ n)) K,
        SpectralTurningComparison S J h (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) (d (φ n)) :=
  spectralTurning_inward_systems ell h b omega gamma r₀ d E R hh hR hr₀ hdata

theorem spectralTurning_paired_comparisons
    (ell : ℕ → ℕ) (b omega gamma rp rm dp dm E : ℕ → ℝ) (R : ℝ)
    (hR : 0 < R) (hrp : Tendsto rp atTop atTop) (hrm : Tendsto rm atTop atTop)
    (hp : SpectralTurningFamilyData ell 1 b omega gamma rp dp E)
    (hm : SpectralTurningFamilyData ell (-1) b omega (-gamma) rm dm E) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ), StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ ∀ᶠ n in atTop,
      ∃ Sp Sm : SpectralScalarBoundarySystem R (E (φ n)) K,
        SpectralTurningComparison Sp J 1 (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) (dp (φ n)) ∧
        SpectralTurningComparison Sm J (-1) (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (-gamma (φ n)) (dm (φ n)) := by
  obtain ⟨φ,Kp,Jp,hφ,hKp,hJp,hplus⟩ := spectralTurning_comparisons ell 1 b omega gamma rp dp E R
    (by norm_num) hR hrp hp
  obtain ⟨ψ,Km,Jm,hψ,hKm,hJm,hminus⟩ := spectralTurning_comparisons (ell ∘ φ) (-1)
    (b ∘ φ) (omega ∘ φ) ((-gamma) ∘ φ) (rm ∘ φ) (dm ∘ φ) (E ∘ φ) R
    (by norm_num) hR (hrm.comp hφ.tendsto_atTop) (hφ.tendsto_atTop.eventually hm)
  refine ⟨φ ∘ ψ,max Kp Km,max Jp Jm,hφ.comp hψ,hKp.trans (le_max_left _ _),
    hJp.trans (le_max_left _ _),?_⟩
  filter_upwards [hψ.tendsto_atTop.eventually hplus,hminus] with n hpn hmn
  obtain ⟨Sp,hsp⟩ := hpn
  obtain ⟨Sm,hsm⟩ := hmn
  exact ⟨Sp.withBound (max Kp Km) (le_max_left _ _),
    Sm.withBound (max Kp Km) (le_max_right _ _),
    hsp.withBound _ _ (le_max_left _ _) (le_max_left _ _),
    hsm.withBound _ _ (le_max_right _ _) (le_max_right _ _)⟩

end DefocusingNLS

end OAI
