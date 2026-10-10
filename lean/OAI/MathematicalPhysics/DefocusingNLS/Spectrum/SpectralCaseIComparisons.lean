import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCaseIData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningPairWeight

namespace OAI

/-! Both channels have inward comparisons with a common diverging weight
floor when angular degree dominates the imaginary spectral parameter. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralCaseI_comparisons
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (R : ℝ) (hR : 0 < R)
    (hescape : Tendsto (fun n => ((ell n : ℝ)*(ell n+10))/(1+omega n)) atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ b n ≤ 1 ∧ 0 ≤ omega n ∧
      |gamma n| ≤ 8 ∧ 0 < E n ∧ (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ) (kap : ℕ → ℝ),
      StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ Tendsto kap atTop atTop ∧
      ∀ᶠ n in atTop,
        (∀ r ∈ Ioc 0 R,
          homogeneousSpectralLocalizationFrequency 1 (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r ≤ 0 ∧
          homogeneousSpectralLocalizationFrequency (-1) (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r ≤ 0) ∧
        ∃ Sp Sm : SpectralScalarBoundarySystem R (E (φ n)) K,
          Sp.V = (fun r => (homogeneousSpectralLocalizationFrequency 1 (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*(gamma (φ n) : ℂ)) ∧
          Sm.V = (fun r => (homogeneousSpectralLocalizationFrequency (-1) (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) r : ℂ)+Complex.I*((-gamma (φ n)) : ℂ)) ∧
          Sp.beta = Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency 1 (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))) : ℂ) ∧
          Sm.beta = -Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency (-1) (b (φ n))
            ((ell (φ n) : ℝ)*(ell (φ n)+10)) (omega (φ n)) (E (φ n))) : ℂ) ∧
          (∀ r ∈ Icc R (E (φ n)), kap n ≤ Sp.k r) ∧
          (∀ r ∈ Icc R (E (φ n)), kap n ≤ Sm.k r) ∧
          (∀ z : ℂ, ∀ r ∈ Icc R (E (φ n)),
            spectralShellNorm (Sp.k r) (Sp.extension z r) ≤ J*Sp.k R*‖z‖) ∧
          (∀ z : ℂ, ∀ r ∈ Icc R (E (φ n)),
            spectralShellNorm (Sm.k r) (Sm.extension z r) ≤ J*Sm.k R*‖z‖) ∧
          ((Sp.U R).2/(Sp.U R).1).re ≤ -(1/24 : ℝ)*(Sp.k R)^2 ∧
          ((Sm.U R).2/(Sm.U R).1).re ≤ -(1/24 : ℝ)*(Sm.k R)^2 := by
  let eta := fun n => (ell n : ℝ)*(ell n+10)
  let rp := fun n => spectralTurningRoot 1 (b n) (eta n) (omega n)
  let rm := fun n => spectralTurningRoot (-1) (b n) (eta n) (omega n)
  let dp := fun n => spectralTurningRootScale (eta n) (rp n)
  let dm := fun n => spectralTurningRootScale (eta n) (rm n)
  obtain ⟨hrp,hdp,hdpp,hpd⟩ := spectralTurningRoot_caseI_data ell 1 b omega gamma E
    (by norm_num) hescape hdata
  obtain ⟨hrm,hdm,hdmp,hmd⟩ := spectralTurningRoot_caseI_data ell (-1) b omega (-gamma) E
    (by norm_num) hescape (by simpa only [Pi.neg_apply,abs_neg] using hdata)
  obtain ⟨φ,K,J,hφ,hK,hJ,hpair⟩ := spectralTurning_paired_comparisons ell b omega gamma
    rp rm dp dm E R hR hrp hrm hpd hmd
  let kap := fun n => (Real.sqrt (dp (φ n)+dm (φ n)))⁻¹
  have hkap : Tendsto kap atTop atTop :=
    (spectralTurning_pair_floor_tendsto dp dm hdp hdm
      (Eventually.of_forall hdpp) (Eventually.of_forall hdmp)).comp hφ.tendsto_atTop
  refine ⟨φ,K,J,kap,hφ,hK,hJ,hkap,?_⟩
  filter_upwards [hpair,(hrp.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop R),
    (hrm.comp hφ.tendsto_atTop).eventually (eventually_ge_atTop R)] with n hn hRp hRm
  obtain ⟨Sp,Sm,hsp,hsm⟩ := hn
  have hfloor := spectralTurning_pair_floor (dp (φ n)) (dm (φ n)) (hdpp _) (hdmp _)
  refine ⟨?_,Sp,Sm,hsp.2.1,?_,?_,?_,?_,?_,hsp.2.2.2.1,hsm.2.2.2.1,
    hsp.2.2.2.2.1,hsm.2.2.2.2.1⟩
  · intro r hr
    have heta : 0 ≤ eta (φ n) := by dsimp only [eta]; positivity
    constructor
    · have hz := spectralTurningRoot_data 1 (b (φ n)) (eta (φ n)) (omega (φ n)) heta
      exact ((homogeneousSpectralLocalizationFrequency_strictMono 1 (b (φ n)) (eta (φ n))
        (omega (φ n)) heta).monotoneOn hr.1 hz.1 (hr.2.trans hRp)).trans_eq hz.2
    · have hz := spectralTurningRoot_data (-1) (b (φ n)) (eta (φ n)) (omega (φ n)) heta
      exact ((homogeneousSpectralLocalizationFrequency_strictMono (-1) (b (φ n)) (eta (φ n))
        (omega (φ n)) heta).monotoneOn hr.1 hz.1 (hr.2.trans hRm)).trans_eq hz.2
  · simpa only [Complex.ofReal_neg] using hsm.2.1
  · simpa only [Complex.ofReal_one,one_mul] using hsp.2.2.1
  · simpa only [Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using hsm.2.2.1
  · intro r _
    rw [hsp.1]
    exact hfloor.1.trans (spectralTurning_weight_floor _ _ _ _ _ _ _)
  · intro r _
    rw [hsm.1]
    exact hfloor.2.trans (spectralTurning_weight_floor _ _ _ _ _ _ _)

end DefocusingNLS

end OAI
