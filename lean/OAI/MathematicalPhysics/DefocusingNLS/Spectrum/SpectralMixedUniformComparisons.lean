import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralUniformComparisons
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningCaseIIData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnComparison
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnWeight
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningWeightEscape

namespace OAI

/-! A common Green bound and diverging weight floor for the mixed
turning/no-turn exterior problem. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralMixed_uniform_comparisons
    (ell : ℕ → ℕ) (b omega gamma rp dp E : ℕ → ℝ) (C R B : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hRB : R ≤ B) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop) (hrp : Tendsto rp atTop atTop)
    (hdp : Tendsto dp atTop (𝓝 0)) (hdpp : ∀ n, 0 < dp n)
    (hp : SpectralTurningFamilyData ell 1 b omega gamma rp dp E)
    (hm : ∀ᶠ n in atTop, 0 ≤ b n ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    ∃ (φ : ℕ → ℕ) (K J : ℝ) (kap eps : ℕ → ℝ),
      StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ Tendsto kap atTop atTop ∧
      (∀ n, 0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ L ∈ Icc R B,
      ∃ Sp Sm : SpectralScalarBoundarySystem L (E (φ n)) K,
        SpectralTurningComparison Sp J 1 (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) (dp (φ n)) ∧
        SpectralNoTurnComparison Sm J (eps n) (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (-gamma (φ n)) ∧
        (∀ r ∈ Icc L (E (φ n)), kap n ≤ Sp.k r) ∧
        (∀ r ∈ Icc L (E (φ n)), kap n ≤ Sm.k r) := by
  obtain ⟨φ,Kp,Jp,hφ,hKp,hJp,hplus⟩ := spectralTurning_uniform_comparisons ell 1 b omega gamma
    rp dp E R B (by norm_num) hR hRB hrp hp
  obtain ⟨Km,Jm,eps,hKm,hJm,heps,heps0,hminus⟩ := spectralNoTurn_uniform_comparisons (ell ∘ φ)
    (b ∘ φ) (omega ∘ φ) ((-gamma) ∘ φ) (E ∘ φ) C R B hC hR hRB hCR
    (hw.comp hφ.tendsto_atTop) (by
      simpa only [Function.comp_def,Pi.neg_apply,abs_neg] using hφ.tendsto_atTop.eventually hm)
  let kap := fun n => min ((Real.sqrt (dp (φ n)))⁻¹) (Real.sqrt (Real.sqrt (omega (φ n)/2)))
  have hkap : Tendsto kap atTop atTop := spectralCommonWeight_tendsto _ _
    ((spectralTurning_weight_floor_tendsto dp hdp (Eventually.of_forall hdpp)).comp hφ.tendsto_atTop)
    ((spectralNoTurn_weight_floor_tendsto omega hw).comp hφ.tendsto_atTop)
  refine ⟨φ,max Kp Km,max Jp Jm,kap,eps,hφ,hKp.trans (le_max_left _ _),
    hJp.trans (le_max_left _ _),hkap,heps,heps0,?_⟩
  filter_upwards [hplus,hminus,hφ.tendsto_atTop.eventually hm,
    (hw.comp hφ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with n hpn hmn hdn hwn
  intro L hL
  obtain ⟨Sp,hsp⟩ := hpn L hL
  obtain ⟨Sm,hsm⟩ := hmn L hL
  refine ⟨Sp.withBound _ (le_max_left _ _),Sm.withBound _ (le_max_right _ _),
    hsp.withBound _ _ (le_max_left _ _) (le_max_left _ _),
    hsm.withBound _ _ (le_max_right _ _) (le_max_right _ _),?_,?_⟩
  · intro r _
    change kap n ≤ Sp.k r
    rw [hsp.1]
    exact (min_le_left _ _).trans (spectralTurning_weight_floor _ _ _ _ _ _ _)
  · intro r hr
    change kap n ≤ Sm.k r
    rw [hsm.1]
    exact (min_le_right _ _).trans (spectralNoTurn_weight_lower _ _ _ _ C R r hdn.1 hwn
      hR (hL.1.trans hr.1) hdn.2.2.2.1 hCR)

end DefocusingNLS

end OAI
