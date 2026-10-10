import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMixedComparisons

namespace OAI

/-! The actual frequency-dominated geometry constructs the mixed pair;
no turning radius or Airy scale is assumed. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralCaseII_comparisons
    (ell : ℕ → ℕ) (b omega gamma E : ℕ → ℝ) (C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 < R) (hCR : 2*C ≤ R^2)
    (hw : Tendsto omega atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 ≤ b n ∧ b n ≤ 1 ∧ |gamma n| ≤ 8 ∧ 0 < E n ∧
      (ell n : ℝ)*(ell n+10)+99/4 ≤ C*omega n ∧
      (E n)^2 = 256*max ((ell n : ℝ)+1) (omega n)) :
    let dp := fun n => spectralTurningRootScale ((ell n : ℝ)*(ell n+10))
      (spectralTurningRoot 1 (b n) ((ell n : ℝ)*(ell n+10)) (omega n))
    ∃ (φ : ℕ → ℕ) (K J : ℝ) (kap eps : ℕ → ℝ),
      StrictMono φ ∧ 0 ≤ K ∧ 0 ≤ J ∧ Tendsto kap atTop atTop ∧
      (∀ n, 0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∃ Sp Sm : SpectralScalarBoundarySystem R (E (φ n)) K,
        SpectralTurningComparison Sp J 1 (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (gamma (φ n)) (dp (φ n)) ∧
        SpectralNoTurnComparison Sm J (eps n) (b (φ n)) ((ell (φ n) : ℝ)*(ell (φ n)+10))
          (omega (φ n)) (-gamma (φ n)) ∧
        (∀ r ∈ Icc R (E (φ n)), kap n ≤ Sp.k r) ∧
        (∀ r ∈ Icc R (E (φ n)), kap n ≤ Sm.k r) := by
  obtain ⟨hrp,hdp,hdpp,hp⟩ := spectralTurningRoot_caseII_data ell b omega gamma E hw (by
    filter_upwards [hdata,hw.eventually (eventually_ge_atTop 0)] with n hn hwn
    exact ⟨hn.1,hn.2.1,hwn,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.2⟩)
  exact spectralMixed_comparisons ell b omega gamma _ _ E C R hC hR hCR hw hrp hdp hdpp hp
    (hdata.mono (fun _ hn => ⟨hn.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2⟩))

end DefocusingNLS

end OAI
