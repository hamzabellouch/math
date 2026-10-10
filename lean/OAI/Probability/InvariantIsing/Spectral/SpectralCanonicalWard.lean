import OAI.Probability.InvariantIsing.Spectral.SpectralWardSymbols
import OAI.Probability.InvariantIsing.Spectral.SpectralQuantileSynchronization
import OAI.Probability.InvariantIsing.Arrays.PathSymbolCongruence

namespace OAI

/-! Both limiting Ward identities act on the canonical group quantiles,
independently of the synchronized factors chosen for a pair of groups. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

 theorem spectralCanonicalWard_pair {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (a b : Fin m)
    (hoff : ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : spectralDiagonalWardResidual Q ρ eig a b = 0) :
    let A := spectralGroupQuantilePath Q hn a
    let B := spectralGroupQuantilePath Q hn b
    (∀ᵐ s ∂pathMeasure, ρ b * pathSymbol (q a.castSucc) A s -
      ρ a * pathSymbol (q b.castSucc) B s =
      (eig a - eig b) * pathSymbol (q a.castSucc) A s * pathSymbol (q b.castSucc) B s) ∧
    (ρ b * Function.rightLim A.val 0 - ρ a * Function.rightLim B.val 0 =
      (eig a - eig b) *
        ((q a.castSucc - ∫ u in 0..1, A u) * Function.rightLim B.val 0 +
          Function.rightLim A.val 0 * (q b.castSucc - ∫ u in 0..1, B u))) := by
  intro A B
  obtain ⟨f, g, hf, hg, hfb, hgb, hfa, hga, hw⟩ :=
    spectralPartition_offWardPath hgg hG q hq hd hE hP hn ρ eig a b hoff
  have hfa01 : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1) := by
    filter_upwards [hfa] with x hx
    exact hx 0 1 (by omega)
  have hga01 : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) b.castSucc : ℝ) = g (spectralSpinArray x 0 1) := by
    filter_upwards [hga] with x hx
    exact hx 0 1 (by omega)
  have hEperm := fun e : Equiv.Perm ℕ => hE e e.injective
  have hAf := spectralGroupQuantilePath_eq_factor hgg hG q hq hd hEperm hP hn a f hf.continuous hfa01
  have hBg := spectralGroupQuantilePath_eq_factor hgg hG q hq hd hEperm hP hn b g hg.continuous hga01
  obtain ⟨hsymbol, hroot⟩ := spectralSynchronizedWard_symbols Q hP hn q hd ρ eig a b
    f g hf hg hfb hgb hfa01 hga01 hdiag hw
  refine ⟨?_, ?_⟩
  · filter_upwards [hsymbol, pathSymbol_congr_ae (q a.castSucc) hAf,
      pathSymbol_congr_ae (q b.castSucc) hBg] with s hs ha hb
    rw [ha, hb]
    exact hs
  · have hAr := synchronized_quantile_root f hf.continuous hAf
    have hBr := synchronized_quantile_root g hg.continuous hBg
    rw [hAr, hBr, intervalIntegral_congr_path_ae hAf le_rfl le_rfl zero_le_one,
      intervalIntegral_congr_path_ae hBg le_rfl le_rfl zero_le_one]
    exact hroot

end InvariantIsing

end

end OAI
