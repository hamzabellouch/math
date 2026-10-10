import OAI.Probability.InvariantIsing.Gaussian.MPClippedTransform

namespace OAI

/-! Weak convergence in probability of the actual Gaussian empirical law after clipping. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace InvariantIsing

theorem gaussianPattern_clipped_weak {α : ℝ} (hα : 0 < α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    TendstoInMeasure P (fun k ω => LevyProkhorov.ofMeasure
      ((empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω))).map
        (spectralClip 0 (marchenkoPasturB α)))) atTop
      (fun _ => LevyProkhorov.ofMeasure (⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩ : ProbabilityMeasure ℝ)) := by
  let R := marchenkoPasturB α
  have hR : 0 ≤ R := sq_nonneg _
  let ν : ProbabilityMeasure ℝ := ⟨marchenkoPasturMeasure α,marchenkoPastur_probability hα⟩
  let W := fun k ω => compactClippedLaw R hR
    (empiricalSpectralLaw (Nat.succ_pos k) (gaussianPatternEigenvalues (Z (k+1) ω)))
  have hh : ∀ t : {t : ℝ // 0 < t}, TendstoInMeasure P
      (fun k ω => ∫ x, compactResolventTest R t x ∂(W k ω : Measure _)) atTop
      (fun _ => ∫ x, compactResolventTest R t x ∂(compactClippedLaw R hR ν : Measure _)) := by
    intro t
    simp only [W,compactClippedLaw_integral]
    change TendstoInMeasure P _ atTop (fun _ => ∫ x,
      positiveResolventTest t (spectralClip 0 (marchenkoPasturB α) x) ∂marchenkoPasturMeasure α)
    rw [marchenkoPastur_clipped_transform hα t.property]
    exact gaussianPattern_clipped_stieltjes hα t.property P Z hZ
  have hc := compact_resolvent_tendstoInMeasure R P W (compactClippedLaw R hR ν) hh
  have hn : (compactClippedLaw R hR ν).map (fun x => (x : ℝ)) = ν :=
    compactClippedLaw_real_eq R hR ν (marchenkoPastur_mem_nonnegative_interval hα)
  rw [hn] at hc
  simpa only [W,compactClippedLaw_real] using hc

end InvariantIsing

end

end OAI
