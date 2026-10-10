import OAI.Probability.InvariantIsing.Spectral.SpectralBoundedSynchronization
import OAI.Probability.InvariantIsing.Arrays.QuantileReplicaProduct

namespace OAI

/-! Replica products for the actual simultaneous spectral GG limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

def spectralSpinQuantilePath {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    OverlapPath :=
  spectralQuantilePath Q (spectralSpinWeight m)
    (by simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn)

lemma spectralSpinQuantilePath_law {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    pathMeasure.map (spectralSpinQuantilePath Q hP hn) =
      scalarOverlapLaw (Q : Measure (SpectralArray (m + 1))) spectralSpinArray := by
  have he := spectralQuantilePath_law Q (spectralSpinWeight m)
    (by simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn)
  simpa only [spectralSpinQuantilePath, spectralLinearLaw, scalarOverlapLaw,
    spectralLinearArray_spinWeight] using he

/-- The actual spectral overlap product is represented by the manuscript
product path under a single total-overlap quantile. -/
theorem spectralPartition_replicaProductPath {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a b : Fin m) :
    ∃ f g : ℝ → ℝ, LipschitzWith 1 f ∧ LipschitzWith 1 g ∧
      (∀ r, f r ∈ Icc (0 : ℝ) 1) ∧ (∀ r, g r ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) a.castSucc : ℝ) = f (spectralSpinArray x i j)) ∧
      (∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) b.castSucc : ℝ) = g (spectralSpinArray x i j)) ∧
      ∀ (Φ : ℝ → ℝ), Measurable Φ → ∀ (C : ℝ), 0 ≤ C → (∀ r, |Φ r| ≤ C) →
        (∫ x, Φ (spectralSpinArray x 0 1) *
          (q a.castSucc * (x (0,1) b.castSucc : ℝ) +
            (x (0,1) a.castSucc : ℝ) * q b.castSucc -
            2 * ((x (0,2) a.castSucc : ℝ) * (x (1,2) b.castSucc : ℝ)))
          ∂(Q : Measure (SpectralArray (m + 1)))) =
        ∫ s, Φ (spectralSpinQuantilePath Q hP hn s) *
          replicaProductPath (q a.castSucc) (fun u => f (spectralSpinQuantilePath Q hP hn u))
            (q b.castSucc) (fun u => g (spectralSpinQuantilePath Q hP hn u)) s ∂pathMeasure := by
  obtain ⟨f, hf, hfb, hfa⟩ := spectralPartition_bounded_synchronization hgg hG q hq hd hE hP hn a
  obtain ⟨g, hg, hgb, hga⟩ := spectralPartition_bounded_synchronization hgg hG q hq hd hE hP hn b
  refine ⟨f, g, hf, hg, hfb, hgb, hfa, hga, ?_⟩
  intro Φ hΦ C hC hΦB
  have hRs : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      ∀ i j, spectralSpinArray x i j = spectralSpinArray x j i := by
    filter_upwards [hG, hd] with x hx hdx
    simpa only [spectralLinearArray_spinWeight] using
      (spectralGram_linear hx q (spectralSpinWeight m) hdx (spectralSpinWeight_nonneg m)).symm
  have hRgg : HasEntryGhirlandaGuerra spectralSpinArray (Q : Measure (SpectralArray (m + 1))) := by
    have he := hgg.map (continuous_spectralLinearEntry (spectralSpinWeight m)).measurable
    change HasEntryGhirlandaGuerra (spectralLinearArray (spectralSpinWeight m))
      (Q : Measure (SpectralArray (m + 1))) at he
    have heq : spectralLinearArray (spectralSpinWeight m) =
        (spectralSpinArray : SpectralArray (m + 1) → RealArray) :=
      funext spectralLinearArray_spinWeight
    rw [heq] at he
    exact he
  have hRu : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), IsUltrametricArray (spectralSpinArray x) := by
    simpa only [spectralLinearArray_spinWeight] using spectralGG_linear_ultrametric
      hgg hG q hq hd (fun e => hE e e.injective) (spectralSpinWeight m) (spectralSpinWeight_nonneg m)
  have hR : Measurable (spectralSpinArray : SpectralArray (m + 1) → RealArray) := by
    unfold spectralSpinArray
    fun_prop
  have habs (r : ℝ) : |f r| ≤ 1 := by rw [abs_of_nonneg (hfb r).1]; exact (hfb r).2
  have hgabs (r : ℝ) : |g r| ≤ 1 := by rw [abs_of_nonneg (hgb r).1]; exact (hgb r).2
  calc
    _ = ∫ x, Φ (spectralSpinArray x 0 1) *
        (q a.castSucc * g (spectralSpinArray x 0 1) +
          f (spectralSpinArray x 0 1) * q b.castSucc -
          2 * (f (spectralSpinArray x 0 2) * g (spectralSpinArray x 1 2)))
        ∂(Q : Measure (SpectralArray (m + 1))) := by
      apply integral_congr_ae
      filter_upwards [hfa, hga] with x hx hy
      rw [hx 0 1 (by omega), hy 0 1 (by omega), hx 0 2 (by omega), hy 1 2 (by omega)]
    _ = _ := gg_replicaProductPath_integral (Q : Measure (SpectralArray (m + 1)))
      spectralSpinArray hR hRgg hRs hRu (spectralSpinQuantilePath Q hP hn)
      (spectralSpinQuantilePath_law Q hP hn) f g Φ hf.continuous.measurable
      hg.continuous.measurable hΦ zero_le_one zero_le_one hC habs hgabs hΦB
      (q a.castSucc) (q b.castSucc)

end InvariantIsing

end

end OAI
