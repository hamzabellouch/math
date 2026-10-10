import OAI.Probability.InvariantIsing.Spectral.SpectralReplicaProduct
import OAI.Probability.InvariantIsing.Arrays.PathSymbolAEUniqueness

namespace OAI

/-! Every continuous synchronized coordinate agrees with its canonical
group quantile under the same total quantile, including atoms. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def spectralGroupQuantilePath {m : ℕ} (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a : Fin m) : OverlapPath :=
  spectralQuantilePath Q (Pi.single a.castSucc 1) (spectralCoordinate_unit hn a.castSucc)

 theorem spectralGroupQuantilePath_eq_factor {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a : Fin m) (f : ℝ → ℝ) (hf : Continuous f)
    (hfa : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1)) :
    ∀ᵐ s ∂pathMeasure, spectralGroupQuantilePath Q hn a s = f (spectralSpinQuantilePath Q hP hn s) := by
  classical
  have hsingle : ∀ b, 0 ≤ (Pi.single a.castSucc 1 : Fin (m + 1) → ℝ) b := by
    intro b
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hp : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (spectralSpinWeight m) x 0 1 ∈ Icc (0 : ℝ) 1 := by
    simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn
  have hpair := spectralQuantilePath_pair_law hgg hG q hq hd hE
    (spectralSpinWeight m) (Pi.single a.castSucc 1) (spectralSpinWeight_nonneg m) hsingle hp
    (spectralCoordinate_unit hn a.castSucc)
  have he := factor_of_pair_law (Q : Measure (SpectralArray (m + 1))) pathMeasure
    (fun x => spectralLinearArray (spectralSpinWeight m) x 0 1)
    (fun x => spectralLinearArray (Pi.single a.castSucc 1) x 0 1)
    (spectralQuantilePath Q (spectralSpinWeight m) hp)
    (spectralGroupQuantilePath Q hn a)
    (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
    (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
    (spectralQuantilePath Q (spectralSpinWeight m) hp).measurable
    (spectralGroupQuantilePath Q hn a).measurable hpair.symm f hf
    (by simpa only [spectralLinearArray_spinWeight, spectralLinearArray_single, spectralCoordinateArray] using hfa)
  exact he

lemma synchronized_quantile_root {p a : OverlapPath} (f : ℝ → ℝ) (hf : Continuous f)
    (he : ∀ᵐ s ∂pathMeasure, a s = f (p s)) :
    Function.rightLim a.val 0 = f (Function.rightLim p.val 0) := by
  have hz : ∀ᵐ s ∂pathMeasure, a s - f (p s) = 0 := by
    filter_upwards [he] with s hs
    rw [hs, sub_self]
  have ht := (a.monotone.tendsto_rightLim 0).sub
    (hf.continuousAt.tendsto.comp (p.monotone.tendsto_rightLim 0))
  have hh := ae_constant_right_root hz ht
  linarith

end InvariantIsing

end

end OAI
