import OAI.Probability.RadialTransition.ConvolutionIntegral

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
section Fock
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma particleBase_convolution {F G : Multiset X → ℝ≥0∞}
    (hF : MeasurableConfiguration F) (hG : MeasurableConfiguration G)
    (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, clusterConvolution F G (particleMultiset x) ∂particleBase μ z) =
      (∫⁻ x, F (particleMultiset x) ∂particleBase μ z)*
      (∫⁻ x, G (particleMultiset x) ∂particleBase μ z) := by
  classical
  have hmF := measurable_particleObservable F hF 0
  have hmG := measurable_particleObservable G hG 0
  have hmC := measurable_particleObservable _ (measurable_clusterConvolution hF hG) 0
  simp only [zero_add] at hmF hmG hmC
  rw [lintegral_particleBase μ z hmC, lintegral_particleBase μ z hmF,
    lintegral_particleBase μ z hmG]
  let A (n : ℕ) := ∫⁻ x : Fin n → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ)
  let B (n : ℕ) := ∫⁻ x : Fin n → X, G (configurationMultiset x) ∂Measure.pi (fun _ => μ)
  have hN (N : ℕ) :
      (∫⁻ x : Fin N → X, clusterConvolution F G (configurationMultiset x) ∂Measure.pi (fun _ => μ)) =
        ∑ k ∈ Finset.range (N+1), (N.choose k : ℝ≥0∞)* (A (N-k)*B k) := by
    simp_rw [clusterConvolution_configuration]
    rw [lintegral_finsetSum]
    · have hi (T : Finset (Fin N)) :
          (∫⁻ x : Fin N → X,
            F (configurationMultiset (fun i : {i // i ∉ T} => x i))*
            G (configurationMultiset (fun i : T => x i)) ∂Measure.pi (fun _ => μ)) = A (N-T.card)*B T.card := by
        rw [configuration_split_integral hF hG μ T,
          configuration_integral_card F μ, configuration_integral_card G μ]
        have hcardA : Fintype.card {i : Fin N // i ∈ T} = T.card := Fintype.card_coe T
        have hcardB : Fintype.card {i : Fin N // i ∉ T} = N-T.card := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardA]
        rw [hcardB, Fintype.card_coe T]
      simp_rw [hi]
      exact ennreal_subsets_card N (fun k => A (N-k)*B k)
    · intro T _
      have hFa : Measurable (fun x : Fin N → X => F (configurationMultiset (fun i : {i // i ∉ T} => x i))) := by
        have hh := (hF 0 {i // i ∉ T}).comp (show Measurable (fun x : Fin N → X => fun i : {i // i ∉ T} => x i) from measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))
        simpa only [zero_add, Function.comp_def] using hh
      have hGa : Measurable (fun x : Fin N → X => G (configurationMultiset (fun i : T => x i))) := by
        have hh := (hG 0 T).comp (show Measurable (fun x : Fin N → X => fun i : T => x i) from measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))
        simpa only [zero_add, Function.comp_def] using hh
      exact hFa.mul hGa
  simp only [particleMultiset]
  simp_rw [hN, Finset.mul_sum]
  have hcoeff (N k : ℕ) (hk : k ∈ Finset.range (N+1)) :
      fockCoeff z N*((N.choose k : ℝ≥0∞)*(A (N-k)*B k)) =
        (fockCoeff z k*B k)*(fockCoeff z (N-k)*A (N-k)) := by
    rw [← mul_assoc, fockCoeff_choose z (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
    ring
  have hsum (N : ℕ) :
      (∑ k ∈ Finset.range (N+1), fockCoeff z N*((N.choose k : ℝ≥0∞)*(A (N-k)*B k))) =
      ∑ k ∈ Finset.range (N+1), (fockCoeff z k*B k)*(fockCoeff z (N-k)*A (N-k)) := by
    exact Finset.sum_congr rfl (fun k hk => hcoeff N k hk)
  change (∑' N, ∑ k ∈ Finset.range (N+1), fockCoeff z N*((N.choose k : ℝ≥0∞)*(A (N-k)*B k))) = _
  simp_rw [hsum]
  rw [ennreal_tsum_triangle (fun k n => (fockCoeff z k*B k)*(fockCoeff z n*A n))]
  simp_rw [ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_mul_right, mul_comm]
  rfl

end Fock
end RadialTransition
end

end OAI
