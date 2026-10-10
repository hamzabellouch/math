import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorWholeFutureEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorEntropyLimit

namespace OAI

/-! # Sublinear terminal-future name bounds force zero predecessor information -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_information_zero_of_sublinear_words
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) ≤ C+N*ε) :
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance)=0 := by
  let I := conditionalSigmaEntropy μ B (fullFutureSigma T Q 1)
  have hI : 0 ≤ I := by
    rw [show I=conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) from
      congrArg (conditionalSigmaEntropy μ B) (fullFutureSigma_one T Q)]
    exact conditionalSigmaEntropy_comap_nonneg μ _
      (entireFutureObservation_measurable hT.measurable hQ) B
      (fun b => hB (measurableSet_singleton b))
  have hupper (ε : ℝ) (hε : 0 < ε) : I ≤ ε := by
    obtain ⟨C,hC⟩ := hsub ε hε
    have hlim : Tendsto (fun N : ℕ => C/(N : ℝ)+ε) atTop (𝓝 ε) := by
      simpa only [zero_add] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const ε
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hc := hC N
    rw [predecessor_word_wholeFuture_entropy μ hT Q hQ B hB href decode hdecode N] at hc
    change (N : ℝ)*I ≤ C+N*ε at hc
    calc
      I ≤ (C+N*ε)/N := (le_div_iff₀ hn).mpr (by nlinarith)
      _ = C/N+ε := by rw [add_div,mul_div_cancel_left₀ _ hn.ne']
  have hz : I=0 := by
    apply le_antisymm _ hI
    by_contra hn
    have hp : 0 < I := lt_of_not_ge hn
    have H := hupper (I/2) (by positivity)
    linarith
  simpa only [I,fullFutureSigma_one] using hz

end DukePrimeDegree

end

end OAI
