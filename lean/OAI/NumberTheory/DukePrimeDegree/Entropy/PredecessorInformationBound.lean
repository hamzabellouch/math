import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureEntropyCriterion

namespace OAI

/-! # Linear word bounds control predecessor information -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets

theorem predecessor_information_le_of_word_bounds
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (a : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) ≤
        C+N*(a+ε)) :
    conditionalSigmaEntropy μ B
      (MeasurableSpace.comap (entireFutureObservation T Q) inferInstance) ≤ a := by
  let I := conditionalSigmaEntropy μ B (fullFutureSigma T Q 1)
  have hupper (ε : ℝ) (hε : 0 < ε) : I ≤ a+ε := by
    obtain ⟨C,hC⟩ := hbound ε hε
    have hlim : Tendsto (fun N : ℕ => C/(N:ℝ)+(a+ε)) atTop (𝓝 (a+ε)) := by
      simpa only [zero_add] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const (a+ε)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hc := hC N
    rw [predecessor_word_wholeFuture_entropy μ hT Q hQ B hB href decode hdecode N] at hc
    change (N:ℝ)*I ≤ C+N*(a+ε) at hc
    calc
      I ≤ (C+N*(a+ε))/N := (le_div_iff₀ hn).mpr (by nlinarith)
      _ = C/N+(a+ε) := by rw [add_div,mul_div_cancel_left₀ _ hn.ne']
  have hIa : I ≤ a := by
    by_contra h
    have hp : 0 < I-a := sub_pos.mpr (lt_of_not_ge h)
    have H := hupper ((I-a)/2) (by positivity)
    linarith
  simpa only [I,fullFutureSigma_one] using hIa

end DukePrimeDegree

end

end OAI
