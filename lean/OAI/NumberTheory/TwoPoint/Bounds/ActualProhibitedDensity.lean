import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeMatrix
import OAI.NumberTheory.TwoPoint.Bounds.PrimeTraceParameters
import OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity

namespace OAI

/-! Apply the finite prohibited-word density estimate to the actual
prime bands and padding degree cap. No rare-event density hypothesis
is retained in this specialization. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma ProhibitedPrimeFamily.whole_factor_card_le {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (dq : ℕ × ℕ) (hdq : dq ∈ data.pairs) :
    (dq.2 * dq.1).primeFactors.card ≤ J + M := by
  rw [Nat.primeFactors_mul (data.padding_squarefree dq hdq).ne_zero
    (data.tuple_squarefree dq hdq).ne_zero]
  have hc := card_union_le dq.2.primeFactors dq.1.primeFactors
  rw [data.tuple_card dq hdq] at hc
  have hm := data.padding_card dq hdq
  omega

theorem ModFiveThetaInput.eventually_actual_prohibited_density
    (hP : ModFiveThetaInput) (h : ℕ) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (hL : 1 ≤ L) (eligible : ℕ → ℕ → Prop),
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      (data.residueLaw B hB).probability (data.deletedEvent ⌊L ^ (1 / 10 : ℝ)⌋₊ B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  have hs := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop 1)
  filter_upwards [eventually_prohibited_density 101 (by norm_num),
    hP.eventually_actual_pool_masses E W hW, hs] with L hd hm hs
  intro hL eligible
  let J := primeSupplyCount W L
  let M := ⌊100 * Real.log L⌋₊
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let B := ⌊Real.exp L⌋₊
  let H := ⌈Real.exp (L ^ (199 / 200 : ℝ))⌉₊
  let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
  have hspos : 1 ≤ s := by
    apply (Nat.le_floor_iff (Real.rpow_nonneg (zero_le_one.trans hL) _)).mpr
    simpa only [Nat.cast_one] using hs
  have hsupper : (s : ℝ) ≤ L ^ (1 / 10 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hL) _)
  have hslots : ((s * (J + M) : ℕ) : ℝ) ≤ 101 * s * Real.log L := by
    have hb := mul_le_mul_of_nonneg_left (prime_trace_degree_budget W L hW hL).1
      (show (0 : ℝ) ≤ s by positivity)
    push_cast at hb ⊢
    nlinarith
  have hlo (p : ℕ) (hp : p ∈ data.P) : H ≤ p := by
    apply centeredPrimePool_lower_nat E (L ^ (199 / 200 : ℝ)) W L J
      (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
      (primeSupplyScale_endpoint W L (zero_lt_one.trans_le hW) hL)
    exact hp
  exact hd h s J M B H data hB hspos hsupper hslots hm.2.2.1 hm.2.2.2.2.1
    hm.2.2.2.2.2 (Nat.le_ceil _) (prime_trace_endpoints L hL).1
    (prime_trace_endpoints L hL).2.1 hlo

end TwoPointCorrelations

end OAI
