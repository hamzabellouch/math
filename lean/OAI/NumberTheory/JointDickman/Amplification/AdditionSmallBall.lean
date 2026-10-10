import OAI.NumberTheory.JointDickman.Arithmetic.AdditionIntervalSieve
import OAI.NumberTheory.JointDickman.Amplification.AdditionCutoffScale

namespace OAI

/-! # Uniform small-ball bounds for the addition product -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- Any logarithmic interval of bounded length above Y/2 carries O(1/Y)
quarter-product mass. The prime set may extend above or below the interval;
only its containing the fixed sieve range is needed. -/
theorem addition_product_small_ball
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Y : ℝ in atTop, ∀ (P : ℕ) (Q : Finset ℕ) (v : ℝ),
      Y / 2 ≤ v → (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q, P < p) →
      (Nat.primesLE (additionSieveCutoff Y)).filter (fun p => P < p) ⊆ Q →
      (∑ n ∈ Icc ⌈Real.exp v⌉₊ ⌊Real.exp (v + H)⌋₊, primeProductMass Q (1 / 4) n) ≤ K / Y := by
  obtain ⟨K, hK, hsieve⟩ := addition_product_interval_sieve hFord hM
  refine ⟨200 * K * (Real.exp H + 1) + 1, by positivity, ?_⟩
  filter_upwards [additionSieveCutoff_eventually] with Y hscale
  intro P Q v hv hQ hrough hprefix
  have hY : 0 < Y := hscale.1
  have hZ := hscale.2.1
  have hlog := hscale.2.2.1
  have hrem := hscale.2.2.2.2
  have hlog0 : 0 < Real.log (additionSieveCutoff Y) := (by positivity : 0 < Y / 200).trans_le hlog
  have hv0 : 0 ≤ v := (by positivity : 0 ≤ Y / 2).trans hv
  have hX : 0 < Real.exp v := Real.exp_pos v
  have hX1 : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv0
  have huv : ⌈Real.exp v⌉₊ ≤ ⌊Real.exp (v + H)⌋₊ + 1 := by
    apply Nat.ceil_le.mpr
    have hh : Real.exp v ≤ Real.exp (v + H) := Real.exp_le_exp.mpr (by linarith only [hH])
    have hf := Nat.lt_floor_add_one (Real.exp (v + H))
    exact hh.trans (by exact_mod_cast hf.le)
  have hlow : ∀ n ∈ Ico ⌈Real.exp v⌉₊ (⌊Real.exp (v + H)⌋₊ + 1), Real.exp v ≤ (n : ℝ) := by
    intro n hn
    exact (Nat.le_ceil (Real.exp v)).trans (by exact_mod_cast (mem_Ico.mp hn).1)
  have hbound := hsieve P (additionSieveCutoff Y) ⌈Real.exp v⌉₊ (⌊Real.exp (v + H)⌋₊ + 1)
    Q (Real.exp v) huv hZ hX hQ hrough hprefix hlow
  have hlen : ((⌊Real.exp (v + H)⌋₊ + 1 : ℕ) : ℝ) - ⌈Real.exp v⌉₊ ≤
      (Real.exp H + 1) * Real.exp v := by
    have hf := Nat.floor_le (Real.exp_pos (v + H)).le
    have hc := Nat.le_ceil (Real.exp v)
    rw [Real.exp_add] at hf
    push_cast
    rw [Real.exp_add]
    nlinarith only [hf, hc, hX1]
  have hfrac : (((⌊Real.exp (v + H)⌋₊ + 1 : ℕ) : ℝ) - ⌈Real.exp v⌉₊) /
      (Real.exp v * Real.log (additionSieveCutoff Y)) ≤ 200 * (Real.exp H + 1) / Y := by
    calc
      _ ≤ ((Real.exp H + 1) * Real.exp v) / (Real.exp v * Real.log (additionSieveCutoff Y)) :=
        div_le_div_of_nonneg_right hlen (mul_nonneg hX.le hlog0.le)
      _ = (Real.exp H + 1) / Real.log (additionSieveCutoff Y) := by field_simp
      _ ≤ _ := by
        apply (div_le_div_iff₀ hlog0 hY).mpr
        have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 200 * (Real.exp H + 1))
        nlinarith only [hh]
  have hrem' : 2 * (additionSieveCutoff Y + 1 : ℝ) * additionSieveCutoff Y / Real.exp v ≤ 1 / Y := by
    apply (div_le_div_iff₀ hX hY).mpr
    simpa only [one_mul] using hrem.trans (Real.exp_le_exp.mpr hv)
  have hI : Ico ⌈Real.exp v⌉₊ (⌊Real.exp (v + H)⌋₊ + 1) =
      Icc ⌈Real.exp v⌉₊ ⌊Real.exp (v + H)⌋₊ := by
    ext n
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hI] at hbound
  calc
    _ ≤ _ := hbound
    _ ≤ K * (200 * (Real.exp H + 1) / Y) + 1 / Y :=
      add_le_add (mul_le_mul_of_nonneg_left hfrac hK.le) hrem'
    _ = _ := by ring

end JointDickman

end OAI
