import OAI.Probability.SLE.Gauge.DenseCoverCore

namespace OAI

/-! Adapted concatenation and the mass/probability scaling of a serpentine
ribbon with a quadratic number of narrow steps. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- Success probabilities multiply as lower bounds under adapted restarts.
The successive steps need not be independent. -/
theorem adapted_successes_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (success : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet[F (n + 1)] (success n))
    (q : ℝ≥0∞)
    (hstep : ∀ n (B : Set Ω), MeasurableSet[F n] B →
      q * P B ≤ P (B ∩ success n)) :
    ∀ N : ℕ, q ^ N * P univ ≤ P (⋂ n ∈ Finset.range N, success n) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    let B : Set Ω := ⋂ n ∈ Finset.range N, success n
    have hB : MeasurableSet[F N] B := by
      apply MeasurableSet.iInter
      intro n
      apply MeasurableSet.iInter
      intro hn
      exact (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hn))) _ (hmeas n)
    have he : (⋂ n ∈ Finset.range (N + 1), success n) = B ∩ success N := by
      ext ω
      simp only [mem_iInter, Finset.mem_range, mem_inter_iff, B]
      constructor
      · intro hω
        exact ⟨fun n hn => hω n (Nat.lt_succ_of_lt hn), hω N (Nat.lt_succ_self N)⟩
      · rintro ⟨hω, hN⟩ n hn
        rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
        · exact hω n hn
        · exact hN
    rw [he, pow_succ]
    calc
      q ^ N * q * P univ = q * (q ^ N * P univ) := by ac_rfl
      _ ≤ q * P B := mul_le_mul' le_rfl ih
      _ ≤ P (B ∩ success N) := hstep N B hB

lemma ribbon_mass_power_cancellation (κ : ℝ) {m : ℝ} (hm : 0 < m) :
    m ^ 2 * (1 / m) ^ dimension κ = m ^ codimension κ := by
  rw [one_div, Real.inv_rpow hm.le, ← Real.rpow_neg hm.le,
    ← Real.rpow_two, ← Real.rpow_add hm]
  rfl

/-- The disjoint middle strips of `m²` steps of width `1/m` carry mass of
order `m^(2-d)`, with no dependence assumption in this deterministic sum. -/
theorem ribbon_m_squared_mass_lower {ι : Type*} (I : Finset ι)
    (ν : Measure ℂ) (D : ι → Set ℂ)
    (hdisj : (I : Set ι).PairwiseDisjoint D)
    (hmeas : ∀ i ∈ I, MeasurableSet (D i))
    (κ : ℝ) (m : ℕ) (hm : 0 < m) (hcard : I.card = m ^ 2)
    (b : ℝ) (_hb : 0 ≤ b)
    (hmass : ∀ i ∈ I, ENNReal.ofReal (b * (1 / (m : ℝ)) ^ dimension κ) ≤ ν (D i)) :
    ENNReal.ofReal (b * (m : ℝ) ^ codimension κ) ≤ ν (⋃ i ∈ I, D i) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [measure_biUnion_finset hdisj hmeas]
  calc
    _ = ∑ _i ∈ I, ENNReal.ofReal (b * (1 / (m : ℝ)) ^ dimension κ) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      rw [Nat.cast_pow]
      calc
        b * (m : ℝ) ^ codimension κ = b *
            ((m : ℝ) ^ 2 * (1 / (m : ℝ)) ^ dimension κ) := by
          rw [ribbon_mass_power_cancellation κ hmR]
        _ = _ := by ring
    _ ≤ _ := Finset.sum_le_sum hmass

/-- A quadratic number of fixed-probability passages has the exponential
cost used by the dense visit. -/
theorem ribbon_quadratic_probability {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      Real.exp (-C * (m : ℝ) ^ 2) ≤ q ^ (m ^ 2) := by
  have hlog : Real.log q ≤ 0 := Real.log_nonpos hq.le hq1
  refine ⟨1 - Real.log q, by linarith, ?_⟩
  intro m
  calc
    _ ≤ Real.exp ((m ^ 2 : ℕ) * Real.log q) := by
      apply Real.exp_le_exp.mpr
      rw [Nat.cast_pow]
      nlinarith [sq_nonneg (m : ℝ)]
    _ = q ^ (m ^ 2) := by rw [Real.exp_nat_mul, Real.exp_log hq]

end SLEExactGauge

end

end OAI
