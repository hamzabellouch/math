import OAI.NumberTheory.JointDickman.Amplification.AdditionSmallBall

namespace OAI

/-! # The manuscript's actual addition-prime process -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def additionPrimes (B : ℕ) (Y : ℝ) : Finset ℕ :=
  largePrimeSet (Real.exp (min Y (4 * B))) (auxiliaryCutoff B)

theorem additionPrimes_prime (B : ℕ) (Y : ℝ) : ∀ p ∈ additionPrimes B Y, p.Prime := by
  intro p hp
  exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2

theorem additionPrimes_rough (B : ℕ) (Y : ℝ) :
    ∀ p ∈ additionPrimes B Y, auxiliaryCutoff B < p := by
  intro p hp
  exact_mod_cast (mem_filter.mp hp).2

theorem additionPrimes_contains_cutoff {B : ℕ} {Y : ℝ} (hY : 0 ≤ Y) (hYB : Y ≤ 8 * B) :
    (Nat.primesLE (additionSieveCutoff Y)).filter (fun p => auxiliaryCutoff B < p) ⊆ additionPrimes B Y := by
  intro p hp
  obtain ⟨hpZ, hpP⟩ := mem_filter.mp hp
  have hscale : Y / 100 ≤ min Y (4 * B) := le_min (by linarith only [hY]) (by linarith only [hYB, hY])
  have hZ : (additionSieveCutoff Y : ℝ) ≤ Real.exp (min Y (4 * B)) :=
    (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr hscale)
  have hpp : (p : ℝ) ≤ Real.exp (min Y (4 * B)) :=
    (by exact_mod_cast (Nat.mem_primesLE.mp hpZ).1 : (p : ℝ) ≤ additionSieveCutoff Y).trans hZ
  apply mem_filter.mpr
  refine ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpp, (Nat.mem_primesLE.mp hpZ).2⟩, ?_⟩
  exact_mod_cast hpP

theorem manuscript_addition_interval_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y v : ℝ,
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B → Y / 2 ≤ v →
      (∑ n ∈ Icc ⌈Real.exp v⌉₊ ⌊Real.exp (v + H)⌋₊,
        primeProductMass (additionPrimes B Y) (1 / 4) n) ≤ K / Y := by
  obtain ⟨K, hK, hbound⟩ := addition_product_small_ball hFord hM hH
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hbound
  have hlog : Tendsto (fun B : ℕ => Real.log (auxiliaryCutoff B)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp auxiliaryCutoff_tendsto)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hlog.eventually_ge_atTop Y₀, hlog.eventually_ge_atTop 0] with B hb hb0
  intro Y v hY hYB hv
  exact hY₀ Y (hb.trans hY) (auxiliaryCutoff B) (additionPrimes B Y) v hv
    (additionPrimes_prime B Y) (additionPrimes_rough B Y)
    (additionPrimes_contains_cutoff (hb0.trans hY) hYB)

open Classical in
noncomputable def additionLogIntervalMass (B : ℕ) (Y v H : ℝ) : ℝ :=
  ∑ S ∈ (additionPrimes B Y).powerset,
    if v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧ Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧
        Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ) then
      bernoulliSubsetMass (additionPrimes B Y) (fun p => (1 / 4 : ℝ) / p) S else 0

theorem additionLogIntervalMass_le_integer_interval (B : ℕ) (Y v H : ℝ) :
    additionLogIntervalMass B Y v H ≤
      ∑ n ∈ Icc ⌈Real.exp (max v (Y / 2))⌉₊ ⌊Real.exp (max v (Y / 2) + H)⌋₊,
        primeProductMass (additionPrimes B Y) (1 / 4) n := by
  classical
  rw [primeProductMass_sum_event]
  unfold additionLogIntervalMass
  apply sum_le_sum
  intro S hS
  have hSP := mem_powerset.mp hS
  have hn : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (additionPrimes_prime B Y p (hSP hp)).pos)
  have hw : 0 ≤ bernoulliSubsetMass (additionPrimes B Y) (fun p => (1 / 4 : ℝ) / p) S := by
    apply bernoulliSubsetMass_nonneg hSP
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (additionPrimes_prime B Y p hp).two_le
    exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  by_cases hlog : v ≤ Real.log (∏ p ∈ S, p : ℕ) ∧
      Real.log (∏ p ∈ S, p : ℕ) ≤ v + H ∧ Y / 2 ≤ Real.log (∏ p ∈ S, p : ℕ)
  · have hlower : Real.exp (max v (Y / 2)) ≤ (∏ p ∈ S, p : ℕ) := by
      rw [← Real.exp_log hn]
      exact Real.exp_le_exp.mpr (max_le hlog.1 hlog.2.2)
    have hupper : (∏ p ∈ S, p : ℕ) ≤ Real.exp (max v (Y / 2) + H) := by
      rw [← Real.exp_log hn]
      exact Real.exp_le_exp.mpr (hlog.2.1.trans (add_le_add (le_max_left _ _) le_rfl))
    have hmem : (∏ p ∈ S, p) ∈ Icc ⌈Real.exp (max v (Y / 2))⌉₊
        ⌊Real.exp (max v (Y / 2) + H)⌋₊ :=
      mem_Icc.mpr ⟨Nat.ceil_le.mpr hlower, Nat.le_floor hupper⟩
    simp only [hlog, hmem, and_self, ite_true, le_refl]
  · simp only [hlog, ite_false]
    split_ifs <;> first | exact hw | exact le_rfl

/-- Manuscript Lemma `amp-small-ball`, for the actual independent
Bernoulli(1/(4p)) addition product and every translated interval. -/
theorem manuscript_addition_small_ball
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {H : ℝ} (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y v : ℝ,
      Real.log (auxiliaryCutoff B) ≤ Y → Y ≤ 8 * B →
      additionLogIntervalMass B Y v H ≤ K / Y := by
  obtain ⟨K, hK, hbound⟩ := manuscript_addition_interval_bound hFord hM hH
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with B hb
  intro Y v hY hYB
  exact (additionLogIntervalMass_le_integer_interval B Y v H).trans
    (hb Y (max v (Y / 2)) hY hYB (le_max_right _ _))

end JointDickman

end OAI
