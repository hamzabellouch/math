import Mathlib

namespace OAI

open scoped BigOperators
open Finset

namespace Balanced
open scoped _root_.Balanced

variable {Index Sample : Type*}

lemma esymm_cons_succ (x : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (x ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + x * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Multiset.sum_map_mul_left]

lemma factorial_mul_esymm_le_sum_pow (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) :
    (k.factorial : ℝ) * s.esymm k ≤ s.sum ^ k := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
      cases k <;> simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | @cons x s ih =>
      have hx : 0 ≤ x := hs x (by simp)
      have hs' : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (by simp [hy])
      have hsum : 0 ≤ s.sum := Multiset.sum_nonneg hs'
      cases k with
      | zero => simp [Multiset.esymm]
      | succ k =>
          rw [esymm_cons_succ, Multiset.sum_cons]
          have h₁ := ih hs' (k + 1)
          have h₂ := mul_le_mul_of_nonneg_left (ih hs' k)
            (mul_nonneg (Nat.cast_nonneg (k + 1)) hx)
          have hb := pow_add_mul_le_add_pow hsum (by positivity : 0 ≤ 2 * s.sum + x) (k + 1)
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h₁ ⊢
          simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at hb h₂
          rw [add_comm x s.sum]
          nlinarith [hb]

lemma sum_prod_powersetCard_le (s : Finset Index) (p : Index → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (k : ℕ) :
    (∑ t ∈ s.powersetCard k, ∏ i ∈ t, p i) ≤ (∑ i ∈ s, p i) ^ k / k.factorial := by
  have h := factorial_mul_esymm_le_sum_pow (s.val.map p) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact hp i hi) k
  rw [Finset.esymm_map_val] at h
  simp only [Finset.sum_map_val] at h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < k.factorial)).2
  simpa [mul_comm] using h

lemma pow_div_factorial_le_exp_ratio (μ : ℝ) (hμ : 0 ≤ μ) (k : ℕ) (hk : 0 < k) :
    μ ^ k / k.factorial ≤ (Real.exp 1 * μ / k) ^ k := by
  have hk₀ : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc
    μ ^ k / k.factorial = (μ / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ (μ / k) ^ k * Real.exp (k : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k)
        (pow_nonneg (div_nonneg hμ (Nat.cast_nonneg k)) k)
    _ = (Real.exp 1 * μ / k) ^ k := by
      rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by simp [← Real.exp_nat_mul],
        ← mul_pow]
      congr 1
      ring

open MeasureTheory ProbabilityTheory

namespace BernoulliTail

noncomputable def countEvents (s : Finset Index) (A : Index → Set Sample) (ω : Sample) : ℕ := by
  classical
  exact (s.filter fun i => ω ∈ A i).card

lemma countEvents_ge_iff (s : Finset Index) (A : Index → Set Sample) (ω : Sample) (k : ℕ) :
    k ≤ countEvents s A ω ↔ ∃ t ∈ s.powersetCard k, ∀ i ∈ t, ω ∈ A i := by
  classical
  constructor
  · intro h
    obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq h
    refine ⟨t, Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩
    · exact ht.trans (Finset.filter_subset _ _)
    · intro i hi
      exact (Finset.mem_filter.mp (ht hi)).2
  · rintro ⟨t, ht, hA⟩
    rw [countEvents]
    rw [← (Finset.mem_powersetCard.mp ht).2]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_powersetCard.mp ht).1 hi, hA i hi⟩

lemma choose_countEvents_eq_sum (s : Finset Index) (A : Index → Set Sample) (ω : Sample) (k : ℕ) :
    ((countEvents s A ω).choose k : ℝ) =
      ∑ t ∈ s.powersetCard k, (⋂ i ∈ t, A i).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  have hset : (s.powersetCard k).filter (fun t => ∀ i ∈ t, ω ∈ A i) =
      (s.filter fun i => ω ∈ A i).powersetCard k := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
    aesop
  simp only [Set.indicator_apply, Set.mem_iInter, Finset.sum_boole]
  rw [hset, Finset.card_powersetCard]
  rfl

lemma integral_choose_countEvents {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset Index) (A : Index → Set Ω) (hA : iIndepSet A μ)
    (hm : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    (∫ ω, ((countEvents s A ω).choose k : ℝ) ∂μ) =
      ∑ t ∈ s.powersetCard k, ∏ i ∈ t, μ.real (A i) := by
  simp_rw [choose_countEvents_eq_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [integral_indicator_const 1 (by exact Finset.measurableSet_biInter t (fun i _ => hm i))]
    simp only [smul_eq_mul, mul_one, measureReal_def, hA.meas_biInter, ENNReal.toReal_prod]
  · intro t ht
    exact (integrable_const (1 : ℝ)).indicator (Finset.measurableSet_biInter t (fun i _ => hm i))

lemma count_tail_le_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset Index) (A : Index → Set Ω) (hm : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    μ.real {ω | k ≤ countEvents s A ω} ≤
      ∫ ω, ((countEvents s A ω).choose k : ℝ) ∂μ := by
  have hint : Integrable (fun ω => ((countEvents s A ω).choose k : ℝ)) μ := by
    simp_rw [choose_countEvents_eq_sum]
    apply integrable_finsetSum
    intro t ht
    exact (integrable_const (1 : ℝ)).indicator (Finset.measurableSet_biInter t (fun i _ => hm i))
  have hnonneg : 0 ≤ ∫ ω, ((countEvents s A ω).choose k : ℝ) ∂μ :=
    integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hbound := hint.measure_le_integral
    (Filter.Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (s := {ω | k ≤ countEvents s A ω}) (by
      intro ω hω
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.choose_pos hω))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal hnonneg)

lemma independent_count_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset Index) (A : Index → Set Ω) (hA : iIndepSet A μ) (k : ℕ) :
    μ.real {ω | k ≤ countEvents s A ω} ≤
      (∑ i ∈ s, μ.real (A i)) ^ k / k.factorial := by
  classical
  have hsub : {ω | k ≤ countEvents s A ω} ⊆
      ⋃ t ∈ s.powersetCard k, ⋂ i ∈ t, A i := by
    intro ω hω
    obtain ⟨t, ht, hAt⟩ := (countEvents_ge_iff s A ω k).mp hω
    simp only [Set.mem_iUnion, Set.mem_iInter]
    exact ⟨t, ht, hAt⟩
  calc
    μ.real {ω | k ≤ countEvents s A ω} ≤
        μ.real (⋃ t ∈ s.powersetCard k, ⋂ i ∈ t, A i) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ t ∈ s.powersetCard k, μ.real (⋂ i ∈ t, A i) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ t ∈ s.powersetCard k, ∏ i ∈ t, μ.real (A i) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [measureReal_def, hA.meas_biInter, ENNReal.toReal_prod]
    _ ≤ (∑ i ∈ s, μ.real (A i)) ^ k / k.factorial :=
      sum_prod_powersetCard_le s (fun i => μ.real (A i)) (fun _ _ => ENNReal.toReal_nonneg) k

lemma independent_count_tail_chain {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset Index) (A : Index → Set Ω) (hA : iIndepSet A μ)
    (hm : ∀ i, MeasurableSet (A i)) (m : ℝ)
    (hmean : ∑ i ∈ s, μ.real (A i) ≤ m) (k : ℕ) (hk : 0 < k) :
    μ.real {ω | k ≤ countEvents s A ω} ≤
        (∫ ω, ((countEvents s A ω).choose k : ℝ) ∂μ) ∧
    (∫ ω, ((countEvents s A ω).choose k : ℝ) ∂μ) ≤ m ^ k / k.factorial ∧
    m ^ k / k.factorial ≤ (Real.exp 1 * m / k) ^ k := by
  have hsum : 0 ≤ ∑ i ∈ s, μ.real (A i) :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  refine ⟨count_tail_le_moment μ s A hm k, ?_,
    pow_div_factorial_le_exp_ratio m (hsum.trans hmean) k hk⟩
  rw [integral_choose_countEvents μ s A hA hm k]
  exact (sum_prod_powersetCard_le s (fun i => μ.real (A i))
    (fun _ _ => ENNReal.toReal_nonneg) k).trans
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hsum hmean k) (by positivity))

lemma independent_count_tail_exp_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Finset Index) (A : Index → Set Ω) (hA : iIndepSet A μ)
    (hm : ∀ i, MeasurableSet (A i)) (m : ℝ)
    (hmean : ∑ i ∈ s, μ.real (A i) ≤ m) (k : ℕ) (hk : 0 < k) :
    μ.real {ω | k ≤ countEvents s A ω} ≤ (Real.exp 1 * m / k) ^ k := by
  obtain ⟨h₁, h₂, h₃⟩ := independent_count_tail_chain μ s A hA hm m hmean k hk
  exact h₁.trans (h₂.trans h₃)

end BernoulliTail

end Balanced

end OAI
