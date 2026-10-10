import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

namespace OAI

open Filter MeasureTheory Set
open scoped Topology

namespace Balanced.SlowThreshold

theorem exists_monotone_slow_sequence (R : ℕ → ℕ → Prop)
    (hR : ∀ k, ∀ᶠ n in atTop, R n k) :
    ∃ t : ℕ → ℕ, Monotone t ∧ Tendsto t atTop atTop ∧
      ∀ᶠ n in atTop, ∀ k ≤ t n, R n k := by
  classical
  choose N hN using fun k => eventually_atTop.mp (hR k)
  let t : ℕ → ℕ := fun n => Nat.findGreatest (fun k => ∀ j ≤ k, N j ≤ n) n
  refine ⟨t, ?_, ?_, ?_⟩
  · intro m n hmn
    exact Nat.findGreatest_mono (fun k hk j hj => (hk j hj).trans hmn) hmn
  · refine tendsto_atTop.2 ?_
    intro k
    have hfinite : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (k + 1), N j ≤ n :=
      (eventually_all_finset _).2 fun j _ => eventually_ge_atTop (N j)
    filter_upwards [hfinite, eventually_ge_atTop k] with n hn hkn
    exact Nat.le_findGreatest hkn (fun j hj => hn j (Finset.mem_range.mpr (by omega)))
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    have hspec : ∀ j ≤ t n, N j ≤ n :=
      Nat.findGreatest_spec (P := fun k => ∀ j ≤ k, N j ≤ n) (Nat.zero_le n)
        (by intro j hj; have : j = 0 := Nat.eq_zero_of_le_zero hj; simpa [this] using hn)
    intro k hk
    exact hN k n (hspec k hk)

theorem exists_monotone_diagonal (p : ℕ → ℕ → ℝ)
    (hp : ∀ k, Tendsto (fun n => p n k) atTop (𝓝 0)) :
    ∃ t : ℕ → ℕ, Monotone t ∧ Tendsto t atTop atTop ∧
      Tendsto (fun n => p n (t n)) atTop (𝓝 0) := by
  have hR : ∀ k, ∀ᶠ n in atTop, |p n k| < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have habs : Tendsto (fun n => |p n k|) atTop (𝓝 0) := by
      simpa using (hp k).abs
    exact habs.eventually_lt_const hpos
  obtain ⟨t, htmono, ht, hbound⟩ := exists_monotone_slow_sequence _ hR
  refine ⟨t, htmono, ht, ?_⟩
  have hinv : Tendsto (fun n : ℕ => 1 / ((t n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
    exact h.comp ht
  have hneg : Tendsto (fun n : ℕ => -(1 / ((t n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using hinv.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hinv
  · filter_upwards [hbound] with n hn
    exact (abs_le.mp (hn (t n) le_rfl).le).1
  · filter_upwards [hbound] with n hn
    exact (abs_le.mp (hn (t n) le_rfl).le).2

theorem exists_monotone_diagonal_on (P : ℕ → Prop) (p : ℕ → ℕ → ℝ)
    (hp : ∀ k, Tendsto (fun n => p n k) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0)) :
    ∃ t : ℕ → ℕ, Monotone t ∧ Tendsto t atTop atTop ∧
      Tendsto (fun n => p n (t n)) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
  have hR : ∀ k, ∀ᶠ n in atTop, P n → |p n k| < 1 / ((k : ℝ) + 1) := by
    intro k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have habs : Tendsto (fun n => |p n k|) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
      simpa using (hp k).abs
    exact eventually_inf_principal.mp (habs.eventually_lt_const hpos)
  obtain ⟨t, htmono, ht, hbound⟩ := exists_monotone_slow_sequence _ hR
  refine ⟨t, htmono, ht, ?_⟩
  have hinv : Tendsto (fun n : ℕ => 1 / ((t n : ℝ) + 1))
      (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0))
    exact (h.comp ht).mono_left inf_le_left
  have hneg : Tendsto (fun n : ℕ => -(1 / ((t n : ℝ) + 1)))
      (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
    simpa using hinv.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hinv
  · apply eventually_inf_principal.mpr
    filter_upwards [hbound] with n hn
    intro hP
    exact (abs_le.mp (hn (t n) le_rfl hP).le).1
  · apply eventually_inf_principal.mpr
    filter_upwards [hbound] with n hn
    intro hP
    exact (abs_le.mp (hn (t n) le_rfl hP).le).2

theorem exists_antitone_tolerance_on (P : ℕ → Prop) (p : ℕ → ℝ → ℝ)
    (hp : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => p n ε) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun n => p n (ε n)) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
  obtain ⟨t, htmono, ht, hpdiag⟩ := exists_monotone_diagonal_on P
    (fun n k => p n (1 / ((k : ℝ) + 1))) (fun k => hp _ (by positivity))
  refine ⟨fun n => 1 / ((t n : ℝ) + 1), ?_, ?_, ?_, hpdiag⟩
  · intro n
    positivity
  · intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right (htmono hmn) 1
  · exact (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)).comp ht

theorem exists_common_tolerance_on {ι : Type*} [Fintype ι]
    (P : ℕ → Prop) (p : ι → ℕ → ℝ → ℝ)
    (hp : ∀ i ε, 0 < ε → Tendsto (fun n => p i n ε)
      (atTop ⊓ 𝓟 {n | P n}) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => p i n (ε n))
        (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
  classical
  have hsum : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, |p i n ε|) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
    intro ε hε
    have hi (i : ι) : Tendsto (fun n => |p i n ε|)
        (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
      simpa using (hp i ε hε).abs
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  obtain ⟨ε, hpos, hanti, hε, herr⟩ :=
    exists_antitone_tolerance_on P (fun n ε => ∑ i, |p i n ε|) hsum
  refine ⟨ε, hpos, hanti, hε, ?_⟩
  intro i
  have hneg : Tendsto (fun n => -(∑ j, |p j n (ε n)|))
      (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) := by
    simpa using herr.neg
  have hle (n : ℕ) : |p i n (ε n)| ≤ ∑ j, |p j n (ε n)| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (p j n (ε n))) (Finset.mem_univ i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hneg herr
  · intro n
    exact (abs_le.mp (hle n)).1
  · intro n
    exact (abs_le.mp (hle n)).2

theorem exists_probability_tolerance_on
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ℕ → Prop) (μ : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ)
    (hX : ∀ δ : ℝ, 0 < δ → Tendsto
      (fun n => (μ n).real {ω | δ ≤ X n ω}) (atTop ⊓ 𝓟 {n | P n}) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Antitone ε ∧
      Tendsto ε atTop (𝓝 0) ∧ Tendsto
      (fun n => (μ n).real {ω | ε n ≤ X n ω})
      (atTop ⊓ 𝓟 {n | P n}) (𝓝 0) :=
  exists_antitone_tolerance_on P (fun n δ => (μ n).real {ω | δ ≤ X n ω}) hX

end Balanced.SlowThreshold

end OAI
