import OAI.Analysis.CircleDomains.Topology.CollarFragmentSelection
import OAI.Analysis.CircleDomains.Modulus.EventualFragmentBudget

namespace OAI

/-! A common subsequence for both endpoint collars and the retained middle,
with the full limiting cost budget. -/

open Set Function Filter
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_twoEnded_fragment_limits {X : Type*} [MetricSpace X] [CompactSpace X]
    (x y : ℕ → ℕ → X) (c d : ℕ → ℕ → ℝ≥0∞) (m : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → ℕ) (x₀ y₀ : ℕ → X) (c₀ d₀ : ℕ → ℝ≥0∞) (m₀ : ℝ≥0∞),
      StrictMono s ∧
      (∀j, Tendsto (fun n => x (s n) j) atTop (𝓝 (x₀ j))) ∧
      (∀j, Tendsto (fun n => y (s n) j) atTop (𝓝 (y₀ j))) ∧
      (∀j, Tendsto (fun n => c (s n) j) atTop (𝓝 (c₀ j))) ∧
      (∀j, Tendsto (fun n => d (s n) j) atTop (𝓝 (d₀ j))) ∧
      Tendsto (fun n => m (s n)) atTop (𝓝 m₀) := by
  let v : ℕ → (ℕ → X × X × ℝ≥0∞ × ℝ≥0∞) × ℝ≥0∞ :=
    fun n => (fun j => (x n j, y n j, c n j, d n j), m n)
  obtain ⟨v₀, _, s, hs, hv⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (v n))
  have hfirst : Tendsto (fun n => (v (s n)).1) atTop (𝓝 v₀.1) :=
    (continuous_fst.tendsto v₀).comp hv
  have hj (j : ℕ) := tendsto_pi_nhds.mp hfirst j
  have hlast (j : ℕ) := (continuous_snd.tendsto (v₀.1 j)).comp (hj j)
  have hcost (j : ℕ) := (continuous_snd.tendsto (v₀.1 j).2).comp (hlast j)
  exact ⟨s, fun j => (v₀.1 j).1, fun j => (v₀.1 j).2.1,
    fun j => (v₀.1 j).2.2.1, fun j => (v₀.1 j).2.2.2, v₀.2, hs,
    fun j => (continuous_fst.tendsto (v₀.1 j)).comp (hj j),
    fun j => (continuous_fst.tendsto (v₀.1 j).2).comp (hlast j),
    fun j => (continuous_fst.tendsto (v₀.1 j).2.2).comp (hcost j),
    fun j => (continuous_snd.tendsto (v₀.1 j).2.2).comp (hcost j),
    (continuous_snd.tendsto v₀).comp hv⟩

theorem twoEnded_limit_budget_of_eventually
    (c d : ℕ → ℕ → ℝ≥0∞) (m A : ℕ → ℝ≥0∞)
    (c₀ d₀ : ℕ → ℝ≥0∞) (m₀ A₀ : ℝ≥0∞)
    (hc : ∀j, Tendsto (fun n => c n j) atTop (𝓝 (c₀ j)))
    (hd : ∀j, Tendsto (fun n => d n j) atTop (𝓝 (d₀ j)))
    (hm : Tendsto m atTop (𝓝 m₀)) (hA : Tendsto A atTop (𝓝 A₀))
    (hbudget : ∀F : Finset ℕ, ∀ᶠn in atTop, m n + ∑j ∈ F, (c n j + d n j) ≤ A n) :
    m₀ + (∑'j, c₀ j) + (∑'j, d₀ j) ≤ A₀ := by
  rw [add_assoc, ← ENNReal.tsum_add, ENNReal.tsum_eq_iSup_sum, ENNReal.add_iSup]
  apply iSup_le
  intro F
  exact le_of_tendsto_of_tendsto
    (hm.add (tendsto_finsetSum F (fun j _ => (hc j).add (hd j)))) hA (hbudget F)

end CircleDomainRigidity

end

end OAI
