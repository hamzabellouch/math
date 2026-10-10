import OAI.Analysis.CircleDomains.Modulus.PositiveCountableWeights
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Sequences

namespace OAI

/-! Compactness and cost bounds for selecting fragments in collar splicing. -/

open Set Function Filter
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem exists_joint_fragment_limits {X : Type*} [MetricSpace X] [CompactSpace X]
    (p q : ℕ → ℕ → X) (c : ℕ → ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → ℕ) (p₀ q₀ : ℕ → X) (c₀ : ℕ → ℝ≥0∞), StrictMono s ∧
      (∀ j, Tendsto (fun n => p (s n) j) atTop (𝓝 (p₀ j))) ∧
      (∀ j, Tendsto (fun n => q (s n) j) atTop (𝓝 (q₀ j))) ∧
      (∀ j, Tendsto (fun n => c (s n) j) atTop (𝓝 (c₀ j))) := by
  let v : ℕ → ℕ → X × X × ℝ≥0∞ := fun n j => (p n j, q n j, c n j)
  obtain ⟨v₀, _, s, hs, hlim⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (v n))
  refine ⟨s, fun j => (v₀ j).1, fun j => (v₀ j).2.1, fun j => (v₀ j).2.2, hs, ?_, ?_, ?_⟩
  · intro j
    exact (continuous_fst.tendsto (v₀ j)).comp (tendsto_pi_nhds.mp hlim j)
  · intro j
    exact (continuous_fst.tendsto (v₀ j).2).comp
      ((continuous_snd.tendsto (v₀ j)).comp (tendsto_pi_nhds.mp hlim j))
  · intro j
    exact (continuous_snd.tendsto (v₀ j).2).comp
      ((continuous_snd.tendsto (v₀ j)).comp (tendsto_pi_nhds.mp hlim j))

theorem fragment_limit_budget (c : ℕ → ℕ → ℝ≥0∞) (c₀ : ℕ → ℝ≥0∞)
    (A : ℕ → ℝ≥0∞) (A₀ : ℝ≥0∞)
    (hc : ∀ j, Tendsto (fun n => c n j) atTop (𝓝 (c₀ j)))
    (hA : Tendsto A atTop (𝓝 A₀))
    (hbudget : ∀ n (F : Finset ℕ), ∑ j ∈ F, c n j ≤ A n) :
    (∑' j, c₀ j) ≤ A₀ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  exact le_of_tendsto_of_tendsto (tendsto_finsetSum F (fun j _ => hc j)) hA
    (Eventually.of_forall (fun n => hbudget n F))

theorem exists_close_fragment_selection {X : Type*} [TopologicalSpace X]
    (p q : ℕ → ℕ → X) (c : ℕ → ℕ → ℝ≥0∞)
    (p₀ q₀ : ℕ → X) (c₀ ε : ℕ → ℝ≥0∞)
    (hp : ∀ j, Tendsto (fun n => p n j) atTop (𝓝 (p₀ j)))
    (hq : ∀ j, Tendsto (fun n => q n j) atTop (𝓝 (q₀ j)))
    (hc : ∀ j, Tendsto (fun n => c n j) atTop (𝓝 (c₀ j)))
    (hfinite : ∀ j, c₀ j ≠ ∞) (hε : ∀ j, ε j ≠ 0)
    (U V : ℕ → Set X) (hU : ∀ j, U j ∈ 𝓝 (p₀ j)) (hV : ∀ j, V j ∈ 𝓝 (q₀ j)) :
    ∃ N : ℕ → ℕ, ∀ j, j ≤ N j ∧ p (N j) j ∈ U j ∧ q (N j) j ∈ V j ∧
      c (N j) j ≤ c₀ j + ε j := by
  have hchoose : ∀ j, ∃ n, j ≤ n ∧ p n j ∈ U j ∧ q n j ∈ V j ∧ c n j ≤ c₀ j + ε j := by
    intro j
    have hcost : ∀ᶠ n in atTop, c n j < c₀ j + ε j :=
      (tendsto_order.mp (hc j)).2 _ (ENNReal.lt_add_right (hfinite j) (hε j))
    have hevent : ∀ᶠ n in atTop, j ≤ n ∧ p n j ∈ U j ∧ q n j ∈ V j ∧
        c n j ≤ c₀ j + ε j := by
      filter_upwards [eventually_ge_atTop j, (hp j).eventually (hU j),
        (hq j).eventually (hV j), hcost] with n hn hp' hq' hc'
      exact ⟨hn, hp', hq', hc'.le⟩
    exact hevent.exists
  choose N hN using hchoose
  exact ⟨N, hN⟩

theorem selected_fragment_total_cost (c : ℕ → ℕ → ℝ≥0∞) (N : ℕ → ℕ)
    (c₀ ε : ℕ → ℝ≥0∞) (A η : ℝ≥0∞)
    (hselection : ∀ j, c (N j) j ≤ c₀ j + ε j)
    (hc : (∑' j, c₀ j) ≤ A) (hε : (∑' j, ε j) ≤ η) :
    (∑' j, c (N j) j) ≤ A + η :=
  (ENNReal.tsum_le_tsum hselection).trans
    ((ENNReal.tsum_add).le.trans (add_le_add hc hε))

end CircleDomainRigidity

end

end OAI
