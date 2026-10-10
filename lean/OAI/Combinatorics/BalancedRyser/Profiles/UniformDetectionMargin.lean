import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

open Set Filter
open scoped Topology

namespace Balanced.UniformDetectionMargin

theorem exists_uniform_pos {X : Type*} [TopologicalSpace X]
    (s : Set X) (hs : IsCompact s) (f : ℕ → X → ℝ)
    (hf : ∀ n, LowerSemicontinuous (f n))
    (hmono : ∀ x, Monotone (fun n => f n x))
    (hdetect : ∀ x ∈ s, ∃ n, 0 < f n x) :
    ∃ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ s, ε ≤ f n x := by
  classical
  rcases s.eq_empty_or_nonempty with hs0 | hsne
  · exact ⟨0, 1, by norm_num, by simp [hs0]⟩
  obtain ⟨n, hn⟩ := hs.elim_directed_cover (fun n => (f n) ⁻¹' Ioi 0)
    (fun n => (hf n).isOpen_preimage 0)
    (by
      intro x hx
      obtain ⟨n, hn⟩ := hdetect x hx
      exact mem_iUnion.mpr ⟨n, hn⟩)
    (by
      intro i j
      refine ⟨max i j, ?_, ?_⟩
      · intro x hx
        exact lt_of_lt_of_le hx (hmono x (le_max_left i j))
      · intro x hx
        exact lt_of_lt_of_le hx (hmono x (le_max_right i j)))
  obtain ⟨x, hx, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hsne hs ((hf n).lowerSemicontinuousOn s)
  exact ⟨n, f n x, hn hx, hmin⟩

theorem exists_eventual_uniform_pos {A : Type*} (order : A → ℕ)
    (test : ℕ → A → ℝ) (hmono : ∀ a, Monotone (fun n => test n a))
    (hsubseq : ∀ u : ℕ → A, Tendsto (fun t => order (u t)) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ n : ℕ, ∃ ε : ℝ,
        0 < ε ∧ ∀ᶠ t in atTop, ε ≤ test n (u (φ t))) :
    ∃ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ Q : ℕ,
      ∀ a : A, Q ≤ order a → ε ≤ test n a := by
  classical
  by_contra hnot
  push Not at hnot
  have hbad : ∀ t : ℕ, ∃ a : A,
      t ≤ order a ∧ test t a < 1 / ((t : ℝ) + 1) := by
    intro t
    exact hnot t (1 / ((t : ℝ) + 1)) (by positivity) t
  choose u huorder hutest using hbad
  have hu : Tendsto (fun t => order (u t)) atTop atTop :=
    tendsto_atTop_mono huorder tendsto_id
  obtain ⟨φ, hφ, n, ε, hε, heps⟩ := hsubseq u hu
  have hsmall : ∀ᶠ t in atTop, 1 / ((φ t : ℝ) + 1) < ε :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually_lt_const hε
  have hindex : ∀ᶠ t in atTop, n ≤ φ t := hφ.tendsto_atTop.eventually (eventually_ge_atTop n)
  have hfalse : ∀ᶠ t : ℕ in atTop, False := by
    filter_upwards [heps, hsmall, hindex] with t ht hs hi
    have hle : test n (u (φ t)) ≤ test (φ t) (u (φ t)) := hmono _ hi
    linarith [hutest (φ t)]
  obtain ⟨t, ht⟩ := hfalse.exists
  exact ht

end Balanced.UniformDetectionMargin

end OAI
