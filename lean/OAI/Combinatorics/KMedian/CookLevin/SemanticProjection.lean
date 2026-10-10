import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookBox
import OAI.Combinatorics.KMedian.Projection.Seed
import OAI.Combinatorics.KMedian.Projection.ToInput

namespace OAI

section Inline_PCPSemanticProjection

namespace MetricKMedian.PCP
open scoped Classical

namespace ProjectionSeed
open Amplifier

abbrev Width (n : ℕ) := Fintype.card (Nested Port n)
abbrev LeftAlphabet (n : ℕ) := Fintype.card (Nested LeftLabel n)
abbrev RightAlphabet (n : ℕ) := Fintype.card (Nested RightLabel n)
noncomputable def input (C : Box) (n : ℕ) : Coverage.ProjectionInput (Width n) (LeftAlphabet n) (RightAlphabet n) :=
  if h : HasLegal C then ((good C h).power n).toInput ((good C h).consistent_power (good_consistent C h) n)
  else (bad.power n).toInput (bad.consistent_power bad_consistent n)
lemma input_perfect (C : Box) (n : ℕ) (h : C.Perfect) : (input C n).Perfect := by
  rw [input,dite_eq_left (hasLegal_of_perfect C h)]
  apply BiProjection.toInput_perfect
  exact BiProjection.perfect_power _ (good_perfect C _ h) n
lemma input_sound (C : Box) (n : ℕ) (h : ¬ C.Perfect) (ε : ℝ) (hε : 0≤ε)
    (hn : contraction^n≤ε^2) : (input C n).Sound ε := by
  unfold input
  split_ifs with hl
  · apply BiProjection.toInput_sound
    exact BiProjection.sound_of_collisionBound _ _ ε
      (BiProjection.collisionBound_power _ contraction contraction_nonneg (good_bound C hl h) n) hε hn
  · apply BiProjection.toInput_sound
    exact BiProjection.sound_of_collisionBound _ _ ε
      (BiProjection.collisionBound_power _ contraction contraction_nonneg bad_bound n) hε hn
lemma repetition_exists (ε : ℝ) (hε : 0<ε) : ∃ n : ℕ, contraction^n≤ε^2 := by
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one (sq_pos_of_pos hε) contraction_lt_one
  exact ⟨n,hn.le⟩
end ProjectionSeed

open Complexity

theorem mathematical_projection_producer (ε : ℝ) (hε : 0<ε) (L : Language) (hL : L∈NP) :
    ∃ r a b : ℕ, ∃ reduce : Word → Coverage.ProjectionInput r a b,
      (∀ x, x∈L → (reduce x).Perfect) ∧ (∀ x, x∉L → (reduce x).Sound ε) := by
  obtain ⟨verify,p,⟨P,hfinite⟩,hverify⟩ := hL
  let (k : P.tm.K) : Finite (P.tm.Γ k) := hfinite k
  let (k : P.tm.K) : Fintype (P.tm.Γ k) := Fintype.ofFinite _
  obtain ⟨n,hn⟩ := ProjectionSeed.repetition_exists ε hε
  refine ⟨ProjectionSeed.Width n,ProjectionSeed.LeftAlphabet n,ProjectionSeed.RightAlphabet n,
    fun x => ProjectionSeed.input (CookLevin.box P p x) n,?_,?_⟩
  · intro x hx
    exact ProjectionSeed.input_perfect _ n ((CookLevin.box_correct P p x).mpr ((hverify x).mp hx))
  · intro x hx
    apply ProjectionSeed.input_sound _ n _ ε hε.le hn
    intro hc
    exact hx ((hverify x).mpr ((CookLevin.box_correct P p x).mp hc))
end MetricKMedian.PCP

end Inline_PCPSemanticProjection

end OAI
