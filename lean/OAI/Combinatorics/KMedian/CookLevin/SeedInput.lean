import Mathlib
import OAI.Combinatorics.KMedian.Projection.PowerTable
import OAI.Combinatorics.KMedian.Projection.SeedTables

namespace OAI

section Inline_PCPSeedInput
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Binary Binary.Automatic Amplifier ProjectionTable
open scoped Classical

noncomputable def leftOrder := Ordered.fixed ProjectionSeed.LeftLabel
noncomputable def rightOrder := Ordered.fixed ProjectionSeed.RightLabel
noncomputable abbrev Width (n : ℕ) := (portOrder.nested n).entries.length
noncomputable abbrev LeftSize (n : ℕ) := (leftOrder.nested n).entries.length
noncomputable abbrev RightSize (n : ℕ) := (rightOrder.nested n).entries.length
variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def output (n : ℕ) : Coverage.ProjectionInput (Width n) (LeftSize n) (RightSize n) :=
  if hl : allLegal t=true then
    input ((good t h).power n) (nestedEquiv (goodRoot t h) n) ((goodNodes t h).nested n)
      (portOrder.nested n) (leftOrder.nested n) (rightOrder.nested n)
      ((good t h).consistent_power (good_consistent t h hl) n)
  else input (ProjectionSeed.bad.power n) (nestedEquiv badRoot n) (badNodes.nested n)
      (portOrder.nested n) (leftOrder.nested n) (rightOrder.nested n)
      (ProjectionSeed.bad.consistent_power ProjectionSeed.bad_consistent n)
lemma output_raw (n : ℕ) : (output t h n).raw=
    raw (leftOrder.nested n) (rightOrder.nested n) (power (seedTable t) n) := by
  unfold output seedTable
  split_ifs with hl
  · rw [input_raw,goodTable_build t h,power_build]
  · rw [input_raw,badTable,power_build]
lemma output_perfect (n : ℕ) (hc : ∃ a, (t.csp h).Satisfies a) : (output t h n).Perfect := by
  rw [output,dite_eq_left (allLegal_of_perfect t h hc)]
  apply input_perfect
  exact BiProjection.perfect_power _ (good_perfect t h hc) n
lemma output_sound (n : ℕ) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
    (ε : ℝ) (hε : 0≤ε) (hn : ProjectionSeed.contraction^n≤ε^2) : (output t h n).Sound ε := by
  unfold output
  split_ifs with hl
  · apply input_sound
    exact BiProjection.sound_of_collisionBound _ _ ε
      (BiProjection.collisionBound_power _ ProjectionSeed.contraction ProjectionSeed.contraction_nonneg
        (good_bound t h hl hg) n) hε hn
  · apply input_sound
    exact BiProjection.sound_of_collisionBound _ _ ε
      (BiProjection.collisionBound_power _ ProjectionSeed.contraction ProjectionSeed.contraction_nonneg
        ProjectionSeed.bad_bound n) hε hn
lemma poly_output_raw (n : ℕ) : Poly (fun t : CSPTable Label=>
    raw (leftOrder.nested n) (rightOrder.nested n) (power (seedTable t) n)) :=
  (poly_raw _ _).comp ((poly_power n).comp poly_seedTable)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedInput

end OAI
