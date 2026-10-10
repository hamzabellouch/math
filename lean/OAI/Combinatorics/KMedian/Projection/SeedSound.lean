import Mathlib
import OAI.Combinatorics.KMedian.Projection.RegularTable
import OAI.Combinatorics.KMedian.Projection.Seed

namespace OAI

section Inline_PCPSeedSound
namespace MetricKMedian.PCP.Compiler.SeedProgram
open Amplifier ProjectionSeed CloudOrder
open scoped Classical

variable (t : CSPTable Label) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable def good := (projection t h).prod (BiProjection.neutral Bool Bool Bool Bool)
lemma chosen_legal (hl : allLegal t=true) : ∀ p, (CloudSpec.regularCSP t h).Legal p
    (choose t (CloudSpec.vertexCode t h p.1) p.2) := by
  intro p
  exact choose_legal t h p.1 p.2 ((allLegal_correct t h).mp hl p)
lemma good_consistent (hl : allLegal t=true) : (good t h).Consistent :=
  BiProjection.consistent_prod _ _ ((CloudSpec.regularCSP t h).projection_consistent _ (chosen_legal t h hl))
    (BiProjection.neutral_consistent _ _ _ _)
lemma regular_complete (hc : ∃ a, (t.csp h).Satisfies a) :
    ∃ a, (CloudSpec.regularCSP t h).Satisfies a := by
  obtain ⟨a,ha⟩ := hc
  exact FlexibleRegularization.complete (CloudSpec.C t h) (cloudEmbed _ (CloudSpec.EO t)) (CloudSpec.padding t h) a ha
lemma allLegal_of_perfect (hc : ∃ a, (t.csp h).Satisfies a) : allLegal t=true := by
  obtain ⟨a,ha⟩ := regular_complete t h hc
  apply (allLegal_correct t h).mpr
  intro p
  apply Finset.nonempty_def.mpr
  refine ⟨(a p.1,a ((CloudSpec.regularGraph t h).rotate p).1),?_⟩
  apply (legal_correct t h p.1 p.2 _).mpr
  exact ⟨ha p.1 p.2,by intro he; rw [he]⟩
lemma good_perfect (hc : ∃ a, (t.csp h).Satisfies a) : (good t h).Perfect := by
  obtain ⟨a,ha⟩ := regular_complete t h hc
  exact BiProjection.perfect_prod _ _ ((CloudSpec.regularCSP t h).projection_complete _ a ha)
    (BiProjection.neutral_perfect _ _ _ _)
lemma rejection (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a)
    (a : GlobalRegularization.Node (CloudSpec.C t h)→Label) :
    gap≤testRate ((CloudSpec.regularCSP t h).Bad a) := by
  have h1 := hg (FlexibleRegularization.decoded (CloudSpec.C t h) (CloudSpec.padding t h) a)
  have h2 := FlexibleRegularization.sound (CloudSpec.C t h) (cloudEmbed _ (CloudSpec.EO t)) (CloudSpec.padding t h) a
  have hd : (0:ℝ)<18*(ExpanderFamily.growth:ℝ)^2 := by
    have hp : (0:ℝ)<ExpanderFamily.growth :=
      Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one ExpanderFamily.growth_gt_one)
    exact mul_pos (by norm_num) (sq_pos_of_pos hp)
  change (1/(capLoss:ℝ))/(18*(ExpanderFamily.growth:ℝ)^2)≤_
  apply (div_le_iff₀ hd).mpr
  rw [mul_comm]
  exact h1.trans h2
lemma good_bound (hl : allLegal t=true) (hg : ∀ a, 1/(capLoss:ℝ)≤(t.csp h).rejection a) :
    (good t h).CollisionBound contraction := by
  have hs := (CloudSpec.regularCSP t h).projection_sound _ (chosen_legal t h hl) gap (rejection t h hg)
  have he := (CloudSpec.regularCSP t h).projection_expands (fun p=>choose t (CloudSpec.vertexCode t h p.1) p.2)
    (FlexibleRegularization.contracts (CloudSpec.C t h) (cloudEmbed _ (CloudSpec.EO t)) (CloudSpec.padding t h))
  have hh := (projection t h).collisionBound_of_expansion (1-gap/2) (1/4)
    (by have := gap_le_one; linarith) (by have := gap_pos; linarith) (by norm_num) (by norm_num) hs he
  have ht := BiProjection.collisionBound_prod _ (BiProjection.neutral Bool Bool Bool Bool)
    (1-(1/4:ℝ)*((1-(1-gap/2))/4)^2) 1 (by have := gap_le_one; have := gap_pos; nlinarith)
    (by norm_num) hh (BiProjection.collisionBound_one _)
  apply BiProjection.collisionBound_mono _ ht
  rw [mul_one]
  change _ ≤ max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)
  apply le_trans _ (le_max_left _ _)
  exact le_of_eq (by ring)
end MetricKMedian.PCP.Compiler.SeedProgram

end Inline_PCPSeedSound

end OAI
