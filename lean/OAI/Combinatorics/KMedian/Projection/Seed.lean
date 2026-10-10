import Mathlib
import OAI.Combinatorics.KMedian.Machines.Box
import OAI.Combinatorics.KMedian.Machines.FixedImpossible
import OAI.Combinatorics.KMedian.Machines.Iteration
import OAI.Combinatorics.KMedian.Projection.CSPProjection
import OAI.Combinatorics.KMedian.Projection.Product
import OAI.Combinatorics.KMedian.Projection.Promises
import OAI.Combinatorics.KMedian.Projection.Tensor

namespace OAI

section Inline_PCPProjectionSeed

namespace MetricKMedian.PCP
open Finset
open scoped Classical BigOperators

namespace BiProjection
variable (D S A B : Type) [Inhabited A] [Inhabited B]
def neutral : BiProjection S D D S A B where
  edge := Equiv.prodComm _ _
  project _ _ := default
lemma neutral_perfect : (neutral D S A B).Perfect :=
  ⟨fun _ => default,fun _ => default,fun _ _ => rfl⟩
omit [Inhabited A] in
lemma neutral_consistent : (neutral D S A B).Consistent := fun _ _ _ _ _ => rfl
variable {U V : Type} {D S A B : Type}
  [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
  [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
omit [Fintype U] [Fintype D] [Nonempty U] [Nonempty V] [Nonempty D]
  [Nonempty S] [Nonempty A] [Nonempty B] in
lemma collisionBound_mono (G : BiProjection U V D S A B) {r s : ℝ}
    (h : G.CollisionBound r) (hrs : r ≤ s) : G.CollisionBound s := by
  intro T _ f hf M hM hm
  exact (h T f hf M hM hm).trans (mul_le_mul_of_nonneg_right hrs hM)
end BiProjection
namespace ProjectionSeed
open Amplifier

noncomputable def gap : ℝ := 1/(capLoss:ℝ)/(18*(ExpanderFamily.growth:ℝ)^2)
lemma gap_pos : 0<gap := by
  unfold gap
  have hc : (0:ℝ)<capLoss := Nat.cast_pos.mpr capLoss_pos
  have hg : (0:ℝ)<ExpanderFamily.growth := Nat.cast_pos.mpr (by have := ExpanderFamily.growth_gt_one; omega)
  positivity
lemma gap_le_one : gap≤1 := by
  have hc : (1:ℝ)≤capLoss := by exact_mod_cast capLoss_pos
  have hg : (1:ℝ)≤ExpanderFamily.growth := by exact_mod_cast ExpanderFamily.growth_gt_one.le
  have hd : (1:ℝ)≤18*(ExpanderFamily.growth:ℝ)^2 := by nlinarith [sq_nonneg ((ExpanderFamily.growth:ℝ)-1)]
  exact (div_le_self (by positivity) hd).trans ((div_le_one (by positivity)).mpr hc)
noncomputable def contraction : ℝ := max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)
lemma contraction_nonneg : 0≤contraction := le_trans (by norm_num : (0:ℝ)≤1-1/1024) (le_max_right _ _)
lemma contraction_lt_one : contraction<1 := by
  change max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)<1
  apply max_lt
  · have h : (0:ℝ)<((gap/2)/4)^2 := sq_pos_of_pos (by have := gap_pos; positivity)
    nlinarith
  · norm_num

abbrev Degree := GlobalRegularization.Degree
abbrev Port := (Degree × Bool) × Bool
abbrev LeftLabel := (Label × Label) × Bool
abbrev RightLabel := Label × Bool
abbrev LeftPort := Bool × Bool
variable (C : Box)
abbrev Node := GlobalRegularization.Node C.amplified.csp
noncomputable def csp := GlobalRegularization.csp C.amplified.csp
instance nodeNonempty : Nonempty (Node C) := inferInstance

lemma rejection (h : ¬ C.Perfect) (a : Node C → Label) : gap≤testRate ((csp C).Bad a) := by
  have h1 := C.amplified_sound h (GlobalRegularization.decoded C.amplified.csp a)
  have h2 := GlobalRegularization.sound C.amplified.csp a
  have hd : (0:ℝ)<18*(ExpanderFamily.growth:ℝ)^2 := by
    have hg : (0:ℝ)<ExpanderFamily.growth := Nat.cast_pos.mpr (by have := ExpanderFamily.growth_gt_one; omega)
    positivity
  change (1/(capLoss:ℝ))/(18*(ExpanderFamily.growth:ℝ)^2) ≤ _
  apply (div_le_iff₀ hd).mpr
  rw [mul_comm]
  exact h1.trans h2

def HasLegal : Prop := ∀ p : Node C × Degree, ∃ a, (csp C).Legal p a
noncomputable def chosen (h : HasLegal C) (p : Node C × Degree) : Label × Label := Classical.choose (h p)
lemma chosen_legal (h : HasLegal C) : ∀ p, (csp C).Legal p (chosen C h p) := fun p => Classical.choose_spec (h p)
noncomputable def good (h : HasLegal C) :
    BiProjection ((Node C × Degree) × Bool) (Node C × Bool) LeftPort Port LeftLabel RightLabel :=
  ((csp C).projection (chosen C h)).prod (BiProjection.neutral Bool Bool Bool Bool)
noncomputable def bad : BiProjection ((Degree × Bool) × Bool) (Bool × Bool) LeftPort Port LeftLabel RightLabel :=
  (BiProjection.neutral Bool (Degree × Bool) (Label × Label) Label).prod BiProjection.impossible
lemma good_consistent (h : HasLegal C) : (good C h).Consistent :=
  BiProjection.consistent_prod _ _ ((csp C).projection_consistent _ (chosen_legal C h))
    (BiProjection.neutral_consistent _ _ _ _)
lemma bad_consistent : bad.Consistent :=
  BiProjection.consistent_prod _ _ (BiProjection.neutral_consistent _ _ _ _) BiProjection.impossible_consistent
lemma hasLegal_of_perfect (h : C.Perfect) : HasLegal C := by
  obtain ⟨a,ha⟩ := GlobalRegularization.complete C.amplified.csp
    (Classical.choose (C.amplified_complete h)) (Classical.choose_spec (C.amplified_complete h))
  intro p
  exact ⟨(a p.1,a ((GlobalRegularization.graph C.amplified.csp).rotate p).1),
    ha p.1 p.2,by intro he; rw [he]⟩
lemma good_perfect (hl : HasLegal C) (h : C.Perfect) : (good C hl).Perfect := by
  obtain ⟨a,ha⟩ := GlobalRegularization.complete C.amplified.csp
    (Classical.choose (C.amplified_complete h)) (Classical.choose_spec (C.amplified_complete h))
  exact BiProjection.perfect_prod _ _ ((csp C).projection_complete _ a ha)
    (BiProjection.neutral_perfect _ _ _ _)
lemma good_bound (hl : HasLegal C) (h : ¬ C.Perfect) : (good C hl).CollisionBound contraction := by
  have hs := (csp C).projection_sound (chosen C hl) (chosen_legal C hl) gap (rejection C h)
  have he := (csp C).projection_expands (chosen C hl) (GlobalRegularization.contracts C.amplified.csp)
  have hh := ((csp C).projection (chosen C hl)).collisionBound_of_expansion (1-gap/2) (1/4)
    (by have := gap_le_one; linarith) (by have := gap_pos; linarith) (by norm_num) (by norm_num) hs he
  have ht := BiProjection.collisionBound_prod _ (BiProjection.neutral Bool Bool Bool Bool)
    (1-(1/4:ℝ)*((1-(1-gap/2))/4)^2) 1 (by have := gap_le_one; have := gap_pos; nlinarith)
    (by norm_num) hh (BiProjection.collisionBound_one _)
  apply BiProjection.collisionBound_mono _ ht
  rw [mul_one]
  change _ ≤ max (1-(1/4:ℝ)*((gap/2)/4)^2) (1-(1:ℝ)/1024)
  apply le_trans _ (le_max_left _ _)
  exact le_of_eq (by ring)
lemma bad_bound : bad.CollisionBound contraction := by
  have ht := BiProjection.collisionBound_prod
    (BiProjection.neutral Bool (Degree × Bool) (Label × Label) Label) BiProjection.impossible
    1 (1-(1:ℝ)/1024) (by norm_num) (by norm_num)
    (BiProjection.collisionBound_one _) BiProjection.impossible_bound
  apply BiProjection.collisionBound_mono _ ht
  rw [one_mul]
  exact le_max_right _ _
end ProjectionSeed
end MetricKMedian.PCP

end Inline_PCPProjectionSeed

end OAI
