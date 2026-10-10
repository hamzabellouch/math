import OAI.Combinatorics.BalancedRyser.Local.LocalConditionSpec
import OAI.Combinatorics.BalancedRyser.Probability.SurplusAcyclic

namespace OAI

namespace Balanced.Local.ConditionSpec

noncomputable section
open scoped Classical
open Surplus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} (P : EqualityPattern b κ)
variable (a : DirectionAssignment F b κ) (bits : Bits b)
variable (p : Point F) (M : MergedPairs F)

theorem exists_acyclic_codes (S : Finset (Position b))
    (u : Position b → Position b) (hb : 3 ≤ b) (hκ : κ ≤ 1)
    (hcard : 2 * b + 2 - 4 * κ ≤ S.card)
    (hex : ∀ v ∈ S, ∃ z : Code b κ,
      Holds P a bits p M v z ∧ v ∉ underlyingAnchors u z) :
    ∃ (T : Finset (Position b)) (code : Position b → Code b κ),
      T ⊆ S ∧ T.card = 3 - κ ∧
      (∀ v ∈ T, Holds P a bits p M v (code v) ∧
        v ∉ underlyingAnchors u (code v)) ∧
      WellFounded (fun x y : {v // v ∈ T} =>
        y.val ∈ underlyingAnchors u (code x.val)) := by
  have hex' : ∀ v : Position b, ∃ z : Code b κ,
      v ∈ S → Holds P a bits p M v z ∧ v ∉ underlyingAnchors u z := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨z, hz⟩ := hex v hv
      exact ⟨z, fun _ => hz⟩
    · exact ⟨Sum.inl (), fun h => False.elim (hv h)⟩
  choose code hcode using hex'
  let R : Position b → Position b → Prop :=
    fun x y => y ∈ underlyingAnchors u (code x)
  have hloop : ∀ x ∈ S, ¬ R x x := fun x hx => (hcode x hx).2
  have hdegree : ∀ x ∈ S, (S.filter (R x)).card ≤ 2 := by
    intro x _
    apply (Finset.card_le_card (show S.filter (R x) ⊆
      underlyingAnchors u (code x) from fun y hy => (Finset.mem_filter.mp hy).2)).trans
    exact underlyingAnchors_card_le_two u (code x)
  obtain ⟨T, hTS, hTcard, hTwf⟩ :=
    source_surplus_acyclic S R b κ hb hκ hcard hloop (by
      intro x hx
      convert hdegree x hx using 1
      congr 1
      ext y
      simp only [Finset.mem_filter])
  exact ⟨T, code, hTS, hTcard, fun v hv => hcode v (hTS hv), hTwf⟩

theorem badCover_zero_reuse_exists_acyclic_spec
    {b : ℕ} (P : EqualityPattern b 0)
    (a : DirectionAssignment F b 0) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M) :
    ∃ (T : Finset (Position b)) (code : Position b → Code b 0),
      T.card = 3 ∧
      (∀ v ∈ T, Holds P a bits p M v (code v) ∧ v ∉ anchors (code v)) ∧
      WellFounded (fun x y : {v // v ∈ T} => y.val ∈ anchors (code x.val)) := by
  obtain ⟨A, hA, hallowed, f, R, hR, hsurplus, _⟩ :=
    badCover_exists_marked_surplus P a bits p M (by omega) (by omega) ha hbad
  let S : Finset (Position b) := Finset.univ \ A.biUnion R
  have hex : ∀ v ∈ S, ∃ z : Code b 0,
      Holds P a bits p M v z ∧ v ∉ underlyingAnchors id z := by
    intro v hv
    obtain ⟨z, hz, hn⟩ := marked_exists_identity_spec P a bits p M f R
      hallowed hR hb ha hadm v hv
    exact ⟨z, hz, by simpa [underlyingAnchors] using hn⟩
  have hcard : 2 * b + 2 - 4 * 0 ≤ S.card := by
    simpa only [Nat.mul_zero] using hsurplus
  obtain ⟨T, code, _, hTcard, hT, hwf⟩ :=
    exists_acyclic_codes P a bits p M S id hb (by omega) hcard hex
  refine ⟨T, code, by simpa using hTcard, ?_, ?_⟩
  · simpa only [underlyingAnchors, Finset.image_id] using hT
  · simpa only [underlyingAnchors, Finset.image_id] using hwf

theorem badCover_one_reuse_exists_acyclic_spec
    {b : ℕ} (P : EqualityPattern b 1)
    (a : DirectionAssignment F b 1) (bits : Bits b) (p : Point F)
    (M : MergedPairs F) (hb : 3 ≤ b) (ha : Eligible P a)
    (hadm : Admissible P a bits p M) (hbad : BadCover P a bits p M)
    (root child : Fin b) (r s : Fin 4)
    (hshared : P.classOf root r = P.classOf child s) :
    let u := ParentMap.underlying root child r s (bits root r) (bits child s)
    ∃ (T : Finset (Position b)) (code : Position b → Code b 1),
      T.card = 2 ∧
      (∀ v ∈ T, v ∉ ParentMap.dependent child s ∧
        Holds P a bits p M v (code v) ∧ v ∉ underlyingAnchors u (code v)) ∧
      WellFounded (fun x y : {v // v ∈ T} => y.val ∈ underlyingAnchors u (code x.val)) := by
  dsimp only
  let u := ParentMap.underlying root child r s (bits root r) (bits child s)
  obtain ⟨A, hA, hallowed, f, R, hR, _, hdiscard⟩ :=
    badCover_exists_marked_surplus P a bits p M (by omega) (by omega) ha hbad
  let S : Finset (Position b) :=
    (Finset.univ \ A.biUnion R) \ ParentMap.dependent child s
  have hdep : (ParentMap.dependent child s).card ≤ 2 * 1 := by
    simpa only [ParentMap.dependent, Nat.mul_one] using
      (Finset.card_le_two (a := (child, s)) (b := (child, s - 1)))
  have hcard : 2 * b + 2 - 4 * 1 ≤ S.card := hdiscard _ hdep
  have hex : ∀ v ∈ S, ∃ z : Code b 1,
      Holds P a bits p M v z ∧ v ∉ underlyingAnchors u z := by
    intro v hv
    obtain ⟨hvs, hvd⟩ := Finset.mem_sdiff.mp hv
    exact marked_exists_spec P a bits p M f R hallowed hR ha hadm
      root child r s hshared v hvs hvd
  obtain ⟨T, code, hTS, hTcard, hT, hwf⟩ :=
    exists_acyclic_codes P a bits p M S u hb (by omega) hcard hex
  refine ⟨T, code, by simpa using hTcard, ?_, hwf⟩
  intro v hv
  exact ⟨(Finset.mem_sdiff.mp (hTS hv)).2, hT v hv⟩

end
end Balanced.Local.ConditionSpec

end OAI
