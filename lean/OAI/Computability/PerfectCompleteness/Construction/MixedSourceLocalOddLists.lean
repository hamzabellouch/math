import OAI.Computability.PerfectCompleteness.Construction.SourceLocalOddLists

namespace OAI

section

namespace PerfectCompleteness.MixedSourceLocalOddLists

open scoped BigOperators Classical
open PointwiseSpaces TreeSourceSpaces SourceAnswerEquiv
open UniqueGamesTheorem.Foundations.Games

abbrev F2 := ZMod 2

noncomputable section

section Composition

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

private theorem parity_comp (π : A → B) (ρ : B → C) (L : Finset A) :
    OddLists.parityPushforward ρ (OddLists.parityPushforward π L) =
      OddLists.parityPushforward (ρ ∘ π) L := by
  let f : A → F2 := fun a => if a ∈ L then 1 else 0
  have hf : OddLists.support f = L := by
    ext a
    by_cases ha : a ∈ L <;> simp [OddLists.mem_support, f, ha]
  rw [← hf, OddLists.parityPushforward_support, OddLists.parityPushforward_support,
    OddLists.parityPushforward_support]
  congr 1
  funext c
  calc
    (∑ b, if ρ b = c then ∑ a, if π a = b then f a else 0 else 0) =
        ∑ b, ∑ a, if ρ b = c then (if π a = b then f a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : ρ b = c <;> simp only [hb, ite_true, ite_false, Finset.sum_const_zero]
    _ = ∑ a, ∑ b, if ρ b = c then (if π a = b then f a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ a, if (ρ ∘ π) a = c then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (π a)]
      · simp only [Function.comp_apply, ite_true]
      · intro b _ hb
        simp only [ite_eq_right (Ne.symm hb), ite_self]
      · intro h
        exact (h (Finset.mem_univ _)).elim

private theorem oddList_map_comp {s : Nat} (π : A → B) (ρ : B → C)
    (L : OddLists.OddList s A) :
    OddLists.OddList.map ρ (OddLists.OddList.map π L) =
      OddLists.OddList.map (ρ ∘ π) L := by
  apply Subtype.ext
  exact parity_comp π ρ L.val

end Composition

private theorem map_eq_of_map_eq {A B : Type*} {s : Nat}
    {f₁ f₂ : Fintype B} {d₁ d₂ : DecidableEq B}
    (π : A → B) (L : OddLists.OddList s A) (R : OddLists.OddList s B)
    (accepted : @OddLists.OddList.map A B s f₁ d₁ π L = R) :
    @OddLists.OddList.map A B s f₂ d₂ π L = R := by
  have hf : f₁ = f₂ := Subsingleton.elim _ _
  cases hf
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  exact accepted

variable {branch : Nat → Nat} {h t v m s : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)

private theorem encoded_accepts {B : Type*} [Fintype B] [DecidableEq B]
    (e : SourceOddLists.Occurrences m t)
    (π : LeftDomain clauses (SourceOddLists.left e) → B)
    (ρ : B → SourceOddLists.RightLabels t)
    (hcomm : ρ ∘ π = (actualProjection clauses e :
      LeftDomain clauses (SourceOddLists.left e) → SourceOddLists.RightLabels t))
    (L : OddLists.OddList s (LeftDomain clauses (SourceOddLists.left e)))
    (R : OddLists.OddList s B) (hnative : OddLists.OddList.map π L = R) :
    OddLists.OddList.map (SourceOddLists.projection clauses e)
      (encodeOddList clauses (SourceOddLists.left e) L) = OddLists.OddList.map ρ R := by
  let actual : LeftDomain clauses (SourceOddLists.left e) → SourceOddLists.RightLabels t :=
    actualProjection clauses e
  have henc0 := encodeOddList_projection clauses e L
  have henc : OddLists.OddList.map actual L =
      OddLists.OddList.map (SourceOddLists.projection clauses e)
        (encodeOddList clauses (SourceOddLists.left e) L) :=
    map_eq_of_map_eq (B := SourceOddLists.RightLabels t) actual L _ henc0.symm
  calc
    _ = OddLists.OddList.map actual L := henc.symm
    _ = OddLists.OddList.map (ρ ∘ π) L :=
      congrArg (fun f : LeftDomain clauses (SourceOddLists.left e) → SourceOddLists.RightLabels t =>
        OddLists.OddList.map f L) hcomm.symm
    _ = OddLists.OddList.map ρ (OddLists.OddList.map π L) := (oddList_map_comp π ρ L).symm
    _ = OddLists.OddList.map ρ R := congrArg (OddLists.OddList.map ρ) hnative

abbrev Endpoints := RecursiveSpaces.Slots branch h → Fin t → SourceKeys.Endpoint v m

def slotsOf (q : Endpoints (branch := branch) (h := h) (t := t) (v := v) (m := m)) :
    RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot :=
  fun leaf k => SourceKeys.slot clauses (q leaf k)

abbrev RightForms :=
  (q : Endpoints (branch := branch) (h := h) (t := t) (v := v) (m := m)) →
    SourceLocalOddLists.Form (slotsOf clauses q)

def defaultValue : (q : SourceKeys.Endpoint v m) → (SourceKeys.slot clauses q).Domain
  | .clause c => (clauseAnswerEquiv (clauses c).signs).symm 0
  | .variable _ => false

def readBit : (q : SourceKeys.Endpoint v m) → (SourceKeys.slot clauses q).Domain → Bool
  | .clause _, _ => false
  | .variable _, b => b

def leafToBits (q : Fin t → SourceKeys.Endpoint v m)
    (a : MixedSupport.Assignment (fun k => SourceKeys.slot clauses (q k))) :
    SourceOddLists.RightLabels t :=
  fun k => readBit clauses (q k) (a k)

def rightResponse (positive : 0 < s) (forms : RightForms (branch := branch) (h := h) (t := t) clauses)
    (q : Endpoints (branch := branch) (h := h) (t := t) (v := v) (m := m))
    (leaf : RecursiveSpaces.Slots branch h) : OddLists.OddList s (SourceOddLists.RightLabels t) :=
  OddLists.OddList.map (leafToBits clauses (q leaf))
    (SourceLocalOddLists.extract positive (slotsOf clauses q) (forms q) leaf
      (fun k => defaultValue clauses (q leaf k)))

def target : Bool → SourceClause.Occurrence m → SourceKeys.Endpoint v m
  | false, e => .clause e.1
  | true, e => .variable ((clauses e.1).variable e.2)

def step : (projected : Bool) → (e : SourceClause.Occurrence m) →
    SourceKeys.Step clauses (.clause e.1) (target clauses projected e)
  | false, e => .keep (.clause e.1)
  | true, e => .select e.1 e.2

def rightEndpoints (projected : RecursiveSpaces.Slots branch h → Bool)
    (e : SourceLocalOddLists.Occurrences (branch := branch) (h := h) (m := m) (t := t)) :
    Endpoints (branch := branch) (h := h) (t := t) (v := v) (m := m) :=
  fun leaf k => target clauses (projected leaf) (e leaf k)

def treeProjection (projected : RecursiveSpaces.Slots branch h → Bool)
    (e : SourceLocalOddLists.Occurrences (branch := branch) (h := h) (m := m) (t := t)) :
    ∀ leaf k, MixedSupport.Projection
      (leftTreeSlots clauses (fun j => SourceOddLists.left (e j)) leaf k)
      (slotsOf clauses (rightEndpoints clauses projected e) leaf k) :=
  fun leaf k => (step clauses (projected leaf) (e leaf k)).projection

theorem clean_leaf_projection (projected : RecursiveSpaces.Slots branch h → Bool)
    (e : SourceLocalOddLists.Occurrences (branch := branch) (h := h) (m := m) (t := t))
    (leaf : RecursiveSpaces.Slots branch h) (hp : projected leaf = true) :
    leafToBits clauses (rightEndpoints clauses projected e leaf) ∘
        MixedSupport.projectionMap (treeProjection clauses projected e leaf) =
      actualProjection clauses (e leaf) := by
  funext a k
  change readBit clauses (target clauses (projected leaf) (e leaf k))
      ((step clauses (projected leaf) (e leaf k)).projection.map (a k)) =
    (a k).val.at (e leaf k).2
  rw [hp]
  rfl

section Clean

open SourceLocalOddLists (CleanLeaves fill)

variable (clean : RecursiveSpaces.Slots branch h → Prop)
  (projected : RecursiveSpaces.Slots branch h → Bool)
  (background : SourceLocalOddLists.Occurrences (branch := branch) (h := h) (m := m) (t := t))

def strategy (positive : 0 < s)
    (leftForms : SourceLocalOddLists.LeftForms (branch := branch) (h := h) (t := t) clauses) (rightForms : RightForms (branch := branch) (h := h) (t := t) clauses) :
    Strategy (CleanLeaves clean → Fin t → Fin m) (CleanLeaves clean → Fin t → Fin v)
      (CleanLeaves clean → OddLists.OddList s (SourceOddLists.LeftLabels t))
      (CleanLeaves clean → OddLists.OddList s (SourceOddLists.RightLabels t)) :=
  (fun q leaf => SourceLocalOddLists.leftResponse clauses positive leftForms
      (fill clean (fun j => SourceOddLists.left (background j)) q) leaf.val,
   fun q leaf => rightResponse clauses positive rightForms
      (fill clean (rightEndpoints clauses projected background)
        (fun i k => SourceKeys.Endpoint.variable (q i k))) leaf.val)

theorem fill_rightEndpoints (hclean : ∀ leaf, clean leaf → projected leaf = true)
    (e : CleanLeaves clean → SourceOddLists.Occurrences m t) :
    fill clean (rightEndpoints clauses projected background)
        (fun i k => SourceKeys.Endpoint.variable (SourceOddLists.right clauses (e i) k)) =
      rightEndpoints clauses projected (fill clean background e) := by
  funext leaf k
  by_cases hc : clean leaf
  · simp only [SourceLocalOddLists.fill, dite_eq_left hc, rightEndpoints, hclean leaf hc, target]
    rfl
  · simp only [SourceLocalOddLists.fill, dite_eq_right hc, rightEndpoints]

theorem strategy_wins [NeZero m] (positive : 0 < s)
    (leftForms : SourceLocalOddLists.LeftForms (branch := branch) (h := h) (t := t) clauses) (rightForms : RightForms (branch := branch) (h := h) (t := t) clauses)
    (hclean : ∀ leaf, clean leaf → projected leaf = true)
    (e : CleanLeaves clean → SourceOddLists.Occurrences m t)
    (z : Module.Dual F2 (squareSpace
      (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j))))))
    (hform : leftForms (fun j => SourceOddLists.left (fill clean background e j)) =
      OddListExtraction.multiplicationForm
        (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j)))) z)
    (hone :
      (1 : Domain (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j))) → F2) ∈
      squareSpace (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j)))))
    (hnorm : z ⟨1, hone⟩ = 1)
    (hrank : OddListExtraction.formRank
      (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j))))
      (leftForms (fun j => SourceOddLists.left (fill clean background e j))) ≤ s)
    (hagree : ∀ f g,
      rightForms (rightEndpoints clauses projected (fill clean background e)) f g =
      OddListExtraction.multiplicationForm
        (H (leftTreeSlots clauses (fun j => SourceOddLists.left (fill clean background e j)))) z
        (HPullback (treeProjection clauses projected (fill clean background e)) f)
        (HPullback (treeProjection clauses projected (fill clean background e)) g)) :
    (IndexedRepetition.game (SourceOddLists.game s clauses t) (CleanLeaves clean)).wins
      (strategy clauses clean projected background positive leftForms rightForms) e = true := by
  simp only [OccurrenceGame.wins, IndexedRepetition.game, SourceOddLists.game,
    OddListGame.game, OccurrenceGame.ofProjection, strategy, decide_eq_true_eq]
  intro leaf
  rw [SourceLocalOddLists.fill_comp clean background e SourceOddLists.left,
    fill_rightEndpoints clauses clean projected background hclean e]
  let full : SourceLocalOddLists.Occurrences (branch := branch) (h := h) (m := m) (t := t) :=
    fill clean background e
  let qL : SourceLocalOddLists.LeftQuestions (branch := branch) (h := h) (t := t) (m := m) :=
    fun j => SourceOddLists.left (full j)
  let qR : Endpoints (branch := branch) (h := h) (t := t) (v := v) (m := m) :=
    rightEndpoints clauses projected full
  let slotsL : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot :=
    leftTreeSlots (branch := branch) (n := h) clauses qL
  let slotsR : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot :=
    slotsOf (branch := branch) (h := h) (t := t) clauses qR
  let L : OddLists.OddList s (LeftDomain clauses (SourceOddLists.left (full leaf.val))) :=
    SourceLocalOddLists.extract (branch := branch) (h := h) (t := t)
      positive slotsL (leftForms qL) leaf.val
      ((leftEquiv clauses (SourceOddLists.left (full leaf.val))).symm (fun _ => 0))
  let R : OddLists.OddList s (LeafDomain slotsR leaf.val) :=
    SourceLocalOddLists.extract (branch := branch) (h := h) (t := t)
      positive slotsR (rightForms qR) leaf.val
      (fun k => defaultValue clauses (qR leaf.val k))
  let π : LeftDomain clauses (SourceOddLists.left (full leaf.val)) → LeafDomain slotsR leaf.val :=
    MixedSupport.projectionMap
      (treeProjection (branch := branch) (h := h) (t := t) clauses projected full leaf.val)
  let ρ : LeafDomain slotsR leaf.val → SourceOddLists.RightLabels t :=
    leafToBits clauses (qR leaf.val)
  have hraw := SourceLocalOddLists.extract_accepts (branch := branch) (h := h) (t := t)
      (slots := slotsL) (projected := slotsR) positive
      (treeProjection (branch := branch) (h := h) (t := t) clauses projected full)
      leaf.val (leftForms qL) (rightForms qR) z hform hone hnorm hrank hagree
      ((leftEquiv clauses (SourceOddLists.left (full leaf.val))).symm (fun _ => 0))
      (fun k => defaultValue clauses (qR leaf.val k))
  have hnative : OddLists.OddList.map π L = R := map_eq_of_map_eq π L R hraw
  have hcomm : ρ ∘ π =
      (actualProjection clauses (full leaf.val) :
        LeftDomain clauses (SourceOddLists.left (full leaf.val)) → SourceOddLists.RightLabels t) :=
    clean_leaf_projection clauses projected full leaf.val (hclean leaf.val leaf.property)
  have haccept := encoded_accepts clauses (full leaf.val) π ρ hcomm L R hnative
  rw [← SourceLocalOddLists.fill_clean clean background e leaf]
  change OddLists.OddList.map (SourceOddLists.projection clauses (full leaf.val))
      (encodeOddList clauses (SourceOddLists.left (full leaf.val)) L) = OddLists.OddList.map ρ R
  exact haccept

end Clean

end
end PerfectCompleteness.MixedSourceLocalOddLists

end

end OAI
