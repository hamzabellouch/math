import Mathlib
import OAI.Computability.MinUncut.Games.Sampling

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

abbrev HintCoefficients (I : Type*) (q : ℕ) :=
  Fin q → (F₂ × ((I → F₂) × (I → Module.Dual F₂ Triple)))

def secondHints {q : ℕ} (V : I → SecondQuestion Name) (c : HintCoefficients I q) :
    Fin q → Forms (SecondAlphabet V) := fun k => hintGenerator V (c k)

def firstHints {q : ℕ} (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (c : HintCoefficients I q) : Fin q → Forms (FirstAlphabet U) :=
  fun k => formPullback (projection U hidden pos) (secondHints (secondQuestion U hidden pos) c k)

structure HintedStrategy (Name I : Type*) [Fintype I] (q : ℕ) where
  first : (U : I → Equation Name) → (Fin q → Forms (FirstAlphabet U)) → FirstAlphabet U
  second : (V : I → SecondQuestion Name) → (Fin q → Forms (SecondAlphabet V)) → SecondAlphabet V

def hintedWins {q : ℕ} (strategy : HintedStrategy Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (c : HintCoefficients I q) : Prop :=
  projection U hidden pos (strategy.first U (firstHints U hidden pos c)) =
    strategy.second (secondQuestion U hidden pos) (secondHints (secondQuestion U hidden pos) c)

def patch {X : Type*} (A : I → Prop) (background : I → X) (active : {i // A i} → X) : I → X :=
  fun i => if h : A i then active ⟨i,h⟩ else background i

omit [Fintype I] in
@[simp] lemma patch_active {X : Type*} (A : I → Prop) (background : I → X)
    (active : {i // A i} → X) (i : {i // A i}) : patch A background active i = active i := by
  simp [patch,i.property]

omit [Fintype I] in
@[simp] lemma patch_inactive {X : Type*} (A : I → Prop) (background : I → X)
    (active : {i // A i} → X) (i : I) (hi : ¬A i) : patch A background active i = background i := by
  simp [patch,hi]

omit [Fintype I] in
lemma patch_comp {X Y : Type*} (A : I → Prop) (background : I → X)
    (active : {i // A i} → X) (f : X → Y) :
    (fun i => f (patch A background active i)) = patch A (fun i => f (background i)) (fun i => f (active i)) := by
  funext i
  by_cases h : A i <;> simp [patch,h]

def slotZero (v : SecondQuestion Name) : Fin (secondSlotCount v) :=
  ⟨0,by cases v <;> exact Nat.zero_lt_succ _⟩

def readBit (V : I → SecondQuestion Name) (a : SecondAlphabet V) (i : I) : F₂ :=
  a i (slotZero (V i))

omit [Fintype I] in
lemma projection_hidden_bit (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (a : FirstAlphabet U) (i : I) (hi : hidden i=true) :
    readBit (secondQuestion U hidden pos) (projection U hidden pos a) i=(a i).val (pos i) := by
  change (slotProjection (U i) (hidden i) (pos i) (a i))
    (slotZero (slotQuestion (U i) (hidden i) (pos i)))=_
  rw [hi]
  rfl

lemma firstHints_position_independent {q : ℕ} (U : I → Equation Name) (hidden : I → Bool)
    (pos pos' : I → Fin 3) (c : HintCoefficients I q)
    (h : ∀ k j, hidden j=true → pos j≠pos' j → (c k).2.1 j=0) :
    firstHints U hidden pos c=firstHints U hidden pos' c := by
  funext k
  exact pulledHint_independent_active U hidden pos pos' _ _ _ (h k)

lemma ordinary_accepts_of_valid_coordinate (E : Equation Name) (a : alphabet E)
    (p : Fin 3) (b : F₂) (he : a.val p=b) :
    ordinaryAccepts E (E.names p) a.val b=true := by
  apply decide_eq_true
  refine ⟨a.property,?_⟩
  intro p' hp'
  exact (a.property.2 p' p hp').trans he

omit [Fintype I] in

lemma secondQuestion_patch (A : I → Prop) (hidden : I → Bool)
    (hA : ∀ i, A i → hidden i=true) (bgU : I → Equation Name) (bgp : I → Fin 3)
    (U : {i // A i} → Equation Name) (p : {i // A i} → Fin 3) :
    secondQuestion (patch A bgU U) hidden (patch A bgp p) =
      patch A (secondQuestion bgU hidden bgp) (fun i => Sum.inl ((U i).names (p i))) := by
  funext i
  by_cases hi : A i
  · simp [patch,secondQuestion,slotQuestion,hA i hi,hi]
  · simp [patch,secondQuestion,hi]

end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

theorem active_simulation {q : ℕ} (strategy : HintedStrategy Name I q)
    (A : I → Prop) (hidden : I → Bool) (hA : ∀ i, A i → hidden i=true)
    (c : HintCoefficients I q) (hzero : ∀ k i, A i → (c k).2.1 i=0)
    (bgU : I → Equation Name) (bgp : I → Fin 3) :
    ∃ (a : ({i // A i} → Equation Name) → {i // A i} → Triple)
      (b : ({i // A i} → Name) → {i // A i} → F₂),
    ∀ (U : {i // A i} → Equation Name) (p : {i // A i} → Fin 3),
      hintedWins strategy (patch A bgU U) hidden (patch A bgp p) c →
      ∀ j, ordinaryAccepts (U j) ((U j).names (p j)) (a U j)
        (b (fun i => (U i).names (p i)) j)=true := by
  classical
  let p₀ : I → Fin 3 := patch A bgp (fun _ => 0)
  let first (U : {i // A i} → Equation Name) : FirstAlphabet (patch A bgU U) :=
    strategy.first (patch A bgU U) (firstHints (patch A bgU U) hidden p₀ c)
  let V (y : {i // A i} → Name) : I → SecondQuestion Name :=
    patch A (secondQuestion bgU hidden bgp) (fun i => Sum.inl (y i))
  let second (y : {i // A i} → Name) : SecondAlphabet (V y) :=
    strategy.second (V y) (secondHints (V y) c)
  let a := fun U (j : {i // A i}) => (first U j).val
  let b := fun y (j : {i // A i}) => readBit (V y) (second y) j
  refine ⟨a,b,?_⟩
  intro U p hwin j
  have hints : firstHints (patch A bgU U) hidden (patch A bgp p) c =
      firstHints (patch A bgU U) hidden p₀ c := by
    apply firstHints_position_independent
    intro k i _ hdiff
    apply hzero k i
    by_contra hi
    exact hdiff (by simp [p₀,patch,hi])
  have hv : secondQuestion (patch A bgU U) hidden (patch A bgp p) =
      V (fun i => (U i).names (p i)) := secondQuestion_patch A hidden hA bgU bgp U p
  unfold hintedWins at hwin
  rw [hints] at hwin
  have hb := congrArg (fun z =>
    readBit (secondQuestion (patch A bgU U) hidden (patch A bgp p)) z j) hwin
  rw [projection_hidden_bit _ _ _ _ _ (hA j j.property)] at hb
  have hcoord : a U j (p j)=b (fun i => (U i).names (p i)) j := by
    simp only [patch_active] at hb
    rw [hv] at hb
    exact hb
  have hvalid : Valid (U j) (a U j) := by
    have hv' : Valid (patch A bgU U j) (a U j) := (first U j).property
    simpa only [patch_active] using hv'
  apply decide_eq_true
  refine ⟨hvalid,?_⟩
  intro p' hp'
  exact (hvalid.2 p' (p j) hp').trans hcoord

end MinUncut.Outer

end

end OAI
