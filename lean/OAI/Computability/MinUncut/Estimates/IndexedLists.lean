import Mathlib
import OAI.Computability.MinUncut.Games.JointHintBound

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

structure IndexedLists (Name I J : Type*) [Fintype I] where
  first : (U : I → Equation Name) → (J → Forms (FirstAlphabet U)) → Finset (FirstAlphabet U)
  second : (V : I → SecondQuestion Name) → (J → Forms (SecondAlphabet V)) → Finset (SecondAlphabet V)

variable {Name I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]

def IndexedLists.numbered (lists : IndexedLists Name I J) : HintLists Name I (Fintype.card J) where
  first U D := lists.first U (fun j => D (Fintype.equivFin J j))
  second V D := lists.second V (fun j => D (Fintype.equivFin J j))

def IndexedLists.matches (lists : IndexedLists Name I J)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (B : J → Forms (SecondAlphabet (secondQuestion U hidden pos))) : Prop :=
  ∃ a ∈ lists.first U (fun j => formPullback (projection U hidden pos) (B j)),
    ∃ b ∈ lists.second (secondQuestion U hidden pos) B, projection U hidden pos a=b

lemma IndexedLists.numbered_matches (lists : IndexedLists Name I J)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3) :
    (𝔼 B : Fin (Fintype.card J) → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      if lists.numbered.matches U hidden pos B then (1 : ℝ) else 0) =
    𝔼 B : J → Forms (SecondAlphabet (secondQuestion U hidden pos)),
      if lists.matches U hidden pos B then (1 : ℝ) else 0 :=
  expect_reindex (Fintype.equivFin J) (fun B => if lists.matches U hidden pos B then 1 else 0)

theorem IndexedLists.shared_soundness [Fintype Name]
    {S : Type*} [Fintype S] [Nonempty S] (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {L R : ℕ} (lists : IndexedLists Name I J)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) (hidden : I → Bool) :
    (𝔼 w : I → S × Fin 3,
      𝔼 B : J → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
      if lists.matches (sampledEquations equations w) hidden (sampledPositions w) B
        then (1 : ℝ) else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J) ^ Fintype.card {i // hidden i=true} := by
  have h := lists.numbered.shared_soundness equations hsound
    (fun U B => hL U _) (fun V B => hR V _) hidden
  simpa only [lists.numbered_matches] using h

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

def tupleProductEquiv {I A B : Type*} : (I → A × B) ≃ ((I → A) × (I → B)) where
  toFun w := (fun i => (w i).1,fun i => (w i).2)
  invFun z := fun i => (z.1 i,z.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

lemma expect_split_tuple {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
    (f : (I → A) → (I → B) → ℝ) :
    (𝔼 w : I → A × B, f (fun i => (w i).1) (fun i => (w i).2)) =
      𝔼 a : I → A, 𝔼 b : I → B, f a b := by
  rw [← expect_pair (fun z : (I → A) × (I → B) => f z.1 z.2)]
  exact Fintype.expect_equiv tupleProductEquiv _ _ (fun _ => rfl)

variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

lemma hiddenSet_card (H : Finset I) : Fintype.card {i // hiddenSet H i=true}=H.card := by
  simpa only [hiddenSet,decide_eq_true_eq] using Fintype.card_coe H

lemma IndexedLists.shared_soundness_split [Fintype Name]
    (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {L R : ℕ} (lists : IndexedLists Name I J)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) (hidden : I → Bool) :
    (𝔼 a : I → S, 𝔼 pos : I → Fin 3,
      𝔼 B : J → Forms (SecondAlphabet (secondQuestion (fun i => equations (a i)) hidden pos)),
      if lists.matches (fun i => equations (a i)) hidden pos B then (1 : ℝ) else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J) ^ Fintype.card {i // hidden i=true} := by
  have h := lists.shared_soundness equations hsound hL hR hidden
  rw [← expect_split_tuple (fun a pos =>
    𝔼 B : J → Forms (SecondAlphabet (secondQuestion (fun i => equations (a i)) hidden pos)),
      if lists.matches (fun i => equations (a i)) hidden pos B then (1 : ℝ) else 0)]
  exact h

def backgroundMean (equations : S → Equation Name) (k : ℕ)
    (F : (U : I → Equation Name) → (hidden : I → Bool) → (pos : I → Fin 3) →
      (J → Forms (SecondAlphabet (secondQuestion U hidden pos))) → ℝ) : ℝ :=
  𝔼 H : FixedSets I k, 𝔼 a : I → S, 𝔼 pos : I → Fin 3,
    𝔼 B : J → Forms (SecondAlphabet (secondQuestion (fun i => equations (a i)) (hiddenSet H.val) pos)),
      F (fun i => equations (a i)) (hiddenSet H.val) pos B

lemma IndexedLists.full_soundness [Fintype Name]
    (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {k L R : ℕ} (hk : k≤Fintype.card I) (lists : IndexedLists Name I J)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) :
    backgroundMean equations k (fun U h pos B => if lists.matches U h pos B then 1 else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J)^k := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  unfold backgroundMean
  calc
    _ ≤ 𝔼 H : FixedSets I k,
        (L : ℝ)*(R : ℝ)*hintRate (Fintype.card J)^k := by
      apply Finset.expect_le_expect
      intro H _
      have h := lists.shared_soundness_split equations hsound hL hR (hiddenSet H.val)
      simpa only [hiddenSet_card,H.property] using h
    _ = _ := Fintype.expect_const _

open scoped BigOperators
open MinUncut.Inner OuterSmoothness
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I J S : Type*} [Fintype I] [Fintype J] [DecidableEq J]
  [Fintype S] [Nonempty S]

abbrev BackgroundStatistic (Name I J : Type*) [Fintype I] :=
  (U : I → Equation Name) → (hidden : I → Bool) → (pos : I → Fin 3) →
    (J → Forms (SecondAlphabet (secondQuestion U hidden pos))) → ℝ

omit [Nonempty S] in
lemma backgroundMean_mono (equations : S → Equation Name) (k : ℕ)
    {F G : BackgroundStatistic Name I J} (h : ∀ U hidden pos B, F U hidden pos B≤G U hidden pos B) :
    backgroundMean equations k F ≤ backgroundMean equations k G := by
  apply Finset.expect_le_expect
  intro H _
  apply Finset.expect_le_expect
  intro a _
  apply Finset.expect_le_expect
  intro pos _
  exact Finset.expect_le_expect (fun B _ => h _ _ _ _)

omit [Nonempty S] in
lemma backgroundMean_add (equations : S → Equation Name) (k : ℕ)
    (F G : BackgroundStatistic Name I J) :
    backgroundMean equations k (fun U h pos B => F U h pos B+G U h pos B) =
      backgroundMean equations k F+backgroundMean equations k G := by
  simp only [backgroundMean,Finset.expect_add_distrib]

omit [Nonempty S] in
lemma backgroundMean_mul (equations : S → Equation Name) (k : ℕ)
    (F : BackgroundStatistic Name I J) (t : ℝ) :
    backgroundMean equations k (fun U h pos B => t*F U h pos B) =
      t*backgroundMean equations k F := by
  simp only [backgroundMean,← Finset.mul_expect]

lemma backgroundMean_const (equations : S → Equation Name) {k : ℕ}
    (hk : k≤Fintype.card I) (t : ℝ) :
    backgroundMean (I := I) (J := J) equations k (fun _ _ _ _ => t)=t := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  simp only [backgroundMean,Fintype.expect_const]

end MinUncut.Outer

end

end OAI
