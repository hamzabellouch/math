import Mathlib
import OAI.Computability.MinUncut.Games.HintSoundness

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype

def paddedChoice {A : Type*} [Nonempty A] (S : Finset A) {L : ℕ} (i : Fin L) : A :=
  if h : i.val<S.card then ((Finset.equivFin S).symm ⟨i.val,h⟩).val else Classical.ofNonempty

lemma paddedChoice_covers {A : Type*} [Nonempty A] (S : Finset A) {L : ℕ}
    (hS : S.card≤L) (a : A) (ha : a ∈ S) : ∃ i : Fin L, paddedChoice S i=a := by
  let j := (Finset.equivFin S) ⟨a,ha⟩
  let i : Fin L := ⟨j.val,j.isLt.trans_le hS⟩
  refine ⟨i,?_⟩
  simp only [paddedChoice,i,dite_eq_left j.isLt]
  exact congrArg Subtype.val ((Finset.equivFin S).symm_apply_apply ⟨a,ha⟩)

variable {Name I : Type*} [Fintype I]

structure HintLists (Name I : Type*) [Fintype I] (q : ℕ) where
  first : (U : I → Equation Name) → (Fin q → Forms (FirstAlphabet U)) → Finset (FirstAlphabet U)
  second : (V : I → SecondQuestion Name) → (Fin q → Forms (SecondAlphabet V)) → Finset (SecondAlphabet V)

def HintLists.strategy {q L R : ℕ} (lists : HintLists Name I q) (z : Fin L × Fin R) :
    HintedStrategy Name I q where
  first U B := paddedChoice (lists.first U B) z.1
  second V B := paddedChoice (lists.second V B) z.2

def HintLists.matches {q : ℕ} (lists : HintLists Name I q)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (B : Fin q → Forms (SecondAlphabet (secondQuestion U hidden pos))) : Prop :=
  ∃ a ∈ lists.first U (fun j => formPullback (projection U hidden pos) (B j)),
    ∃ b ∈ lists.second (secondQuestion U hidden pos) B, projection U hidden pos a=b

lemma HintLists.matching_le_sum {q L R : ℕ} (lists : HintLists Name I q)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R)
    (U : I → Equation Name) (hidden : I → Bool) (pos : I → Fin 3)
    (B : Fin q → Forms (SecondAlphabet (secondQuestion U hidden pos))) :
    (if lists.matches U hidden pos B then (1 : ℝ) else 0) ≤
      ∑ z : Fin L × Fin R, if hintedAcceptance (lists.strategy z) U hidden pos B then 1 else 0 := by
  classical
  by_cases hm : lists.matches U hidden pos B
  · rw [ite_eq_left hm]
    obtain ⟨a,ha,b,hb,hab⟩ := hm
    obtain ⟨i,hi⟩ := paddedChoice_covers _ (hL _ _) a ha
    obtain ⟨j,hj⟩ := paddedChoice_covers _ (hR _ _) b hb
    have hwin : hintedAcceptance (lists.strategy (i,j)) U hidden pos B := by
      change projection U hidden pos (paddedChoice _ i)=paddedChoice _ j
      rw [hi,hj]
      exact hab
    have hs := Finset.single_le_sum (s := Finset.univ) (f := fun z : Fin L × Fin R =>
      if hintedAcceptance (lists.strategy z) U hidden pos B then (1 : ℝ) else 0)
      (fun _ _ => by positivity) (Finset.mem_univ (i,j))
    simpa only [ite_eq_left hwin] using hs
  · rw [ite_eq_right hm]
    exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem HintLists.shared_soundness [Fintype Name]
    {S : Type*} [Fintype S] [Nonempty S] (equations : S → Equation Name)
    (hsound : ∀ s : Name → F₂, equationFraction equations s ≤ 3/4)
    {q L R : ℕ} (lists : HintLists Name I q)
    (hL : ∀ U B, (lists.first U B).card≤L)
    (hR : ∀ V B, (lists.second V B).card≤R) (hidden : I → Bool) :
    (𝔼 w : I → S × Fin 3,
      𝔼 B : Fin q → Forms (SecondAlphabet
        (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
      if lists.matches (sampledEquations equations w) hidden (sampledPositions w) B
        then (1 : ℝ) else 0) ≤
      (L : ℝ)*(R : ℝ)*hintRate q ^ Fintype.card {i // hidden i=true} := by
  calc
    _ ≤ 𝔼 w : I → S × Fin 3,
        𝔼 B : Fin q → Forms (SecondAlphabet
          (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
        ∑ z : Fin L × Fin R,
          if hintedAcceptance (lists.strategy z) (sampledEquations equations w) hidden
            (sampledPositions w) B then (1 : ℝ) else 0 := by
      apply Finset.expect_le_expect
      intro w _
      exact Finset.expect_le_expect (fun B _ => lists.matching_le_sum hL hR _ hidden _ B)
    _ = ∑ z : Fin L × Fin R, 𝔼 w : I → S × Fin 3,
        𝔼 B : Fin q → Forms (SecondAlphabet
          (secondQuestion (sampledEquations equations w) hidden (sampledPositions w))),
          if hintedAcceptance (lists.strategy z) (sampledEquations equations w) hidden
            (sampledPositions w) B then (1 : ℝ) else 0 := by
      simp_rw [Finset.expect_sum_comm]
    _ ≤ ∑ _z : Fin L × Fin R, hintRate q ^ Fintype.card {i // hidden i=true} := by
      apply Finset.sum_le_sum
      intro z _
      exact shared_hint_soundness equations hsound (lists.strategy z) hidden
    _ = _ := by simp [mul_assoc]


open scoped BigOperators
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I : Type*} [Fintype I]

abbrev CoordinateSlot (E : Equation Name) := Fin (Module.finrank F₂ (alphabet E).direction) → F₂
abbrev FirstCoordinateSpace (U : I → Equation Name) := ∀ i, CoordinateSlot (U i)

def firstCoordinates (U : I → Equation Name) :
    FirstCoordinateSpace U ≃ᵃ[F₂] FirstAlphabet U :=
  (LinearEquiv.piCongrRight (fun i => coordinates (U i))).toAffineEquiv.trans
    (AffineEquiv.vaddConst F₂ (fun i => origin (U i)))

omit [Fintype I] in
@[simp] lemma firstCoordinates_apply (U : I → Equation Name)
    (v : FirstCoordinateSpace U) (i : I) :
    (firstCoordinates U v i).val = directionEmbedding (U i) (v i) + (origin (U i)).val := rfl

omit [Fintype I] in
lemma firstCoordinates_symm_apply (U : I → Equation Name) (a : FirstAlphabet U) (i : I) :
    (firstCoordinates U).symm a i = (alphabetCoordinates (U i)).symm (a i) := rfl

def formsTransport {V W A B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
    [AddCommGroup W] [Module F₂ W] [AddTorsor W B] (e : A ≃ᵃ[F₂] B) :
    Forms B ≃ₗ[F₂] Forms A where
  toFun f := f.comp e.toAffineMap
  invFun f := f.comp e.symm.toAffineMap
  left_inv f := by ext b; simp
  right_inv f := by ext a; simp
  map_add' f g := by ext a; rfl
  map_smul' c f := by ext a; rfl

def firstFormCoordinates (U : I → Equation Name) :
    (F₂ × (∀ i, Module.Dual F₂ (CoordinateSlot (U i)))) ≃ₗ[F₂] Forms (FirstAlphabet U) :=
  ((LinearEquiv.refl F₂ F₂).prodCongr
    (LinearMap.lsum F₂ (fun i => CoordinateSlot (U i)) F₂)).trans
    ((AffineMap.toConstProdLinearMap F₂).symm.trans (formsTransport (firstCoordinates U)).symm)

lemma firstFormCoordinates_apply (U : I → Equation Name) (κ : F₂)
    (b : ∀ i, Module.Dual F₂ (CoordinateSlot (U i))) (a : FirstAlphabet U) :
    firstFormCoordinates U (κ,b) a =
      (∑ i, b i ((alphabetCoordinates (U i)).symm (a i)))+κ := by
  change (∑ i, (b i).comp (LinearMap.proj i)) ((firstCoordinates U).symm a)+κ=_
  simp only [LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,
    firstCoordinates_symm_apply]

abbrev TupleCoordinateData (U : I → Equation Name) (d : ℕ) :=
  (Fin d → F₂) × (∀ i, OuterSmoothness.JointForms.Block
    (Module.finrank F₂ (alphabet (U i)).direction) d)

def tupleCoordinateSlice (U : I → Equation Name) (d : ℕ) (k : Fin d) :
    TupleCoordinateData U d →ₗ[F₂] (F₂ × (∀ i, Module.Dual F₂ (CoordinateSlot (U i)))) where
  toFun z := (z.1 k,fun i => z.2 i k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tupleCoordinateGenerator (U : I → Equation Name) (d : ℕ) :
    TupleCoordinateData U d →ₗ[F₂] (Fin d → Forms (FirstAlphabet U)) :=
  LinearMap.pi (fun k => (firstFormCoordinates U).toLinearMap.comp (tupleCoordinateSlice U d k))

lemma tupleCoordinateGenerator_surjective (U : I → Equation Name) (d : ℕ) :
    Function.Surjective (tupleCoordinateGenerator U d) := by
  intro f
  let z := fun k => (firstFormCoordinates U).symm (f k)
  refine ⟨(fun k => (z k).1,fun i k => (z k).2 i),?_⟩
  funext k
  exact (firstFormCoordinates U).apply_symm_apply (f k)

lemma uniform_tupleCoordinateGenerator (U : I → Equation Name) (d : ℕ)
    (f : (Fin d → Forms (FirstAlphabet U)) → ℝ) :
    (𝔼 z : TupleCoordinateData U d, f (tupleCoordinateGenerator U d z)) = 𝔼 L, f L :=
  IndependentSquares.expect_surjective_linear _ (tupleCoordinateGenerator_surjective U d) f

end MinUncut.Outer

end

end OAI
