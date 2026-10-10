import OAI.LinearAlgebra.MatrixMultiplication.Completion.ColorLaws

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionProductLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

def centerWordEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → ColorSlice S center) ≃
      {w : Fin m → Leaf S // completionEvent S center center m w} where
  toFun w := ⟨fun i => (w i).val, by
    constructor
    · simpa [raisedFlag] using (fun i => (w i).property)
    · exact fun i => Or.inl (w i).property⟩
  invFun w := fun i => ⟨w.val i, by
    have hall : ∀ j, leafColor S (w.val j) = center := by
      simpa [raisedFlag] using w.property.1
    exact hall i⟩
  left_inv w := by
    funext i
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

def centerCompletionEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → ColorSlice S center) ≃ ColorSlice (complete S center m) center :=
  (centerWordEquiv S center m).trans (conditionalLeafEquiv S center center m).symm

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem centerCompletionEquiv_slots (S : FlaggedTensor X Y Z) (center : Color)
    (m : ℕ) (w : Fin m → ColorSlice S center) :
    slot S center m ((centerCompletionEquiv S center m) w).val =
      fun i => (w i).val := by
  funext i
  apply Subtype.ext
  rfl

def centerCompletionLaw (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) :
    FiniteLaw (ColorSlice (complete S center m) center) :=
  transport (centerCompletionEquiv S center m)
    (independentProduct (fun _ : Fin m => p))

theorem centerCompletionLaw_mass (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (w : Fin m → ColorSlice S center) :
    (centerCompletionLaw S center p m).mass ((centerCompletionEquiv S center m) w) =
      ∏ i, p.mass (w i) :=
  transport_mass (centerCompletionEquiv S center m) _ w

theorem centerCompletionLaw_entropy (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) :
    finiteEntropy (centerCompletionLaw S center p m).mass =
      (m : ℝ) * finiteEntropy p.mass := by
  rw [centerCompletionLaw, transport_entropy, independentProduct_entropy]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem centerCompletionLaw_map_mass {B : Type*} [Fintype B]
    (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (f : Leaf S → B) (y : Fin m → B) :
    ((centerCompletionLaw S center p m).map
      (fun a i => f (slot S center m a.val i))).mass y =
      ∏ i, (p.map (fun a => f a.val)).mass (y i) := by
  rw [FiniteLaw.map_mass]
  calc
    (∑ a, if (fun i => f (slot S center m a.val i)) = y then
        (centerCompletionLaw S center p m).mass a else 0) =
        ∑ w : Fin m → ColorSlice S center,
          if (fun i => f (w i).val) = y then ∏ i, p.mass (w i) else 0 := by
      rw [← (centerCompletionEquiv S center m).sum_comp
        (fun a => if (fun i => f (slot S center m a.val i)) = y then
          (centerCompletionLaw S center p m).mass a else 0)]
      simp only [centerCompletionEquiv_slots, centerCompletionLaw_mass]
    _ = _ := by
      simpa only [FiniteLaw.map_mass, independentProduct_mass] using
        independentProduct_map_mass (fun _ : Fin m => p)
          (fun _ a => f a.val) y

theorem completionEvent_same_zero_mass (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) :
    eventMass (iidColorLaw S center center p p m 0 (by norm_num) (by norm_num))
      (completionEvent S center center m) = 1 := by
  unfold eventMass
  rw [← (centerWordEquiv S center m).sum_comp
    (fun w => (iidColorLaw S center center p p m 0 (by norm_num) (by norm_num)).mass w.val)]
  calc
    _ = ∑ w : Fin m → ColorSlice S center,
        (independentProduct (fun _ : Fin m => p)).mass w := by
      apply Finset.sum_congr rfl
      intro w _
      change (∏ i, (colorMix S center center p p 0 (by norm_num) (by norm_num)).mass
        (w i).val) = ∏ i, p.mass (w i)
      apply Finset.prod_congr rfl
      intro i _
      rw [colorMix_mass]
      simp only [zero_mul, sub_zero, one_mul, zero_add]
      exact p.map_mass_apply Subtype.val Subtype.val_injective (w i)
    _ = 1 := (independentProduct (fun _ : Fin m => p)).total

theorem conditionalCompletionLaw_same_zero_mass
    (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (hm : 0 < m)
    (w : Fin m → ColorSlice S center) :
    (conditionalCompletionLaw S center center p p m hm 0 (by norm_num) (by norm_num)).mass
        ((centerCompletionEquiv S center m) w) = ∏ i, p.mass (w i) := by
  rw [conditionalCompletionLaw_mass, completionEvent_same_zero_mass, div_one,
    centerCompletionEquiv_slots]
  change (∏ i, (colorMix S center center p p 0 (by norm_num) (by norm_num)).mass
    (w i).val) = ∏ i, p.mass (w i)
  apply Finset.prod_congr rfl
  intro i _
  rw [colorMix_mass]
  simp only [zero_mul, sub_zero, one_mul, zero_add]
  exact p.map_mass_apply Subtype.val Subtype.val_injective (w i)

theorem conditionalCompletionLaw_same_zero_entropy
    (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) (hm : 0 < m) :
    finiteEntropy
      (conditionalCompletionLaw S center center p p m hm 0 (by norm_num) (by norm_num)).mass =
      (m : ℝ) * finiteEntropy p.mass := by
  have hmass :
      (conditionalCompletionLaw S center center p p m hm 0 (by norm_num) (by norm_num)).mass =
        (centerCompletionLaw S center p m).mass := by
    funext a
    obtain ⟨w, rfl⟩ := (centerCompletionEquiv S center m).surjective a
    rw [conditionalCompletionLaw_same_zero_mass, centerCompletionLaw_mass]
  rw [hmass, centerCompletionLaw_entropy]

end MatrixMultiplication.CompletionColorLaws

end

end OAI
