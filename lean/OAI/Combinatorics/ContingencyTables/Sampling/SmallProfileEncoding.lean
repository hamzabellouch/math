import OAI.Combinatorics.ContingencyTables.Sampling.SmallBalancedEncoding
import OAI.Combinatorics.ContingencyTables.Transport.FiniteSupportVariance

namespace OAI

/-! # The variance encoding retains exactly the positive physical states -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev VarianceEncoding (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) :=
  (Fin (Fintype.card (Cells small)) → Fin (U+1)) ⊕ PositiveDefects small B r c L

noncomputable def encodeProfile (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    VarianceEncoding small B r c L U → Profiles small B
  | .inl x => ⟨choiceProfile small B U hB (wordChoices small U x),
      Or.inl (choiceProfile_balanced small B U hB _)⟩
  | .inr z => ⟨z.val,Or.inr z.property.1⟩

lemma encodeProfile_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) :
    Function.Injective (encodeProfile small B r c L U hB) := by
  intro x y he
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      apply congrArg Sum.inl
      apply (wordChoices small U).injective
      apply rawChoice_injective small U
      exact congrArg (fun z : Profiles small B => naturalProfile z.val) he
    | inr y =>
      have hp := choiceProfile_balanced small B U hB (wordChoices small U x)
      have hxy := congrArg (fun z : Profiles small B => naturalProfile z.val) he
      change rawChoice small U (wordChoices small U x)=naturalProfile y.val at hxy
      have hb : Balanced small B (naturalProfile y.val) := by rwa [← hxy]
      exact False.elim (balanced_not_defect small B _ hb y.property.1)
  | inr x =>
    cases y with
    | inl y =>
      have hp := choiceProfile_balanced small B U hB (wordChoices small U y)
      have hxy := congrArg (fun z : Profiles small B => naturalProfile z.val) he
      change naturalProfile x.val=rawChoice small U (wordChoices small U y) at hxy
      have hb : Balanced small B (naturalProfile x.val) := by rwa [hxy]
      exact False.elim (balanced_not_defect small B _ hb x.property.1)
    | inr y =>
      apply congrArg Sum.inr
      apply Subtype.ext
      exact congrArg (fun z : Profiles small B => z.val) he

/-- Every omitted physical profile has zero completion weight. -/
lemma outside_encoding_weight_zero (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (p : Profiles small B)
    (hp : p ∉ Set.range (encodeProfile small B r c L U hB)) :
    hardMarginal small B r c L (naturalProfile p.val)=0 := by
  have hn : ¬0 < hardMarginal small B r c L (naturalProfile p.val) := by
    intro hpos
    apply hp
    rcases p.property with hb|hd
    · refine ⟨.inl (balancedWord small B U hB p.val),?_⟩
      apply Subtype.ext
      apply naturalProfile_injective small B
      exact balancedWord_profile small B U hB p.val hb
    · exact ⟨.inr ⟨p.val,hd,hpos⟩,rfl⟩
  exact le_antisymm (le_of_not_gt hn) (hardMarginal_nonnegative _ _ _ _ _ _)

/-- The completed graph variance proof concerns the literal bounded
physical profiles; the auxiliary encoding drops only zero-mass defects. -/
theorem encoding_variance_eq (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (H : SmallProfile small → ℝ) :
    variance
      (Sum.elim (wordWeight small B r c L U)
        (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)))
      (Sum.elim (wordObservable small U H) (fun z => H (naturalProfile z.val)))=
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
        (fun z => H (naturalProfile z.val)) := by
  convert variance_support_embedding (encodeProfile small B r c L U hB)
    (encodeProfile_injective small B r c L U hB)
    (fun z => hardMarginal small B r c L (naturalProfile z.val))
    (outside_encoding_weight_zero small B r c L U hB)
    (fun z => H (naturalProfile z.val)) using 1
  congr 1 <;> funext x <;> cases x <;> rfl

end ContingencyTables.SmallGraphProfiles

end OAI
