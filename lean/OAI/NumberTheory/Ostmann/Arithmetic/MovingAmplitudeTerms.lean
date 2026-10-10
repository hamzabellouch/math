import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeIndex
import OAI.NumberTheory.Ostmann.Arithmetic.MovingTemplateTransfer

namespace OAI

/-! # The actual diagonal and integer off-diagonal of a prime amplitude -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem movingOneGiant_transform_tagged {I : Type*} [Fintype I]
    (X : ℕ) (p : I → ℕ) [NeZero X] [∀ i, NeZero (p i)]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (movingOneGiantModuli X p)
      (movingOneGiantFactors X p greg ggiant favorable) D s =
    movingTaggedTransform (movingOneGiantModuli X p)
      (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable D s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  cases i <;> rfl

local instance amplitudeSum_neZero {J I : Type*} (q : J → ℕ) (p : I → ℕ)
    [∀ j, NeZero (q j)] [∀ i, NeZero (p i)] (i : J ⊕ I) :
    NeZero (Sum.elim q p i) := by
  cases i <;> dsimp only [Sum.elim] <;> infer_instance

theorem movingOneGiant_pair_transform_tagged {I : Type*} [Fintype I]
    (X Y : ℕ) (p q : I → ℕ) [NeZero X] [NeZero Y]
    [∀ i, NeZero (p i)] [∀ i, NeZero (q i)]
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) (D : ℕ) (s : ℤ) :
    movingRegularTransform (Sum.elim (movingOneGiantModuli X p) (movingOneGiantModuli Y q))
      (movingSumFactors (movingOneGiantModuli X p) (movingOneGiantModuli Y q)
        (movingOneGiantFactors X p greg ggiant favorable)
        (movingOneGiantFactors Y q greg ggiant favorable)) D s =
    movingTaggedTransform (Sum.elim (movingOneGiantModuli X p) (movingOneGiantModuli Y q))
      (Sum.elim (Sum.elim (fun _ : Unit => true) (fun _ => false))
        (Sum.elim (fun _ : Unit => true) (fun _ => false))) greg ggiant favorable D s := by
  unfold movingRegularTransform movingTaggedTransform
  apply Finset.prod_congr rfl
  intro i _
  rcases i with (i | i) <;> cases i <;> rfl

noncomputable def movingAmplitudeDiagonal {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg I : Finset ℕ)
    (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) : ℝ :=
  let A := MovingAmplitudeIndex σ Pg n r m V
  let X := fun a : A => (a.1 : ℕ)
  let y := fun a : A => a.2.1
  let v := fun a : A => a.2.2.val
  let α := fun a : A => (movingAmplitudePrior Pg n r m V ρ ν a : ℂ)
  let W := movingTemplateTransferWeight value outside μ childBound pivotBound V F φ G
    n r m v α X y
  ∑ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) *
    ∑ p ∈ I, φ (Real.log p - G (n + 1)) *
      (pivotDiagonal (fun a => X a * ∏ i, value (y a i)) v
        (fun a => W u p a * movingTaggedTransform (movingOneGiantModuli (X a) (value ∘ y a))
          (Sum.elim (fun _ => true) (fun _ => false)) greg ggiant favorable
          (p * (∏ i, value (u i)) * outside.prod) (v a))).re

noncomputable def movingAmplitudeOffDiagonal {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ) (Pg I : Finset ℕ)
    (ρ : Pg → ℝ) (ν : MovingRegularSlot n r m → σ → ℝ)
    (greg ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool) : ℂ :=
  ∑ u : TreeLeafIndex n × Fin 4 → σ,
    (((∏ i, μ n (u i)) * (∏ i, value (u i) : ℕ) : ℝ) : ℂ) *
      ∑ s : transferFrequencyRange (V (n + 1)),
        ∑ a : MovingAmplitudeIndex σ Pg n r m V,
          ∑ b : MovingAmplitudeIndex σ Pg n r m V,
            (movingAmplitudePrior Pg n r m V ρ ν a : ℂ) *
              (movingAmplitudePrior Pg n r m V ρ ν b : ℂ) *
                movingTemplateIntegerFourierTerm value outside μ childBound pivotBound V F φ G
                  n r m I a.1 b.1 s.val a.2.1 b.2.1 greg ggiant favorable u a.2.2.val b.2.2.val

end Ostmann

end OAI
