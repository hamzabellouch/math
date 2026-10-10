import OAI.Computability.PerfectCompleteness.Algebra.LowerCrossRank
import OAI.Computability.PerfectCompleteness.Foundations.DualQuotientRowsLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RestrictionRowsLaw

namespace OAI

section

namespace PerfectCompleteness.RestrictionCrossLaw

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Foundations.Games
open RestrictionRowsLaw DualQuotientRows

variable {E C I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 C) (b : Module.Basis I F2 C')

def rowPairEquiv (m : Nat) :
    ((Fin m ⊕ Fin m) → Module.Dual F2 (E ⧸ W)) ≃ₗ[F2]
      ((Fin m → W.dualAnnihilator) × (Fin m → W.dualAnnihilator)) :=
  (LinearEquiv.piCongrRight
    (fun _ : Fin m ⊕ Fin m => quotientRowEquiv W)).trans
      (LinearEquiv.sumArrowLequivProdArrow
        (Fin m) (Fin m) F2 W.dualAnnihilator)

variable {m : Nat} (sel : (Fin m ⊕ Fin m) → I)

def selectedPair : Parameter W C' →ₗ[F2]
    ((Fin m → W.dualAnnihilator) × (Fin m → W.dualAnnihilator)) :=
  (rowPairEquiv W m).toLinearMap.comp (selectedRowsLinear W C' b sel)

omit [Fintype I] in
@[simp] theorem selectedPair_fst (A : Parameter W C') (i : Fin m) :
    (selectedPair W C' b sel A).1 i =
      quotientRowEquiv W (rowsLinear W C' b A (sel (Sum.inl i))) := rfl

omit [Fintype I] in
@[simp] theorem selectedPair_snd (A : Parameter W C') (j : Fin m) :
    (selectedPair W C' b sel A).2 j =
      quotientRowEquiv W (rowsLinear W C' b A (sel (Sum.inr j))) := rfl

theorem selectedPair_surjective (hsel : Function.Injective sel) :
    Function.Surjective (selectedPair W C' b sel) :=
  (rowPairEquiv W m).surjective.comp (selectedRowsLinear_surjective W C' b sel hsel)

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro p
  change (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ)) =
    1 / (Fintype.card (A × B) : ℝ)
  simp only [Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]

theorem selectedPair_law [Fintype (Parameter W C')] [Fintype W.dualAnnihilator]
    (hsel : Function.Injective sel) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward (selectedPair W C' b sel) =
      (FiniteDistribution.uniform (Fin m → W.dualAnnihilator)).product
        (FiniteDistribution.uniform (Fin m → W.dualAnnihilator)) := by
  rw [uniform_product]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (selectedPair W C' b sel) (selectedPair_surjective W C' b sel hsel)

omit [Fintype I] in
theorem coordinate_translate_left (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) (A : Parameter W C') (i : Fin m) :
    (coordinates (sel (Sum.inl i))).comp (translate W C' X A) =
      (coordinates (sel (Sum.inl i))).comp X +
        ((selectedPair W C' b sel A).1 i : Module.Dual F2 E) := by
  simpa only [affineRow, selectedPair_fst, quotientRowEquiv_val] using
    coordinate_translate W C' b coordinates hcoordinates X A (sel (Sum.inl i))

omit [Fintype I] in
theorem coordinate_translate_right (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) (A : Parameter W C') (j : Fin m) :
    (coordinates (sel (Sum.inr j))).comp (translate W C' X A) =
      (coordinates (sel (Sum.inr j))).comp X +
        ((selectedPair W C' b sel A).2 j : Module.Dual F2 E) := by
  simpa only [affineRow, selectedPair_snd, quotientRowEquiv_val] using
    coordinate_translate W C' b coordinates hcoordinates X A (sel (Sum.inr j))

theorem crossMatrix_law [Fintype (Parameter W C')] [Fintype W.dualAnnihilator]
    (hsel : Function.Injective sel)
    (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C)
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E)) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (Γ := Matrix (Fin m) (Fin m) F2)
        (fun A i j =>
          F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
            ((coordinates (sel (Sum.inr j))).comp (translate W C' X A))) =
      ((FiniteDistribution.uniform (Fin m → W.dualAnnihilator)).product
        (FiniteDistribution.uniform (Fin m → W.dualAnnihilator))).pushforward
          (Γ := Matrix (Fin m) (Fin m) F2)
          (fun p => LowerCrossRank.crossMatrix F W.dualAnnihilator
            (fun i => (coordinates (sel (Sum.inl i))).comp X)
            (fun j => (coordinates (sel (Sum.inr j))).comp X) p.1 p.2) := by
  have hcross :
      (fun (A : Parameter W C') =>
        (fun i j => F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
          ((coordinates (sel (Sum.inr j))).comp (translate W C' X A)) :
            Matrix (Fin m) (Fin m) F2)) =
      (fun A => LowerCrossRank.crossMatrix F W.dualAnnihilator
        (fun i => (coordinates (sel (Sum.inl i))).comp X)
        (fun j => (coordinates (sel (Sum.inr j))).comp X)
        (selectedPair W C' b sel A).1 (selectedPair W C' b sel A).2) := by
    funext A i j
    rw [coordinate_translate_left W C' b sel coordinates hcoordinates X A i,
      coordinate_translate_right W C' b sel coordinates hcoordinates X A j]
    rfl
  rw [hcross, ← FiniteDistribution.pushforward_comp
    (FiniteDistribution.uniform (Parameter W C')) (selectedPair W C' b sel)
    (fun p => LowerCrossRank.crossMatrix F W.dualAnnihilator
      (fun i => (coordinates (sel (Sum.inl i))).comp X)
      (fun j => (coordinates (sel (Sum.inr j))).comp X) p.1 p.2),
    selectedPair_law W C' b sel hsel]

end
end PerfectCompleteness.RestrictionCrossLaw

end

end OAI
