import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Counts

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section
namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem shapeCounts_fiber {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) :
    shapeCounts code weight u = ∑ i : {i : I // code i = u}, weight i.val := by
  unfold shapeCounts
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro i; simp) weight

def shapeCountFiberEquiv {I : Type*} [Fintype I] (code : I → JointPopulation.Shape)
    (weight : I → ℕ) (u : JointPopulation.Shape) :
    Fin (shapeCounts code weight u) ≃
      (Σ i : {i : I // code i = u}, Fin (weight i.val)) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma, shapeCounts_fiber])

abbrev InitialPlacement (K : ℕ) := Initial K × Placement

abbrev InitialShapeFiber {K : ℕ} (j : Fin K) (u : JointPopulation.Shape) :=
  {p : Fin sortedInitial.length × Placement // rootShape (j, p.1) p.2 = u}

def initialClassPositionEquiv {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape) :
    Fin (initialJointCounts allocation dilation j u) ≃
      (Σ p : InitialShapeFiber j u,
        Fin (population allocation dilation (.initial (j, p.val.1), p.val.2))) :=
  shapeCountFiberEquiv _ _ u

theorem initialClassPosition_shape {K : ℕ} (allocation : Allocation) (dilation : ℕ)
    (j : Fin K) (u : JointPopulation.Shape)
    (i : Fin (initialJointCounts allocation dilation j u)) :
    rootShape (j, (initialClassPositionEquiv allocation dilation j u i).1.val.1)
      (initialClassPositionEquiv allocation dilation j u i).1.val.2 = u :=
  (initialClassPositionEquiv allocation dilation j u i).1.property

def initialStateEquiv (K : ℕ) : State K 0 ≃ InitialPlacement K where
  toFun h := by
    rcases h with ⟨⟨h, phi⟩, hr⟩
    cases h with
    | initial g => exact (g, phi)
    | afterA a => have := hr.1; dsimp [resident] at hr; omega
    | afterB b => have := hr.1; dsimp [resident] at hr; omega
    | partC c => dsimp [resident] at hr; omega
    | afterC c => dsimp [resident] at hr; omega
  invFun h := ⟨(.initial h.1, h.2), fun _ => Nat.zero_le _⟩
  left_inv h := by
    rcases h with ⟨⟨h, phi⟩, hr⟩
    cases h with
    | initial g => rfl
    | afterA a => have := hr.1; dsimp [resident] at hr; omega
    | afterB b => have := hr.1; dsimp [resident] at hr; omega
    | partC c => dsimp [resident] at hr; omega
    | afterC c => dsimp [resident] at hr; omega
  right_inv h := rfl

end MatrixMultiplication.AllFieldHistory

end

end OAI
