import OAI.NumberTheory.Ostmann.Supply.ResidueKernel
import OAI.NumberTheory.Ostmann.Supply.TensorKernel

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ℕ) [∀ i, NeZero (p i)]

def residueVectors (S : ∀ i, Finset (ZMod (p i))) (a : ℕ) :
    ∀ i, EuclideanSpace ℂ (ZMod (p i)) :=
  fun i => centeredProjection (S i) (EuclideanSpace.single (a : ZMod (p i)) 1)

theorem residueTensorKernel_eq (A : Finset ℕ)
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ a ∈ A, ∀ i, (a : ZMod (p i)) ∈ S i) :
    (∑ a ∈ A, ∑ b ∈ A,
      ∏ i, ((p i : ℂ)*(if (a : ZMod (p i)) = (b : ZMod (p i)) then 1 else 0)-1)) =
    ∑ t : Finset ι,
      ((∏ i ∈ t, (p i : ℝ)) * ∏ i ∈ tᶜ, complementRatio (S i) : ℝ) *
        subsetRawEnergy A (residueVectors p S) t := by
  rw [← tensorKernel_expansion]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.prod_congr rfl
  intro i hi
  exact primeKernel_centered (S i) _ _ (hS a ha i) (hS b hb i)

theorem residueTensorKernel_lower (A : Finset ℕ)
    (S : ∀ i, Finset (ZMod (p i)))
    (hSn : ∀ i, (S i).Nonempty)
    (hS : ∀ a ∈ A, ∀ i, (a : ZMod (p i)) ∈ S i) :
    (A.card : ℝ)^2 * (∏ i, complementRatio (S i)) ≤
    (∑ a ∈ A, ∑ b ∈ A,
      ∏ i, ((p i : ℂ)*(if (a : ZMod (p i)) = (b : ZMod (p i)) then 1 else 0)-1)).re := by
  have h := tensorKernel_lower A (residueVectors p S)
    (fun i => complementRatio (S i)) (fun i => (p i : ℝ))
    (fun i => complementRatio_nonneg (S i) (hSn i)) (fun i => Nat.cast_nonneg _)
  have he : (∑ a ∈ A, ∑ b ∈ A,
        ∏ i, ((p i : ℂ)*(if (a : ZMod (p i)) = (b : ZMod (p i)) then 1 else 0)-1)) =
      ∑ a ∈ A, ∑ b ∈ A, ∏ i,
        ((p i : ℂ)*inner ℂ (residueVectors p S a i) (residueVectors p S b i) +
          complementRatio (S i)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.prod_congr rfl
    intro i hi
    exact primeKernel_centered (S i) _ _ (hS a ha i) (hS b hb i)
  rw [he]
  exact h

end Ostmann.Supply

end

end OAI
