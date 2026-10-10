import OAI.NumberTheory.PrimePackets.ShannonEntropy

namespace OAI

/-!
# Time reversal of entropy

Reversing a finite orbit name and shifting its starting point does not
change its Shannon entropy. This proves equality of
Kolmogorov--Sinai entropy for mutually inverse measure-preserving maps,
as used in EKL (2006), equation (3.2).
-/

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

/-- Reversal is a permutation of the finite word alphabet. -/
def reverseWordEquiv (α : Type*) (N : ℕ) : (Fin N → α) ≃ (Fin N → α) where
  toFun w j := w j.rev
  invFun w j := w j.rev
  left_inv w := by funext j; simp
  right_inv w := by funext j; simp

lemma inverse_orbitName {Y α : Type*} (T S : Y → Y)
    (hST : Function.LeftInverse S T) (P : Y → α) (N : ℕ) (y : Y) :
    orbitName S P N (T^[N - 1] y) =
      reverseWordEquiv α N (orbitName T P N y) := by
  funext j
  change P (S^[j.val] (T^[N - 1] y)) = P (T^[j.rev.val] y)
  congr 1
  have hN : N - 1 = j.val + (N - 1 - j.val) := by omega
  rw [hN, Function.iterate_add_apply]
  rw [(hST.iterate j.val) _]
  rw [Fin.val_rev]
  exact congrArg (fun m : ℕ => T^[m] y) (by omega)

/-- Finite block entropies agree exactly under time reversal. -/
theorem orbitEntropy_inverse {Y α : Type*} [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) (N : ℕ) :
    observationEntropy μ (orbitName S P N) =
      observationEntropy μ (orbitName T P N) := by
  calc
    observationEntropy μ (orbitName S P N) =
        observationEntropy μ (fun y => orbitName S P N (T^[N - 1] y)) :=
      (observationEntropy_comp_preserving μ _
        (orbitName_measurable_fiber hS hP N) (hT.iterate (N - 1))).symm
    _ = observationEntropy μ (fun y => reverseWordEquiv α N (orbitName T P N y)) := by
      congr 1
      funext y
      exact inverse_orbitName T S hST P N y
    _ = _ := observationEntropy_equiv μ _ _

/-- Equality holds for every finite observation, before taking the supremum. -/
theorem observationEntropyRate_inverse {Y α : Type*}
    [MeasurableSpace Y] [Fintype α]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y = a}) :
    observationEntropyRate μ S P = observationEntropyRate μ T P := by
  unfold observationEntropyRate
  congr 2
  funext N
  rw [orbitEntropy_inverse μ T S hT hS hST P hP]

/-- Entropy is invariant under reversing an invertible measure-preserving map. -/
theorem measureEntropy_inverse {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (T S : Y → Y)
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : Function.LeftInverse S T) :
    measureEntropy μ S = measureEntropy μ T := by
  unfold measureEntropy
  congr 1
  funext k
  congr 1
  funext P
  congr 1
  funext hP
  rw [observationEntropyRate_inverse μ T S hT hS hST P hP]

end DukePrimeDegree

end

end OAI
