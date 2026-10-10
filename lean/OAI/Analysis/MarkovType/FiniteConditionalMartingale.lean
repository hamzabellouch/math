import OAI.Analysis.MarkovType.FiniteConditionalAverage
import OAI.Analysis.MarkovType.FiniteMartingaleBasic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity
namespace FinitePartitionFiltration

variable {Ω : Type*} (F : FinitePartitionFiltration Ω)

def quotientCoarsening {i j : ℕ} (hij : i ≤ j) :
    Quotient (F.part j) → Quotient (F.part i) :=
  Quotient.lift (Quotient.mk (F.part i))
    (fun _ _ h => Quotient.sound (F.refines hij h))

@[simp] theorem quotientCoarsening_mk {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    F.quotientCoarsening hij (Quotient.mk (F.part j) ω) =
      Quotient.mk (F.part i) ω := rfl

theorem quotientCoarsening_comp {i j : ℕ} (hij : i ≤ j) :
    F.quotientCoarsening hij ∘ Quotient.mk (F.part j) =
      Quotient.mk (F.part i) := rfl

variable [Fintype Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) : Ω → E :=
  μ.conditionalAverage (Quotient.mk (F.part j)) f

theorem adaptedAt_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) :
    F.AdaptedAt j (F.conditionalProcess μ f j) := by
  intro ω η hωη
  exact μ.conditionalAverage_eq_of_key_eq (Quotient.mk (F.part j)) f
    (Quotient.sound hωη)

theorem fiberSum_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) (a : Quotient (F.part i)) :
    μ.fiberSum (Quotient.mk (F.part i)) (F.conditionalProcess μ f j) a =
      μ.fiberSum (Quotient.mk (F.part i)) f a := by
  have h := μ.fiberSum_conditionalAverage_comp (Quotient.mk (F.part j))
    (F.quotientCoarsening hij) f a
  rw [F.quotientCoarsening_comp hij] at h
  exact h

theorem conditionalAverage_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    μ.conditionalAverage (Quotient.mk (F.part i)) (F.conditionalProcess μ f j) ω =
      F.conditionalProcess μ f i ω := by
  exact congrArg (fun z : E =>
    (μ.fiberMass (Quotient.mk (F.part i)) (Quotient.mk (F.part i) ω))⁻¹ • z)
      (F.fiberSum_conditionalProcess μ f hij (Quotient.mk (F.part i) ω))

theorem atom_sum_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) (a : Ω) :
    (∑ ω, if (F.part i).r ω a then
      μ.mass ω • F.conditionalProcess μ f j ω else 0) =
      ∑ ω, if (F.part i).r ω a then μ.mass ω • f ω else 0 := by
  simpa only [FiniteLaw.fiberSum, FiniteLaw.fiberWeight, Quotient.eq,
    ite_smul, zero_smul] using
    F.fiberSum_conditionalProcess μ f hij (Quotient.mk (F.part i) a)

theorem hasZeroConditionalSum_conditionalProcess_sub (μ : FiniteLaw Ω) (f : Ω → E)
    {i j : ℕ} (hij : i ≤ j) :
    HasZeroConditionalSum μ (F.part i)
      (fun ω => F.conditionalProcess μ f j ω - F.conditionalProcess μ f i ω) := by
  intro a
  calc
    _ = (∑ ω, if (F.part i).r ω a then
        μ.mass ω • F.conditionalProcess μ f j ω else 0) -
        ∑ ω, if (F.part i).r ω a then
          μ.mass ω • F.conditionalProcess μ f i ω else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : (F.part i).r ω a <;>
        simp only [h, ite_true, ite_false, smul_sub, sub_zero]
    _ = 0 := by
      rw [F.atom_sum_conditionalProcess μ f hij,
        F.atom_sum_conditionalProcess μ f (i := i) le_rfl, sub_self]

theorem isMartingaleUpTo_conditionalProcess (μ : FiniteLaw Ω) (f : Ω → E) (N : ℕ) :
    F.IsMartingaleUpTo μ (F.conditionalProcess μ f) N := by
  constructor
  · intro j _
    exact F.adaptedAt_conditionalProcess μ f j
  · intro j hj _
    simpa only [finiteDifference, ite_eq_right (Nat.ne_of_gt hj)] using
      F.hasZeroConditionalSum_conditionalProcess_sub μ f (Nat.sub_le j 1)

theorem finiteL2Norm_conditionalProcess_le (μ : FiniteLaw Ω) (f : Ω → E) (j : ℕ) :
    finiteL2Norm μ (F.conditionalProcess μ f j) ≤ finiteL2Norm μ f := by
  apply Real.sqrt_le_sqrt
  simpa only [conditionalProcess, Real.rpow_two] using
    μ.expect_norm_conditionalAverage_rpow_le (Quotient.mk (F.part j)) f
      (q := (2 : ℝ)) (by norm_num)

end FinitePartitionFiltration
end MarkovSuperreflexivity

end

end OAI
