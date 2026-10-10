import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Selection.Selection

namespace OAI

namespace Balanced.Selection

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {I V : Type*} [Fintype I] [Fintype V]
variable {G : Input I V} (law : OutputLaw G)

theorem successMass_nonnegative : 0 ≤ successMass law :=
  Finset.sum_nonneg (fun a _ => law.nonnegative a)

theorem successMass_le_one : successMass law ≤ 1 := law.mass_le_one

theorem outcomeWeight_nonnegative (o : Option (I → V)) : 0 ≤ outcomeWeight law o := by
  cases o with
  | none => exact sub_nonneg.mpr law.mass_le_one
  | some a => exact law.nonnegative a

theorem sum_outcomeWeight : (∑ o, outcomeWeight law o) = 1 := by
  rw [Fintype.sum_option]
  simp only [outcomeWeight, successMass]
  ring

def OutputLaw.toPMF : PMF (Option (I → V)) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (outcomeWeight law o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => outcomeWeight_nonnegative law o)]
    rw [sum_outcomeWeight]
    simp)

@[simp] theorem toPMF_none : law.toPMF none = ENNReal.ofReal (1 - successMass law) := rfl

@[simp] theorem toPMF_some (a : I → V) : law.toPMF (some a) = ENNReal.ofReal (law.weight a) := rfl

theorem toPMF_some_real (a : I → V) : (law.toPMF (some a)).toReal = law.weight a :=
  ENNReal.toReal_ofReal (law.nonnegative a)

theorem weight_eq_zero_of_not_transversal (a : I → V)
    (ha : ¬ IsIndependentTransversal G a) : law.weight a = 0 := by
  apply le_antisymm _ (law.nonnegative a)
  by_contra h
  exact ha (law.supported a (lt_of_not_ge h))

theorem positive_output_is_transversal (a : I → V)
    (ha : 0 < law.toPMF (some a)) : IsIndependentTransversal G a := by
  apply law.supported a
  exact ENNReal.ofReal_pos.mp ha

theorem returned_finset_probability (E : Finset (I → V)) :
    (law.toPMF.toOuterMeasure (E.image some : Finset (Option (I → V)))).toReal =
      ∑ a ∈ E, law.weight a := by
  classical
  rw [PMF.toOuterMeasure_apply_finset]
  rw [Finset.sum_image]
  · simp only [toPMF_some]
    rw [ENNReal.toReal_sum (fun a _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl (fun a _ => ENNReal.toReal_ofReal (law.nonnegative a))
  · intro a _ b _ h
    exact Option.some.inj h

theorem success_probability :
    (law.toPMF.toOuterMeasure
      ((Finset.univ : Finset (I → V)).image some : Finset (Option (I → V)))).toReal =
      successMass law :=
  returned_finset_probability law Finset.univ

theorem cylinder_probability (J : Finset I) (prescribed : I → V) :
    (law.toPMF.toOuterMeasure
      ((Finset.univ.filter (fun a : I → V => ∀ i ∈ J, a i = prescribed i)).image some :
        Finset (Option (I → V)))).toReal = cylinderMass law J prescribed := by
  classical
  exact returned_finset_probability law _

theorem impossible_cylinder_zero (J : Finset I) (prescribed : I → V)
    (h : ∀ a, (∀ i ∈ J, a i = prescribed i) → ¬ IsIndependentTransversal G a) :
    cylinderMass law J prescribed = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a ha
  exact weight_eq_zero_of_not_transversal law a (h a (Finset.mem_filter.mp ha).2)

theorem occupancy_failure_probability
    {q : ℕ} {P D L : Type*} [Fintype P] [Fintype D] [Fintype L]
    (A : FiniteAffine.Plane q P D L) (line : V → L) (T : L → Finset P) (ρ : ℝ) :
    (law.toPMF.toOuterMeasure
      ((Finset.univ.filter (fun a : I → V =>
        ∃ ℓ : L, ((finalTracked A line T a ℓ).card : ℝ) < ρ * q)).image some :
          Finset (Option (I → V)))).toReal = occupancyFailureMass law A line T ρ := by
  classical
  exact returned_finset_probability law _

end
end Balanced.Selection

end OAI
