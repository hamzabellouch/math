import OAI.NumberTheory.TwoPoint.Bounds.FiniteLawMapping
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDifferenceLaw

namespace OAI

/-! The padding experiment has tilted prime availability `5/(p+4)` and,
given availability, two independent selections of probability `4/5`.
Its exact difference pushforward is the manuscript's three-point law. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def booleanLaw (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FiniteLaw Bool where
  weight b := if b then q else 1 - q
  nonneg b := by cases b <;> simp [hq0, sub_nonneg.mpr hq1]
  total := by simp

noncomputable def paddingAvailabilityLaw (p : ℕ) (hp : 2 ≤ p) : FiniteLaw Bool :=
  booleanLaw (5 / ((p : ℝ) + 4)) (by positivity)
    (by
      apply (div_le_one (by positivity)).mpr
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
      linarith)

noncomputable def paddingSelectionLaw (a : Bool) : FiniteLaw Bool :=
  booleanLaw (if a then 4 / 5 else 0) (by cases a <;> norm_num)
    (by cases a <;> norm_num)

noncomputable def paddingPairLocal (p : ℕ) (hp : 2 ≤ p) : FiniteLaw (Bool × (Bool × Bool)) :=
  (paddingAvailabilityLaw p hp).dependentProduct
    (fun a => (paddingSelectionLaw a).product (paddingSelectionLaw a))

def paddingPairDifference (x : Bool × (Bool × Bool)) : Fin 3 :=
  if x.2.1 = x.2.2 then 0 else if x.2.1 then 1 else 2

lemma paddingPairLocal_average (p : ℕ) (hp : 2 ≤ p) (F : Fin 3 → ℝ) :
    (paddingPairLocal p hp).average (fun x => F (paddingPairDifference x)) =
      (paddingStepLaw p hp).average F := by
  have hd : (p : ℝ) + 4 ≠ 0 := by positivity
  simp only [FiniteLaw.average, paddingPairLocal, FiniteLaw.dependentProduct,
    paddingAvailabilityLaw, paddingSelectionLaw, booleanLaw, FiniteLaw.product,
    Fintype.sum_prod_type, Fintype.sum_bool, paddingPairDifference,
    paddingStepLaw, paddingDifferenceAtom, Fin.sum_univ_three]
  norm_num
  field_simp
  ring

lemma paddingPairLocal_fiber (p : ℕ) (hp : 2 ≤ p) (e : Fin 3) :
    (paddingPairLocal p hp).probability (fun x => paddingPairDifference x = e) =
      (paddingStepLaw p hp).weight e := by
  have hh := paddingPairLocal_average p hp (fun x => if x = e then 1 else 0)
  simpa [FiniteLaw.probability, FiniteLaw.average] using hh

noncomputable def paddingPairLaw (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p) :
    FiniteLaw (Q → Bool × (Bool × Bool)) :=
  FiniteLaw.independent (fun p : Q => paddingPairLocal p (hQ p p.property))

lemma paddingPairLaw_average (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (F : (Q → Fin 3) → ℝ) :
    (paddingPairLaw Q hQ).average (fun x => F (fun p => paddingPairDifference (x p))) =
      (paddingDifferenceLaw Q hQ).average F :=
  FiniteLaw.independent_average_map
    (fun p : Q => paddingPairLocal p (hQ p p.property))
    (fun p : Q => paddingStepLaw p (hQ p p.property))
    (fun _ => paddingPairDifference)
    (fun p => paddingPairLocal_fiber p (hQ p p.property)) F

end TwoPointCorrelations

end OAI
