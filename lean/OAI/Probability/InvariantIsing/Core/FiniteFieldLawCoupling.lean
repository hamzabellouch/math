import OAI.Probability.InvariantIsing.Core.FiniteFieldAtomMass

namespace OAI

/-! Two positive finite representations of the same field law have a
coupling supported on identical field values. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def sameFieldCoupling {A B : Type*} [Fintype A]
    (γ c : A → ℝ) (δ d : B → ℝ) (a : A) (j : B) : ℝ :=
  if c a=d j then γ a*δ j/fieldAtomMass γ c (c a) else 0

lemma sameFieldCoupling_nonneg {A B : Type*} [Fintype A]
    (γ c : A → ℝ) (δ d : B → ℝ) (hγ : ∀ a, 0 < γ a) (hδ : ∀ j, 0 ≤ δ j) (a : A) (j : B) :
    0 ≤ sameFieldCoupling γ c δ d a j := by
  unfold sameFieldCoupling
  split_ifs
  · exact div_nonneg (mul_nonneg (hγ a).le (hδ j)) (fieldAtomMass_pos_at γ c hγ a).le
  · rfl

lemma sameFieldCoupling_row {A B : Type*} [Fintype A] [Fintype B]
    (γ c : A → ℝ) (δ d : B → ℝ) (hγ : ∀ a, 0 < γ a)
    (he : ∀ x, fieldAtomMass γ c x=fieldAtomMass δ d x) (a : A) :
    ∑ j, sameFieldCoupling γ c δ d a j=γ a := by
  have hw j : sameFieldCoupling γ c δ d a j=
      (γ a/fieldAtomMass γ c (c a))*(if d j=c a then δ j else 0) := by
    unfold sameFieldCoupling
    by_cases hh : c a=d j
    · simp only [hh,eq_self,ite_true]
      ring
    · have hh' : ¬ d j=c a := Ne.symm hh
      simp only [hh,hh',ite_false,mul_zero]
  simp_rw [hw]
  rw [← Finset.mul_sum,show (∑ j, if d j=c a then δ j else 0)=fieldAtomMass δ d (c a) from rfl,
    ← he (c a)]
  exact div_mul_cancel₀ _ (fieldAtomMass_pos_at γ c hγ a).ne'

lemma sameFieldCoupling_col {A B : Type*} [Fintype A] [Fintype B]
    (γ c : A → ℝ) (δ d : B → ℝ) (hδ : ∀ j, 0 < δ j)
    (he : ∀ x, fieldAtomMass γ c x=fieldAtomMass δ d x) (j : B) :
    ∑ a, sameFieldCoupling γ c δ d a j=δ j := by
  have hw a : sameFieldCoupling γ c δ d a j=
      (δ j/fieldAtomMass γ c (d j))*(if c a=d j then γ a else 0) := by
    unfold sameFieldCoupling
    by_cases hh : c a=d j
    · simp only [hh,eq_self,ite_true]
      ring
    · simp only [hh,ite_false,mul_zero]
  simp_rw [hw]
  rw [← Finset.mul_sum,show (∑ a, if c a=d j then γ a else 0)=fieldAtomMass γ c (d j) from rfl]
  apply div_mul_cancel₀
  rw [he]
  exact (fieldAtomMass_pos_at δ d hδ j).ne'

lemma sameFieldCoupling_cost {A B : Type*} [Fintype A] [Fintype B]
    (γ c : A → ℝ) (δ d : B → ℝ) :
    (∑ a, ∑ j, sameFieldCoupling γ c δ d a j* |c a-d j|)=0 := by
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro j _
  unfold sameFieldCoupling
  split_ifs with h
  · simp only [h,sub_self,abs_zero,mul_zero]
  · exact zero_mul _

end InvariantIsing

end

end OAI
