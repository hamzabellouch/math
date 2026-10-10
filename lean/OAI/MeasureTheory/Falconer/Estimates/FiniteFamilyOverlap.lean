import OAI.MeasureTheory.Falconer.Estimates.FinitePopularity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

/-! A common row with many large intersections, for the two-sided
additive-energy refinements. -/
namespace Falconer

 theorem finite_membership_sum {β : Type*} [DecidableEq β]
    (U S : Finset β) (hS : S ⊆ U) :
    (∑ x ∈ U, if x ∈ S then (1 : ℝ) else 0) = S.card := by
  have he : U.filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hx => hS hx)
  rw [Finset.sum_boole,he]

 theorem finite_family_overlap_moment {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hsub : ∀ i ∈ I, A i ⊆ U) :
    (∑ i ∈ I, ((A i).card : ℝ))^2 ≤
      (U.card : ℝ)*(∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ)) := by
  classical
  let d := fun x => ∑ i ∈ I, if x ∈ A i then (1 : ℝ) else 0
  have htotal : ∑ x ∈ U, d x = ∑ i ∈ I, ((A i).card : ℝ) := by
    dsimp [d]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi => finite_membership_sum U (A i) (hsub i hi)
  have hsquare : (∑ x ∈ U, (d x)^2) =
      ∑ i ∈ I, ∑ j ∈ I, ((A i ∩ A j).card : ℝ) := by
    calc
      _ = ∑ x ∈ U, ∑ i ∈ I, ∑ j ∈ I,
          (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) := by
        simp only [d,pow_two,Finset.sum_mul_sum]
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ U,
          (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j _
        have he (x : β) :
            (if x ∈ A i then (1 : ℝ) else 0)*(if x ∈ A j then 1 else 0) =
            if x ∈ A i ∩ A j then 1 else 0 := by
          by_cases hx : x ∈ A i <;> by_cases hy : x ∈ A j <;> simp [hx,hy]
        simp_rw [he]
        exact finite_membership_sum U _ fun x hx => hsub i hi (Finset.mem_inter.mp hx).1
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq U (fun _ => (1 : ℝ)) d
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one,htotal,hsquare] using hCS

 theorem finite_family_common_row {α β : Type*} [DecidableEq β]
    (I : Finset α) (U : Finset β) (A : α → Finset β)
    (hI : I.Nonempty) (hU : U.Nonempty) {m : ℝ} (hm : 0 < m)
    (hsub : ∀ i ∈ I, A i ⊆ U) (hsize : ∀ i ∈ I, m ≤ ((A i).card : ℝ)) :
    ∃ i₀ ∈ I, ∃ J ⊆ I,
      (m^2/(U.card : ℝ))*(I.card : ℝ) ≤ 2*(U.card : ℝ)*(J.card : ℝ) ∧
      ∀ j ∈ J, m^2/(2*(U.card : ℝ)) ≤ ((A i₀ ∩ A j).card : ℝ) := by
  classical
  have hIpos : 0 < (I.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hI)
  have hUpos : 0 < (U.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hU)
  let w := fun i => ∑ j ∈ I, ((A i ∩ A j).card : ℝ)
  obtain ⟨i₀,hi₀,hmax⟩ := I.exists_max_image w hI
  have hsum : m*(I.card : ℝ) ≤ ∑ i ∈ I, ((A i).card : ℝ) := by
    calc
      _ = ∑ _i ∈ I, m := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hsize
  have hmoment := finite_family_overlap_moment I U A hsub
  have hmaxsum : (∑ i ∈ I, w i) ≤ (I.card : ℝ)*w i₀ := by
    calc
      _ ≤ ∑ _i ∈ I, w i₀ := Finset.sum_le_sum fun i hi => hmax i hi
      _ = _ := by simp
  have hlower : (m*(I.card : ℝ))^2 ≤ (U.card : ℝ)*((I.card : ℝ)*w i₀) := by
    exact (pow_le_pow_left₀ (mul_pos hm hIpos).le hsum 2).trans
      (hmoment.trans (mul_le_mul_of_nonneg_left hmaxsum hUpos.le))
  have hw : (m^2/(U.card : ℝ))*(I.card : ℝ) ≤ w i₀ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hUpos).2
    apply (mul_le_mul_iff_left₀ hIpos).1
    calc
      _ = (m*(I.card : ℝ))^2 := by ring
      _ ≤ _ := hlower
      _ = _ := by ring
  let J := I.filter fun j => m^2/(2*(U.card : ℝ)) ≤ ((A i₀ ∩ A j).card : ℝ)
  have hp := finite_popular_mass I (fun j => ((A i₀ ∩ A j).card : ℝ))
    (I := (m^2/(U.card : ℝ))*(I.card : ℝ))
    (θ := m^2/(2*(U.card : ℝ))) (L := (U.card : ℝ))
    (by positivity) hw (le_of_eq (by ring))
    (fun j _ => Nat.cast_le.mpr (Finset.card_le_card
      (fun x hx => hsub i₀ hi₀ (Finset.mem_inter.mp hx).1)))
  refine ⟨i₀,hi₀,J,Finset.filter_subset _ _,?_,?_⟩
  · have hh := hp.2
    change (m^2/(U.card : ℝ))*(I.card : ℝ)/2 ≤ (U.card : ℝ)*(J.card : ℝ) at hh
    linarith
  · intro j hj
    exact (Finset.mem_filter.mp hj).2

end Falconer

end OAI
