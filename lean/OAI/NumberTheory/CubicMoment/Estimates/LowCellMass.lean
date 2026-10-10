import OAI.NumberTheory.CubicMoment.Estimates.LogCellCount

namespace OAI
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadic_logCell_left_mass (P S : Finset Eisenstein) {J A B : ℝ} (hJ : 1 ≤ J)
    (hP : ∀ a ∈ P, 1 ≤ norm a/A ∧ norm a/A ≤ 2)
    (hS : ∀ b ∈ S, 1 ≤ norm b/B ∧ norm b/B ≤ 2)
    (E : Finset (ℤ × ℤ))
    (hE : E ⊆ (P.image (logNormCell J A)).product (S.image (logNormCell J B)))
    (α : Eisenstein → ℂ) :
    (∑ e ∈ E, Real.sqrt (∑ a ∈ logNormCellSupport P J A e.1, ‖α a‖^2)) ≤
      4*J^2*Real.sqrt (∑ a ∈ P, ‖α a‖^2) := by
  let I := P.image (logNormCell J A)
  let L := S.image (logNormCell J B)
  let a := fun i => Real.sqrt (∑ n ∈ logNormCellSupport P J A i, ‖α n‖^2)
  have hi : (I.card:ℝ) ≤ 2*J := dyadic_logCell_card_bound P hJ hP
  have hl : (L.card:ℝ) ≤ 2*J := dyadic_logCell_card_bound S hJ hS
  have hs : (∑ i ∈ I, a i) ≤ Real.sqrt (I.card:ℝ)*Real.sqrt (∑ n ∈ P, ‖α n‖^2) := by
    have hh := cell_mass_sum_le I a
    simpa only [I,a,logNormCell_energy] using hh
  have hroot : Real.sqrt (I.card:ℝ) ≤ 2*J := by
    have hn := Real.sqrt_nonneg (I.card:ℝ)
    have hsq := Real.sq_sqrt (show 0 ≤ (I.card:ℝ) by positivity)
    nlinarith [sq_nonneg (Real.sqrt (I.card:ℝ)-1)]
  calc
    _ ≤ ∑ e ∈ I.product L, a e.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => Real.sqrt_nonneg _)
    _ = (L.card:ℝ)*(∑ i ∈ I, a i) := by
      calc
        _ = ∑ i ∈ I, ∑ _j ∈ L, a i := Finset.sum_product I L _
        _ = _ := by
          simp only [Finset.sum_const,nsmul_eq_mul]
          rw [Finset.mul_sum]
    _ ≤ (2*J)*(Real.sqrt (I.card:ℝ)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)) :=
      mul_le_mul hl hs (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by positivity)
    _ ≤ (2*J)*((2*J)*Real.sqrt (∑ n ∈ P, ‖α n‖^2)) := by gcongr
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
