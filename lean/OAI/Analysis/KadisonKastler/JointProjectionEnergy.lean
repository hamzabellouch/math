import OAI.Analysis.KadisonKastler.ProjectionMatrices

namespace OAI

/-! # Vector energy in two commuting finite spectral partitions -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace H] in
theorem jointProjection_total (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∑ i, P i = 1) (hQ : ∑ j, Q j = 1) :
    (∑ a : ι × κ, P a.1 * Q a.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hQ,mul_one]
  exact hP

omit [CompleteSpace H] [Fintype ι] [Fintype κ] in
theorem jointProjection_orthogonal
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i k, i ≠ k → P i * P k = 0)
    (hQ : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hc : ∀ i j, Commute (P i) (Q j)) :
    ∀ a b : ι × κ, a ≠ b → (P a.1 * Q a.2) * (P b.1 * Q b.2) = 0 := by
  intro a b hab
  have he : (P a.1 * Q a.2) * (P b.1 * Q b.2) =
      (P a.1 * P b.1) * (Q a.2 * Q b.2) := by
    rw [mul_assoc,← mul_assoc (Q a.2),(hc b.1 a.2).eq.symm]
    simp only [mul_assoc]
  rw [he]
  by_cases hi : a.1 = b.1
  · have hj : a.2 ≠ b.2 := fun hj => hab (Prod.ext hi hj)
    rw [hQ _ _ hj,mul_zero]
  · rw [hP _ _ hi,zero_mul]

omit [CompleteSpace H] in
theorem jointProjection_weighted_sum
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∑ i, P i = 1) (hQ : ∑ j, Q j = 1)
    (c : ι → ℂ) (d : κ → ℂ) :
    (∑ a : ι × κ, (c a.1-d a.2) • (P a.1 * Q a.2)) =
      (∑ i, c i • P i) - (∑ j, d j • Q j) := by
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib,Fintype.sum_prod_type,Fintype.sum_prod_type]
  have hl : (∑ i, ∑ j, c i • (P i * Q j)) = ∑ i, c i • P i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.smul_sum,← Finset.mul_sum,hQ,mul_one]
  have hr : (∑ i, ∑ j, d j • (P i * Q j)) = ∑ j, d j • Q j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.smul_sum,← Finset.sum_mul,hP,one_mul]
  rw [hl,hr]

theorem norm_jointProjection_weighted_sum_sq
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι × κ → ℂ) (ξ : H) :
    ‖(∑ a : ι × κ, c a • (P a.1 * Q a.2)) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖c a‖ ^ 2 * ‖(P a.1 * Q a.2) ξ‖ ^ 2 := by
  classical
  have ho := orthogonal_projection_vectors (fun a : ι × κ => P a.1 * Q a.2)
    (fun a => ((hP a.1).mul (hQ a.2) (hc a.1 a.2)).isSelfAdjoint)
    (jointProjection_orthogonal P Q hPo hQo hc) ξ
  have horth : ∀ a ∈ (univ : Finset (ι × κ)), ∀ b ∈ (univ : Finset (ι × κ)),
      a ≠ b → inner ℂ (c a • (P a.1 * Q a.2) ξ) (c b • (P b.1 * Q b.2) ξ) = 0 := by
    intro a _ b _ hab
    rw [inner_smul_left,inner_smul_right,ho hab,mul_zero,mul_zero]
  have he := norm_sum_sq_of_pairwise_orthogonal univ
    (fun a : ι × κ => c a • (P a.1 * Q a.2) ξ) horth
  simpa only [_root_.sum_apply,smul_apply,norm_smul,mul_pow] using he

theorem jointProjection_gap_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℂ) (d : κ → ℂ) (ξ : H) :
    ‖((∑ i, c i • P i) - (∑ j, d j • Q j)) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖c a.1-d a.2‖ ^ 2 * ‖(P a.1 * Q a.2) ξ‖ ^ 2 := by
  rw [← jointProjection_weighted_sum P Q hPt hQt c d]
  exact norm_jointProjection_weighted_sum_sq P Q hP hQ hPo hQo hc _ ξ

end

end KadisonKastler

end OAI
