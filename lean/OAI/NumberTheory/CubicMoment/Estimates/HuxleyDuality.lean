import OAI.NumberTheory.CubicMoment.Estimates.PublishedAdditiveSieve

namespace OAI

/-! Finite Hilbert-space duality for the two sums in the additive large sieve. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_additive_sieve_duality {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (A : ι → κ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hdual : ∀ b : ι → ℂ,
      (∑ n ∈ N, ‖∑ p ∈ P, b p*A p n‖^2) ≤ B*∑ p ∈ P, ‖b p‖^2)
    (v : κ → ℂ) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n*A p n‖^2) ≤ B*∑ n ∈ N, ‖v n‖^2 := by
  let F := fun p => ∑ n ∈ N, v n*A p n
  let S : ℝ := ∑ p ∈ P, ‖F p‖^2
  let T := fun n => ∑ p ∈ P, star (F p)*A p n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ ∑ n ∈ N, ‖v n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (S:ℂ) = ∑ n ∈ N, v n*T n := by
    calc
      (S:ℂ) = ∑ p ∈ P, F p*star (F p) := by
        simp only [S,Complex.ofReal_sum,Complex.ofReal_pow]
        apply Finset.sum_congr rfl
        intro p hp
        exact (Complex.mul_conj' (F p)).symm
      _ = ∑ p ∈ P, ∑ n ∈ N, v n*A p n*star (F p) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_mul N (fun n => v n*A p n) (star (F p))
      _ = ∑ n ∈ N, v n*T n := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp only [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  have hnorm : S ≤ ∑ n ∈ N, ‖v n‖*‖T n‖ := by
    calc
      S = ‖(S:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hS]
      _ ≤ _ := by
        rw [he]
        simpa only [norm_mul] using norm_sum_le N (fun n => v n*T n)
  have hc : S^2 ≤ (∑ n ∈ N, ‖v n‖^2)*(∑ n ∈ N, ‖T n‖^2) := by
    exact ((sq_le_sq₀ hS (Finset.sum_nonneg (fun _ _ => mul_nonneg
      (_root_.norm_nonneg _) (_root_.norm_nonneg _)))).mpr hnorm).trans
      (Finset.sum_mul_sq_le_sq_mul_sq N (fun n => ‖v n‖) (fun n => ‖T n‖))
  have hd : (∑ n ∈ N, ‖T n‖^2) ≤ B*S := by
    simpa only [T,S,norm_star] using hdual (fun p => star (F p))
  have hsquare : S*S ≤ (B*(∑ n ∈ N, ‖v n‖^2))*S := by
    calc
      S*S = S^2 := (pow_two _).symm
      _ ≤ _ := hc.trans (mul_le_mul_of_nonneg_left hd hE)
      _ = _ := by ring
  change S ≤ _
  by_cases hzero : S = 0
  · rw [hzero]
    exact mul_nonneg hB hE
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hS (Ne.symm hzero))).mp hsquare

end CubicFirstMoment

end

end OAI
