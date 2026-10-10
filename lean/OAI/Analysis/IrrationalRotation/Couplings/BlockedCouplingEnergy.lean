import OAI.Analysis.IrrationalRotation.Couplings.ProductCoupling

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Invariant233.BlockedProductCoupling

theorem sum_block_energy (m : ℕ) (hm : 0 < m) (κ t : ℝ) :
    (∑' _i : Fin m, 20 * (2 * κ ^ 2 / (m : ℝ) + t / (m : ℝ))) =
      20 * (2 * κ ^ 2 + t) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem full_energy_sum (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (κ : ℕ → ℝ) (hκ : Summable (fun s => κ s ^ 2)) (j : ℕ) :
    Summable (fun p : Σ s, Fin (m s) =>
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) ∧
    (∑' p : Σ s, Fin (m s),
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  classical
  have htag : Summable (fun s : ℕ => if s = j then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {j}) (by simp)
  have he (s : ℕ) :
      (∑' _i : Fin (m s), 20 * (2 * κ s ^ 2 / (m s : ℝ) +
        (if s = j then 1 else 0) / (m s : ℝ))) =
      20 * (2 * κ s ^ 2 + (if s = j then 1 else 0)) :=
    sum_block_energy _ (hm s) _ _
  have hblock : Summable (fun s => 20 * (2 * κ s ^ 2 +
      (if s = j then (1 : ℝ) else 0))) :=
    ((hκ.mul_left 2).add htag).mul_left 20
  have hs : Summable (fun p : Σ s, Fin (m s) =>
      20 * (2 * κ p.1 ^ 2 / (m p.1 : ℝ) +
        (if p.1 = j then 1 else 0) / (m p.1 : ℝ))) := by
    apply (summable_sigma_of_nonneg (fun p => by positivity)).2
    refine ⟨fun s => (hasSum_fintype _).summable, ?_⟩
    simpa only [he] using hblock
  refine ⟨hs, ?_⟩
  rw [hs.tsum_sigma' (fun s => (hasSum_fintype _).summable)]
  simp only [he]
  rw [tsum_mul_left, (hκ.mul_left 2).tsum_add htag, tsum_mul_left]
  simp

theorem enumerated_energy_sum (m : ℕ → ℕ) (hm : ∀ s, 0 < m s)
    (κ : ℕ → ℝ) (hκ : Summable (fun s => κ s ^ 2))
    (e : ℕ ≃ Σ s, Fin (m s)) (j : ℕ) :
    Summable (fun i : ℕ => 20 * (2 * κ (e i).1 ^ 2 / (m (e i).1 : ℝ) +
      (if (e i).1 = j then 1 else 0) / (m (e i).1 : ℝ))) ∧
    (∑' i : ℕ, 20 * (2 * κ (e i).1 ^ 2 / (m (e i).1 : ℝ) +
      (if (e i).1 = j then 1 else 0) / (m (e i).1 : ℝ))) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  obtain ⟨hs, hv⟩ := full_energy_sum m hm κ hκ j
  exact ⟨e.summable_iff.mpr hs, (e.tsum_eq _).trans hv⟩

end Invariant233.BlockedProductCoupling

end OAI
