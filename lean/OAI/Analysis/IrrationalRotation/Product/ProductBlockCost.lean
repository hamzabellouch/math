import OAI.Analysis.IrrationalRotation.Product.ProductLogIntegral
import OAI.Analysis.IrrationalRotation.Analysis.BlockAngleConstruction

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

theorem one_le_block_cost {m : ℕ} (hm : 0 < m) (K C : ℝ)
    (hK : 1 ≤ K) (hC : K ^ 2 ≤ C) (θ : Fin m → ℝ)
    (hθ : ∀ r, 1 / ((m : ℝ) * K) ≤ θ r) :
    (1 : ℝ≥0∞) ≤ ∑' r, ENNReal.ofReal (C * θ r) := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hC0 : 0 ≤ C := le_trans (sq_nonneg K) hC
  have hθ0 (r : Fin m) : 0 ≤ θ r :=
    (le_of_lt (one_div_pos.mpr (mul_pos hmpos hKpos))).trans (hθ r)
  have hlower : C / K ≤ ∑ r : Fin m, C * θ r := by
    calc
      C / K = ∑ _r : Fin m, C * (1 / ((m : ℝ) * K)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      _ ≤ ∑ r : Fin m, C * θ r :=
        Finset.sum_le_sum (fun r _ ↦ mul_le_mul_of_nonneg_left (hθ r) hC0)
  have hone : 1 ≤ C / K := by
    apply (le_div_iff₀ hKpos).mpr
    nlinarith
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg
    (fun r _ ↦ mul_nonneg hC0 (hθ0 r))]
  exact ENNReal.one_le_ofReal.mpr (hone.trans hlower)

theorem tsum_block_coordinate_cost_eq_top
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    (∑' i, ENNReal.ofReal (C (e i).1 * θ i)) = ∞ := by
  rw [← e.symm.tsum_eq (fun i : ℕ ↦ ENNReal.ofReal (C (e i).1 * θ i))]
  simp only [e.apply_symm_apply]
  rw [ENNReal.tsum_sigma (fun (j : ℕ) (r : Fin (m j)) ↦
    ENNReal.ofReal (C j * θ (e.symm ⟨j, r⟩)))]
  apply top_le_iff.mp
  calc
    (∞ : ℝ≥0∞) = ∑' _j : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' j, ∑' r : Fin (m j), ENNReal.ofReal (C j * θ (e.symm ⟨j, r⟩)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply one_le_block_cost (hm j) (K j) (C j) (hK j) (hC j)
      intro r
      simpa only [e.apply_symm_apply] using hθ (e.symm ⟨j, r⟩)

theorem hasNegInfiniteLogIntegral_of_block_bounds
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hθ : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i ↦ C (e i).1)) := by
  apply (hasNegInfiniteLogIntegral_iff_tsum θ _ hθ01
    (fun i ↦ le_trans (sq_nonneg _) (hC (e i).1))).mpr
  exact tsum_block_coordinate_cost_eq_top m hm K C hK hC e θ hθ

theorem exists_admissible_block_weight
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j ↦ 1 / K j)) :
    ∃ (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ),
      (∀ i : Σ j, Fin (m j), e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val) ∧
      (∀ i, θ i ∈ Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1))) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      AdmissibleAnglesAndCosts θ (fun i ↦ C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i ↦ C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure, 0 < weight θ (fun i ↦ C (e i).1) x ∧
        weight θ (fun i ↦ C (e i).1) x ≤ 1) := by
  have hKpos (j : ℕ) : 0 < K j := lt_of_lt_of_le zero_lt_one (hK j)
  have hCpos (j : ℕ) : 0 < C j := lt_of_lt_of_le (sq_pos_of_pos (hKpos j)) (hC j)
  obtain ⟨e, θ, he, hbounds, hθ01, hθsum, hsumBound, hlin⟩ :=
    InvariantProjection.IndependentAngles.exists_summable_block_angles_unitInterval
      m hm K hKpos hscale hsum
  refine ⟨e, θ, he, hbounds, hsumBound, ?_, ?_, ?_⟩
  · exact ⟨fun i ↦ ⟨(hθ01 i).1, (hθ01 i).2, hCpos (e i).1⟩, hθsum, hlin⟩
  · exact hasNegInfiniteLogIntegral_of_block_bounds m hm K C hK hC e θ
      (fun i ↦ ⟨(hθ01 i).1.le, (hθ01 i).2⟩) (fun i ↦ (hbounds i).1)
  · filter_upwards [ae_weight_pos θ (fun i ↦ C (e i).1)
      (fun i ↦ (hθ01 i).1.le) (fun i ↦ (hCpos (e i).1).le) hθsum] with x hx
    exact ⟨hx, (weight_mem_Icc θ _ x).2⟩

end Invariant233.ProductModel

end OAI
