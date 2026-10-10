import OAI.Analysis.MarkovType.CoefficientFunctional
import OAI.Analysis.MarkovType.TriangularBasic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} {K : ℝ} {x : Fin n → E}

theorem CoefficientBasic.triangular_of_large_entries (hx : CoefficientBasic K x)
    (hK : 0 < K) (hS : 0 < ‖∑ i, x i‖)
    (hlarge : ∀ i, ‖∑ j, x j‖ / 2 < ‖x i‖) :
    Nonempty (TriangularSystem E n (1 / (4 * K ^ 2))) := by
  classical
  let S : ℝ := ‖∑ i, x i‖
  have hSpos : 0 < S := hS
  have hxpos (i : Fin n) : 0 < ‖x i‖ :=
    (div_pos hSpos (by norm_num : (0 : ℝ) < 2)).trans (hlarge i)
  choose f hf hpair using fun i =>
    hx.exists_coordinate_functional hK.le i (norm_pos_iff.mp (hxpos i))
  have hfbound (i : Fin n) : ‖f i‖ ≤ 4 * K / S := by
    apply (hf i).trans
    apply (div_le_div_iff₀ (hxpos i) hSpos).mpr
    have hh : S ≤ 2 * ‖x i‖ := by linarith [hlarge i]
    have hm := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK.le)
    nlinarith only [hm]
  let v : Fin n → E := fun i => ∑ j, if j.val < i.val + 1 then x j else 0
  have hv (i : Fin n) : ‖v i‖ ≤ K * S :=
    hx.norm_prefix_le (i.val + 1) i.is_lt
  have hfv (i j : Fin n) : f j (v i) = if j ≤ i then 1 else 0 := by
    change f j (∑ k, if k.val < i.val + 1 then x k else 0) = _
    rw [map_sum]
    calc
      _ = ∑ k : Fin n, if k = j then (if j ≤ i then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hcmp : j.val < i.val + 1 ↔ j ≤ i := by
            change j.val < i.val + 1 ↔ j.val ≤ i.val
            omega
          by_cases hji : j ≤ i
          · simp [hcmp, hji, hpair]
          · simp [hcmp, hji]
        · have hjk : j ≠ k := Ne.symm hkj
          by_cases hki : k.val < i.val + 1
          · simp only [ite_eq_left hki, hpair, ite_eq_right hjk, ite_eq_right hkj]
          · simp only [ite_eq_right hki, map_zero, ite_eq_right hkj]
      _ = _ := by simp
  have hKS : 0 < K * S := mul_pos hK hSpos
  have hscale : 0 < S / (4 * K) := div_pos hSpos (by positivity)
  refine ⟨{
    vectors := fun i => (K * S)⁻¹ • v i
    functionals := fun j => (S / (4 * K)) • f j
    vectors_bound := ?_
    functionals_bound := ?_
    pairing := ?_ }⟩
  · intro i
    calc
      ‖(K * S)⁻¹ • v i‖ = (K * S)⁻¹ * ‖v i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hKS)]
      _ ≤ (K * S)⁻¹ * (K * S) :=
        mul_le_mul_of_nonneg_left (hv i) (inv_nonneg.mpr hKS.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hKS)
  · intro j
    calc
      ‖(S / (4 * K)) • f j‖ ≤ (S / (4 * K)) * ‖f j‖ := by
        simpa only [Real.norm_eq_abs, abs_of_pos hscale] using
          ContinuousLinearMap.opNorm_smul_le (S / (4 * K)) (f j)
      _ ≤ (S / (4 * K)) * (4 * K / S) :=
        mul_le_mul_of_nonneg_left (hfbound j) hscale.le
      _ = 1 := by field_simp [ne_of_gt hK, ne_of_gt hSpos]
  · intro i j
    change (S / (4 * K)) * f j ((K * S)⁻¹ • v i) = _
    rw [(f j).map_smul, smul_eq_mul, hfv]
    by_cases hji : j ≤ i
    · simp only [ite_eq_left hji, mul_one]
      field_simp [ne_of_gt hK, ne_of_gt hSpos]

    · simp only [ite_eq_right hji, mul_zero]

theorem CoefficientBasic.exists_half_entry_of_no_triangular
    (hx : CoefficientBasic K x) (hK : 0 < K) (hn : 0 < n)
    (hnone : ¬ Nonempty (TriangularSystem E n (1 / (4 * K ^ 2)))) :
    ∃ i : Fin n, ‖x i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, x j‖ := by
  by_contra h
  have hlarge (i : Fin n) : ‖∑ j, x j‖ / 2 < ‖x i‖ := by
    apply lt_of_not_ge
    intro hi
    apply h ⟨i, ?_⟩
    nlinarith
  have hS : 0 < ‖∑ i, x i‖ := by
    by_contra hnpos
    have hz : ‖∑ i, x i‖ = 0 := le_antisymm (le_of_not_gt hnpos) (norm_nonneg _)
    let i : Fin n := ⟨0, hn⟩
    have hb := hx.norm_entry_le i
    have hh := hlarge i
    rw [hz] at hb hh
    nlinarith
  exact hnone (hx.triangular_of_large_entries hK hS hlarge)

theorem FiniteTriangularObstruction.coefficient_half_gain
    (hE : FiniteTriangularObstruction E) {K : ℝ} (hK : 1 < K) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ x : Fin M → E, CoefficientBasic K x →
      ∃ i : Fin M, ‖x i‖ ≤ (1 / 2 : ℝ) * ‖∑ j, x j‖ := by
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hden : 0 < 4 * K ^ 2 := by positivity
  have hθpos : 0 < 1 / (4 * K ^ 2) := one_div_pos.mpr hden
  have hθlt : 1 / (4 * K ^ 2) < 1 := by
    apply (div_lt_one hden).mpr
    nlinarith
  obtain ⟨n, hn, hnone⟩ := hE (1 / (4 * K ^ 2)) hθpos hθlt
  let M := max n 2
  have hM : 0 < M := lt_of_lt_of_le (by decide : 0 < 2) (le_max_right n 2)
  have hnoneM : ¬ Nonempty (TriangularSystem E M (1 / (4 * K ^ 2))) :=
    TriangularSystem.no_longer_of_no_shorter (le_max_left n 2) hnone
  refine ⟨M, le_max_right n 2, ?_⟩
  intro x hx
  exact hx.exists_half_entry_of_no_triangular hKpos hM hnoneM

end MarkovSuperreflexivity

end

end OAI
