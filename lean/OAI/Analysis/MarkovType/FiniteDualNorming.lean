import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.ConjExponents
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [sectionNormedSpaceℝE : NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

theorem exists_unit_test_ge_norm_sub (f : E →L[ℝ] ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ ‖f‖ - ε ≤ f x := by
  obtain ⟨x, hx, hfx⟩ := f.exists_lt_apply_of_lt_opNorm (sub_lt_self ‖f‖ hε)
  by_cases hpos : 0 ≤ f x
  · refine ⟨x, hx.le, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hfx.le
  · refine ⟨-x, by simpa only [norm_neg] using hx.le, ?_⟩
    simpa only [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hpos)] using hfx.le

theorem exists_weighted_dual_l2_test (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : ι → E →L[ℝ] ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hDsq : D ^ (2 : ℕ) = ∑ i, w i * ‖f i‖ ^ (2 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ι → E,
      (∑ i, w i * ‖z i‖ ^ (2 : ℕ)) ≤ 1 ∧
      D - ε ≤ ∑ i, w i * (f i) (z i) := by
  classical
  by_cases hDz : D = 0
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · simp
    · simp only [map_zero, mul_zero, Finset.sum_const_zero, hDz, zero_sub]
      exact neg_nonpos.mpr hε.le
  have hDpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
  let S : ℝ := ∑ i, w i * ‖f i‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (norm_nonneg _)
  have hS1 : 0 < S + 1 := by linarith only [hS]
  let η : ℝ := ε * D / (S + 1)
  have hη : 0 < η := div_pos (mul_pos hε hDpos) hS1
  let u : ι → E := fun i => Classical.choose (exists_unit_test_ge_norm_sub (f i) hη)
  have hu (i : ι) : ‖u i‖ ≤ 1 ∧ ‖f i‖ - η ≤ (f i) (u i) :=
    Classical.choose_spec (exists_unit_test_ge_norm_sub (f i) hη)
  let a : ι → ℝ := fun i => ‖f i‖ / D
  have ha (i : ι) : 0 ≤ a i := div_nonneg (norm_nonneg _) hD
  let z : ι → E := fun i => a i • u i
  have hnorm (i : ι) : ‖z i‖ ≤ a i := by
    calc
      ‖z i‖ = a i * ‖u i‖ := by
        dsimp [z]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha i)]
      _ ≤ a i * 1 := mul_le_mul_of_nonneg_left (hu i).1 (ha i)
      _ = a i := mul_one _
  have hnormsq (i : ι) : ‖z i‖ ^ (2 : ℕ) ≤ a i ^ (2 : ℕ) := by
    nlinarith only [hnorm i, norm_nonneg (z i), ha i]
  have hasq : (∑ i, w i * a i ^ (2 : ℕ)) = 1 := by
    calc
      (∑ i, w i * a i ^ (2 : ℕ)) =
          (∑ i, w i * ‖f i‖ ^ (2 : ℕ)) / D ^ (2 : ℕ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [a]
        rw [div_pow, mul_div_assoc]
      _ = 1 := by rw [← hDsq, div_self (pow_ne_zero 2 hDz)]
  have hasum : (∑ i, w i * a i) = S / D := by
    dsimp [a, S]
    simp only [mul_div_assoc, Finset.sum_div]
  have hamoment : (∑ i, w i * a i * ‖f i‖) = D := by
    calc
      (∑ i, w i * a i * ‖f i‖) =
          (∑ i, w i * ‖f i‖ ^ (2 : ℕ)) / D := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [a]
        ring
      _ = D := by
        rw [← hDsq]
        field_simp [hDz]
  have hηbound : η * (S / D) ≤ ε := by
    have hratio : S / (S + 1) ≤ 1 := (div_le_one hS1).mpr (by linarith)
    calc
      η * (S / D) = ε * (S / (S + 1)) := by
        dsimp [η]
        field_simp [hDz, hS1.ne']
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := mul_one _
  refine ⟨z, ?_, ?_⟩
  · calc
      (∑ i, w i * ‖z i‖ ^ (2 : ℕ)) ≤ ∑ i, w i * a i ^ (2 : ℕ) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hnormsq i) (hw i)
      _ = 1 := hasq
  · have htest : (∑ i, w i * a i * (‖f i‖ - η)) ≤
        ∑ i, w i * (f i) (z i) := by
      apply Finset.sum_le_sum
      intro i _
      have hpoint := mul_le_mul_of_nonneg_left (hu i).2 (mul_nonneg (hw i) (ha i))
      simpa only [z, map_smul, smul_eq_mul, mul_assoc] using hpoint
    have hleft : (∑ i, w i * a i * (‖f i‖ - η)) = D - η * (S / D) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hamoment, hasum]
      ring
    rw [hleft] at htest
    linarith only [htest, hηbound]

omit sectionNormedSpaceℝE in
theorem weighted_norm_rpow_root [NormedSpace ℝ E] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : ι → E) {q : ℝ} (hq : 0 < q) :
    ((∑ i, w i * ‖x i‖ ^ q) ^ (1 / q)) ^ q = ∑ i, w i * ‖x i‖ ^ q := by
  have hsum : 0 ≤ ∑ i, w i * ‖x i‖ ^ q :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.rpow_mul hsum]
  have hexp : (1 / q) * q = (1 : ℝ) := by field_simp [hq.ne']
  rw [hexp, Real.rpow_one]

theorem exists_weighted_dual_norming (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : ι → E) {p q : ℝ} (hpq : p.HolderConjugate q)
    (D : ℝ) (hD : 0 < D) (hDq : D ^ q = ∑ i, w i * ‖x i‖ ^ q) :
    ∃ ψ : ι → E →L[ℝ] ℝ,
      (∑ i, w i * ‖ψ i‖ ^ p) ≤ 1 ∧ (∑ i, w i * ψ i (x i)) = D := by
  classical
  let ell : ι → E →L[ℝ] ℝ := fun i => Classical.choose (exists_dual_vector'' ℝ (x i))
  have hell (i : ι) : ‖ell i‖ ≤ 1 ∧ ell i (x i) = ‖x i‖ :=
    Classical.choose_spec (exists_dual_vector'' ℝ (x i))
  let c : ι → ℝ := fun i => (‖x i‖ / D) ^ (q - 1)
  have hc (i : ι) : 0 ≤ c i := Real.rpow_nonneg (div_nonneg (norm_nonneg _) hD.le) _
  let ψ : ι → E →L[ℝ] ℝ := fun i => c i • ell i
  have hψnorm (i : ι) : ‖ψ i‖ ≤ c i := by
    calc
      ‖ψ i‖ ≤ ‖c i‖ * ‖ell i‖ := ContinuousLinearMap.opNorm_smul_le (c i) (ell i)
      _ = c i * ‖ell i‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (hc i)]
      _ ≤ c i * 1 := mul_le_mul_of_nonneg_left (hell i).1 (hc i)
      _ = c i := mul_one _
  have hcpow (i : ι) : c i ^ p = ‖x i‖ ^ q / D ^ q := by
    dsimp [c]
    rw [← Real.rpow_mul (div_nonneg (norm_nonneg _) hD.le),
      hpq.symm.sub_one_mul_conj, Real.div_rpow (norm_nonneg _) hD.le]
  have hcnorm (i : ι) : c i * ‖x i‖ = ‖x i‖ ^ q / D ^ (q - 1) := by
    have hxpow : ‖x i‖ ^ (q - 1) * ‖x i‖ = ‖x i‖ ^ q := by
      have hexp : q - 1 + 1 = q := by ring
      rw [← Real.rpow_add_one' (y := q - 1) (norm_nonneg _)
        (by simpa only [hexp] using hpq.symm.ne_zero), hexp]
    dsimp [c]
    rw [Real.div_rpow (norm_nonneg _) hD.le]
    calc
      (‖x i‖ ^ (q - 1) / D ^ (q - 1)) * ‖x i‖ =
          (‖x i‖ ^ (q - 1) * ‖x i‖) / D ^ (q - 1) := by ring
      _ = ‖x i‖ ^ q / D ^ (q - 1) := by rw [hxpow]
  refine ⟨ψ, ?_, ?_⟩
  · calc
      (∑ i, w i * ‖ψ i‖ ^ p) ≤ ∑ i, w i * c i ^ p := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hψnorm i) hpq.pos.le) (hw i)
      _ = (∑ i, w i * ‖x i‖ ^ q) / D ^ q := by
        simp only [hcpow, mul_div_assoc, Finset.sum_div]
      _ = 1 := by rw [← hDq, div_self (Real.rpow_pos_of_pos hD q).ne']
  · calc
      (∑ i, w i * ψ i (x i)) = ∑ i, w i * (c i * ‖x i‖) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [ψ, smul_apply, smul_eq_mul, (hell i).2]
      _ = (∑ i, w i * ‖x i‖ ^ q) / D ^ (q - 1) := by
        simp only [hcnorm, mul_div_assoc, Finset.sum_div]
      _ = D := by
        rw [← hDq, ← Real.rpow_sub hD q (q - 1)]
        have hexp : q - (q - 1) = (1 : ℝ) := by ring
        rw [hexp, Real.rpow_one]

end MarkovSuperreflexivity

end OAI
