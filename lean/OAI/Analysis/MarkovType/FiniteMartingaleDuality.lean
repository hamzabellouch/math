import OAI.Analysis.MarkovType.FiniteMartingalePairing
import OAI.Analysis.MarkovType.FiniteDualNorming
import OAI.Analysis.MarkovType.FiniteWeightedHolder
import OAI.Analysis.MarkovType.FiniteL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_l2_dual_pairing_bound {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (g : Ω → E →L[ℝ] ℝ) (f : Ω → E) :
    |μ.expect (fun ω => g ω (f ω))| ≤ finiteL2Norm μ g * finiteL2Norm μ f := by
  have h := abs_sum_weighted_le_holder Finset.univ
    (w := μ.mass) (a := fun ω => ‖g ω‖) (b := fun ω => ‖f ω‖)
    (c := fun ω => g ω (f ω)) Real.HolderConjugate.two_two
    (fun ω _ => μ.mass_nonneg ω) (fun ω _ => norm_nonneg _)
    (fun ω _ => norm_nonneg _) (by
      intro ω _
      simpa only [Real.norm_eq_abs] using (g ω).le_opNorm (f ω))
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, finiteL2Norm, FiniteLaw.expect] using h

theorem lowerL2_dual_exponent_range {s : ℝ} (hs : 2 ≤ s) :
    1 < s / (s - 1) ∧ s / (s - 1) ≤ 2 := by
  have hd : 0 < s - 1 := by linarith only [hs]
  constructor
  · apply (lt_div_iff₀ hd).mpr
    linarith only [hs]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hs]

theorem finiteLowerL2_dual_upper {s χ : ℝ} (hs : 2 ≤ s) (hχ : 1 ≤ χ)
    (h : FiniteLowerL2 E s χ) :
    FiniteUpperL2 (E →L[ℝ] ℝ) (s / (s - 1)) χ := by
  intro m μ F G N B hB hG hdiff
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hs
  have hsm1 : 0 < s - 1 := by linarith only [hs]
  have hexp : 1 / (s / (s - 1)) = 1 - 1 / s := by
    field_simp [hspos.ne', hsm1.ne']
  let C : ℝ := χ * (N + 1 : ℝ) ^ (1 - 1 / s)
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans hχ) (Real.rpow_nonneg (by positivity) _)
  let D : ℝ := finiteL2Norm μ (G N)
  let R : ℝ := χ * (N + 1 : ℝ) ^ (1 / (s / (s - 1))) * B
  change D ≤ R
  by_contra hbound
  let ε : ℝ := (D - R) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr (lt_of_not_ge hbound))
  obtain ⟨f, hfunit, htest⟩ := exists_weighted_dual_l2_test μ.mass μ.mass_nonneg
    (G N) D (finiteL2Norm_nonneg μ (G N))
    (by simpa only [D, FiniteLaw.expect] using finiteL2Norm_sq μ (G N)) hε
  have hfL2 : finiteL2Norm μ f ≤ 1 := by
    have hsq : finiteL2Norm μ f ^ (2 : ℕ) ≤ 1 := by
      rw [finiteL2Norm_sq]
      exact hfunit
    exact (sq_le_sq₀ (finiteL2Norm_nonneg μ f) zero_le_one).1
      (by simpa only [one_pow] using hsq)
  let V := F.conditionalProcess μ f
  have hV : F.IsMartingaleUpTo μ V N := F.isMartingaleUpTo_conditionalProcess μ f N
  have hVN : finiteL2Norm μ (V N) ≤ 1 :=
    (F.finiteL2Norm_conditionalProcess_le μ f N).trans hfL2
  have hsum : (∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference V j)) ≤ C := by
    calc
      _ ≤ C * finiteL2Norm μ (V N) := h m μ F V N hV
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hVN hC
      _ = C := mul_one _
  have hpair : μ.expect (fun ω => G N ω (f ω)) ≤ R := by
    calc
      _ = ∑ j ∈ Finset.range (N + 1),
          μ.expect (fun ω => finiteDifference G j ω (finiteDifference V j ω)) :=
        finite_martingale_terminal_pairing hG f
      _ ≤ ∑ j ∈ Finset.range (N + 1), B * finiteL2Norm μ (finiteDifference V j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hGj := hdiff j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
        calc
          _ ≤ |μ.expect (fun ω => finiteDifference G j ω (finiteDifference V j ω))| :=
            le_abs_self _
          _ ≤ finiteL2Norm μ (finiteDifference G j) *
              finiteL2Norm μ (finiteDifference V j) :=
            finite_l2_dual_pairing_bound μ (finiteDifference G j) (finiteDifference V j)
          _ ≤ B * finiteL2Norm μ (finiteDifference V j) :=
            mul_le_mul_of_nonneg_right hGj (finiteL2Norm_nonneg μ _)
      _ = B * ∑ j ∈ Finset.range (N + 1), finiteL2Norm μ (finiteDifference V j) :=
        by rw [Finset.mul_sum]
      _ ≤ B * C := mul_le_mul_of_nonneg_left hsum hB
      _ = R := by dsimp [C, R]; rw [hexp]; ring
  change D - ε ≤ μ.expect (fun ω => G N ω (f ω)) at htest
  dsimp [ε] at htest
  linarith only [htest, hpair, lt_of_not_ge hbound]

end MarkovSuperreflexivity

end

end OAI
