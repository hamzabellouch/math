import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationProfileBudgetBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open TemplateOneSidedNumericInputs Arithmetic

theorem exists_normalized_source_profile_budget (k j : ℕ) (ρ : 𝓢(ℝ,ℂ))
    {z a C CD CM β : ℝ} (Wl Wc : ℝ) (hz : 0 < z) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hCM : 0 ≤ CM) (hβ : 0 ≤ β) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ L : ℝ, ∀ D M : ℕ,
      (D : ℝ) ≤ CD * (1 + (⌊z * L⌋₊ : ℝ)) →
      (M : ℝ) ≤ CM * (1 + (⌊z * L⌋₊ : ℝ)) →
      max (Real.exp Wc)
          (Real.exp ((-a * (⌊z * L⌋₊ : ℝ) + Wl) / 2) * leafProfileBound ρ) ≤
        Real.exp (historyPolynomialCost C' z 4 L) ∧
      (((6 + 2 * sourceDegreeFactor k j) * (M + 1) + 1 : ℕ) : ℝ) ≤
        Real.exp (historyPolynomialCost C' z 4 L) ∧
      (3 + ∑ i : Unit ⊕ (Fin (2^j) ⊕ Fin (2^j)),
        (Sum.elim (fun _ : Unit => Wc)
            (fun _ : Fin (2^j) ⊕ Fin (2^j) => -a * (⌊z * L⌋₊ : ℝ) + Wl) i -
          Sum.elim (fun _ : Unit => -Wc)
            (fun _ : Fin (2^j) ⊕ Fin (2^j) =>
              coarseLower D (rowLogHeight C z β L) (a * (⌊z * L⌋₊ : ℝ)) Wl) i)) ≤
        Real.exp (historyPolynomialCost C' z 4 L) := by
  let K := numericCostCoefficient β z C CD a Wl
  let R : ℝ := 3 + 2 * |Wc| + 2 * (2 : ℝ)^j
  let P : ℝ := Real.exp |Wc| + Real.exp (|Wl| / 2) * leafProfileBound ρ + 1
  let F : ℝ := ((6 + 2 * sourceDegreeFactor k j : ℕ) : ℝ)
  let G : ℝ := F * (CM + 1) + 1
  let C' : ℝ := K + R + (P + 1) + (G + 1) + 1
  have hK : 0 < K := (numeric_inputs_cost Wl hβ hz hC hCD ha).1
  have hR : 0 < R := by dsimp [R]; positivity
  have hP : 0 < P := by
    have hp := leafProfileBound_pos ρ
    dsimp [P]
    positivity
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hG : 0 < G := by dsimp [G]; positivity
  have hC' : 0 < C' := by dsimp [C']; linarith
  refine ⟨C', hC', ?_⟩
  intro L D M hD hM
  let m : ℝ := 1 + (⌊z * L⌋₊ : ℝ)
  have hm : 1 ≤ m := by dsimp [m]; linarith [Nat.cast_nonneg (α:=ℝ) ⌊z*L⌋₊]
  have hsmall (A : ℝ) (hA : A ≤ C') :
      Real.exp (historyPolynomialCost A z 4 L) ≤
        Real.exp (historyPolynomialCost C' z 4 L) :=
    Real.exp_le_exp.mpr (historyPolynomialCost_mono_coefficient hA z L 4)
  have hΔ : 0 ≤ a * (⌊z * L⌋₊ : ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
  have hprofile : max (Real.exp Wc)
      (Real.exp ((-a * (⌊z * L⌋₊ : ℝ) + Wl) / 2) * leafProfileBound ρ) ≤ P := by
    apply max_le
    · have hh := Real.exp_le_exp.mpr (le_abs_self Wc)
      dsimp [P]
      linarith [mul_nonneg (Real.exp_nonneg (|Wl| / 2)) (leafProfileBound_pos ρ).le]
    · have hh := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (show (-a * (⌊z*L⌋₊:ℝ) + Wl) / 2 ≤ |Wl| / 2 by
          linarith [le_abs_self Wl])) (leafProfileBound_pos ρ).le
      dsimp [P]
      linarith [Real.exp_pos |Wc|]
  refine ⟨?_, ?_, ?_⟩
  · apply hprofile.trans
    apply (le_mul_of_one_le_right hP.le hm).trans
    apply (linear_le_exp_quartic_cost P z L hP.le).trans
    exact hsmall (P + 1) (by dsimp [C']; linarith)
  · have hdegree : (((6 + 2 * sourceDegreeFactor k j) * (M + 1) + 1 : ℕ) : ℝ) ≤ G*m := by
      have hcast : (((6 + 2 * sourceDegreeFactor k j) * (M + 1) + 1 : ℕ) : ℝ) =
          F * ((M : ℝ) + 1) + 1 := by
        dsimp only [F]
        push_cast
        ring
      rw [hcast]
      have hMM : (M : ℝ) + 1 ≤ (CM + 1) * m := by change (M:ℝ) ≤ CM*m at hM; nlinarith
      have hh := mul_le_mul_of_nonneg_left hMM hF
      dsimp [G]
      nlinarith
    exact hdegree.trans ((linear_le_exp_quartic_cost G z L hG.le).trans
      (hsmall (G + 1) (by dsimp [C']; linarith)))
  · simp only [neg_mul]
    rw [normalizedProfile_width_eq]
    have hheight : 0 ≤ rowLogHeight C z β L := by
      unfold rowLogHeight historyPolynomialCost
      have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      positivity
    have hwidth := (coarseProfile_width_le D (Δ:=a*(⌊z*L⌋₊:ℝ)) (W:=Wl) hheight).trans
      (((numeric_inputs_cost Wl hβ hz hC hCD ha).2 L).2 (D:ℝ) (Nat.cast_nonneg _) hD)
    have hbase : 1 ≤ Real.exp (historyPolynomialCost K z 4 L) :=
      Real.one_le_exp (mul_nonneg hK.le (by positivity))
    have hh := mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ 2*(2:ℝ)^j)
    have hconst := le_mul_of_one_le_right
      (show 0 ≤ 3 + 2*|Wc| by positivity) hbase
    have htotal : 3 + 2*Wc + (2*(2:ℝ)^j)*
        ((-(a*(⌊z*L⌋₊:ℝ)) + Wl) - coarseLower D (rowLogHeight C z β L)
          (a*(⌊z*L⌋₊:ℝ)) Wl) ≤ R * Real.exp (historyPolynomialCost K z 4 L) := by
      dsimp [R]
      linarith [le_abs_self Wc]
    exact htotal.trans ((constant_mul_exp_quartic_cost R K z L hR.le).trans
      (hsmall (R + K) (by dsimp [C']; linarith)))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
