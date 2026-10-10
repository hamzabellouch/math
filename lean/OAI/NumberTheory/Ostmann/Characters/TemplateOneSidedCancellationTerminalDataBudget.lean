import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationProfileBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalData

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open TemplateOneSidedNumericInputs TemplateOneSidedBudget Arithmetic

theorem exists_terminal_source_profile_budget (k j : ℕ) (ρ : 𝓢(ℝ,ℂ))
    {z a C CD CM β : ℝ} (Wl : ℝ) (hz : 0 < z) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hCD : 0 ≤ CD) (hCM : 0 ≤ CM) (hβ : 0 ≤ β) :
    ∃C' : ℝ,0 < C' ∧ ∀L : ℝ,∀D M : ℕ,
      (D:ℝ) ≤ CD*(1+(⌊z*L⌋₊:ℝ)) → (M:ℝ) ≤ CM*(1+(⌊z*L⌋₊:ℝ)) →
      Real.exp ((-a*(⌊z*L⌋₊:ℝ)+Wl)/2)*leafProfileBound ρ ≤
        Real.exp (historyPolynomialCost C' z 4 L) ∧
      ((2*sourceDegreeFactor k j*(M+1)+1:ℕ):ℝ) ≤
        Real.exp (historyPolynomialCost C' z 4 L) ∧
      3+(∑_i:Fin (2^j) ⊕ Fin (2^j),
        ((-a*(⌊z*L⌋₊:ℝ)+Wl)-coarseLower D (rowLogHeight C z β L)
          (a*(⌊z*L⌋₊:ℝ)) Wl)) ≤ Real.exp (historyPolynomialCost C' z 4 L) := by
  obtain ⟨C',hC',hb⟩ := exists_normalized_source_profile_budget k j ρ Wl 0 hz ha hC hCD hCM hβ
  refine ⟨C',hC',?_⟩
  intro L D M hD hM
  obtain ⟨hp,hd,hw⟩ := hb L D M hD hM
  refine ⟨(le_max_right _ _).trans hp,?_,?_⟩
  · apply le_trans _ hd
    exact_mod_cast (show 2*sourceDegreeFactor k j*(M+1)+1 ≤
      (6+2*sourceDegreeFactor k j)*(M+1)+1 by nlinarith)
  · simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,
      neg_zero,sub_self,zero_add,add_zero] using hw

theorem terminalProfile_linear_budgets (k j N m Cw : ℕ) (hN : N ≤ Cw*(m+1)) :
    (obstructionSizeFactor k j*(2*(N+1)+1):ℝ) ≤
      (obstructionSizeFactor k j*(2*Cw+3):ℕ)*(1+(m:ℝ)) ∧
    (2*(N+1):ℝ) ≤ (2*(Cw+1):ℕ)*(1+(m:ℝ)) := by
  have hD : obstructionSizeFactor k j*(2*(N+1)+1) ≤
      (obstructionSizeFactor k j*(2*Cw+3))*(m+1) := by
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    nlinarith
  have hM : 2*(N+1) ≤ (2*(Cw+1))*(m+1) := by nlinarith
  constructor
  · have hh := (show ((obstructionSizeFactor k j*(2*(N+1)+1):ℕ):ℝ) ≤
      (((obstructionSizeFactor k j*(2*Cw+3))*(m+1):ℕ):ℝ) from by exact_mod_cast hD)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_comm (m:ℝ) 1] using hh
  · have hh := (show ((2*(N+1):ℕ):ℝ) ≤ (((2*(Cw+1))*(m+1):ℕ):ℝ) from by exact_mod_cast hM)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,add_comm (m:ℝ) 1] using hh

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
