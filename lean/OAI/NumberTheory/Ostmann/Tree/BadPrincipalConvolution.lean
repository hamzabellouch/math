import OAI.NumberTheory.Ostmann.Tree.DoubleMellinEnergy
import OAI.NumberTheory.Ostmann.Tree.SpectralParts

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem principalEnergy_mulInv (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ ν ψ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    principalEnergy g σ χ (ν*ψ⁻¹) a=
      if ψ=ν then ‖twistedPairFourier g σ χ 1 a‖^2 else 0 := by
  classical
  by_cases he : ψ=ν
  · subst ψ
    simp [principalEnergy]
  · have hα : (ν*ψ⁻¹ : MulChar (ZMod p) ℂ)≠1 := by
      intro hmul
      exact he (mul_inv_eq_one.mp hmul).symm
    simp [principalEnergy,he,hα]

theorem principalEnergy_total (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (e : ZMod p ≃ ZMod p) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      principalEnergy g σ ψ (ν*χ⁻¹) (e a)) ≤ 2*(p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ) := by
  classical
  rw [Finset.sum_comm]
  have he (ψ : MulChar (ZMod p) ℂ) :
      (∑ χ : MulChar (ZMod p) ℂ,∑ a : ZMod p,principalEnergy g σ ψ (ν*χ⁻¹) (e a)) =
      ∑ a : ZMod p,‖twistedPairFourier g σ ψ 1 a‖^2 := by
    rw [Finset.sum_comm]
    simp_rw [principalEnergy_mulInv]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact e.sum_comp (fun a => ‖twistedPairFourier g σ ψ 1 a‖^2)
  simp_rw [he]
  exact (Finset.sum_le_sum (fun ψ _ => twistedPairFourier_energy g σ ψ 1)).trans
    (pairFourthMass_total g hg0 hg)

theorem bad_mixed_left_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      nonprincipalEnergy g σ χ (ν*ψ⁻¹) a*principalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) ≤
      2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3/(p:ℝ) := by
  let B : ℝ := (p:ℝ)⁻¹*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2
  calc
    _ ≤ ∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
        B*principalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a) := by
      apply Finset.sum_le_sum
      intro χ _
      apply Finset.sum_le_sum
      intro ψ _
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right (nonprincipalEnergy_le g σ χ _ a hg0 hg)
        (principalEnergy_nonneg h τ ψ _ (-a))
    _ = B*(∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
        principalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) := by simp only [Finset.mul_sum]
    _ ≤ B*(2*(p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)) :=
      mul_le_mul_of_nonneg_left (principalEnergy_total h τ ν⁻¹ (Equiv.neg _) hh0 hh) (by dsimp [B]; positivity)
    _ = _ := by dsimp [B]; ring

theorem bad_mixed_right_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      principalEnergy g σ χ (ν*ψ⁻¹) a*nonprincipalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) ≤
      2*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3/(p:ℝ) := by
  have he : (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      principalEnergy g σ χ (ν*ψ⁻¹) a*nonprincipalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) =
      ∑ ψ : MulChar (ZMod p) ℂ,∑ χ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      nonprincipalEnergy h τ ψ (ν⁻¹*χ⁻¹) a*principalEnergy g σ χ (ν*ψ⁻¹) (-a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ψ _
    apply Finset.sum_congr rfl
    intro χ _
    have hi := (Equiv.neg (ZMod p)).bijective.sum_comp
      (fun a => nonprincipalEnergy h τ ψ (ν⁻¹*χ⁻¹) a*principalEnergy g σ χ (ν*ψ⁻¹) (-a))
    simpa only [Equiv.neg_apply,neg_neg,mul_comm] using hi
  rw [he]
  simpa only [inv_inv] using bad_mixed_left_bound h g τ σ ν⁻¹ hh0 hh hg0 hg

theorem bad_principal_bound (g h : ZMod p → ℂ) (σ τ : (ZMod p)ˣ)
    (ν : MulChar (ZMod p) ℂ) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (hh0 : h 0=0) (hh : l2Sq h≤1) :
    (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      principalEnergy g σ χ (ν*ψ⁻¹) a*principalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) ≤
      (((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*(correlationBound g:ℝ)^2+
        (Fintype.card (ZMod p)ˣ:ℝ)⁻¹)^2 *
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  classical
  let B : ℝ := ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*(correlationBound g:ℝ)^2+
    (Fintype.card (ZMod p)ˣ:ℝ)⁻¹
  have he : (∑ χ : MulChar (ZMod p) ℂ,∑ ψ : MulChar (ZMod p) ℂ,∑ a : ZMod p,
      principalEnergy g σ χ (ν*ψ⁻¹) a*principalEnergy h τ ψ (ν⁻¹*χ⁻¹) (-a)) =
      ∑ a : ZMod p, ‖twistedPairFourier g σ ν⁻¹ 1 a‖^2*‖twistedPairFourier h τ ν 1 (-a)‖^2 := by
    rw [sum_three_rotate]
    apply Finset.sum_congr rfl
    intro a _
    simp only [principalEnergy_mulInv,ite_mul,mul_ite,zero_mul,mul_zero]
    simp
  rw [he]
  calc
    _ ≤ ∑ a : ZMod p,B^2*‖twistedPairFourier h τ ν 1 (-a)‖^2 := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_twistedPairFourier_principal_le g σ ν⁻¹ a hg0 hg) 2) (sq_nonneg _)
    _ = B^2*(∑ a : ZMod p, ‖twistedPairFourier h τ ν 1 a‖^2) := by
      rw [← Finset.mul_sum]
      congr 1
      exact (Equiv.neg (ZMod p)).bijective.sum_comp (fun a => ‖twistedPairFourier h τ ν 1 a‖^2)
    _ ≤ B^2*pairFourthMass h ν := mul_le_mul_of_nonneg_left (twistedPairFourier_energy h τ ν 1) (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (pairFourthMass_basic_le h ν hh0 hh) (sq_nonneg _)

end
end Ostmann.FiniteField

end OAI
