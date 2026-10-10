import OAI.NumberTheory.Ostmann.Tree.CharacterFourthNonprincipal
import OAI.NumberTheory.Ostmann.Tree.PairTotalMass
import OAI.NumberTheory.Ostmann.Tree.WeightedFourierGauss

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem fourier_nonprincipal_fourth_bound (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b,fourier f b=(w b:ℂ)) (hw : ∀ b,0≤w b) :
    (∑ α : MulChar (ZMod p) ℂ, if α=1 then 0 else
      ∑ a : ZMod p, ‖fourier (fun d => f d*α d) a‖^4) ≤
      2*(∑ b,w b^2)^2+3*(p:ℝ)⁻¹^2*(∑ b,w b)^4 := by
  classical
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have he (α : MulChar (ZMod p) ℂ) :
      (if α=1 then 0 else ∑ a : ZMod p, ‖fourier (fun d => f d*α d) a‖^4) =
      (p:ℝ)⁻¹^2*(if α⁻¹=1 then 0 else ∑ a : ZMod p, ‖weightedCharacterSum w α⁻¹ a‖^4) := by
    by_cases hα : α=1
    · simp [hα]
    · simp only [hα,ite_false,inv_eq_one,
        norm_fourier_mulChar_fourth f w hf α hα,← Finset.mul_sum]
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hi := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp
    (fun α : MulChar (ZMod p) ℂ => if α=1 then (0:ℝ) else ∑ a : ZMod p, ‖weightedCharacterSum w α a‖^4)
  change (∑ α : MulChar (ZMod p) ℂ, if α⁻¹=1 then (0:ℝ) else ∑ a : ZMod p, ‖weightedCharacterSum w α⁻¹ a‖^4) = _ at hi
  rw [hi]
  have hb := weightedCharacterSum_nonprincipal_fourth_bound w hw
  rw [ZMod.card] at hb
  have hN : (Fintype.card (ZMod p)ˣ:ℝ)≤(p:ℝ) := by
    exact_mod_cast (show Fintype.card (ZMod p)ˣ≤p by rw [ZMod.card_units]; omega)
  calc
    _ ≤ (p:ℝ)⁻¹^2*(2*(Fintype.card (ZMod p)ˣ:ℝ)*(p:ℝ)*(∑ b,w b^2)^2+3*(∑ b,w b)^4) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ (p:ℝ)⁻¹^2*(2*(p:ℝ)*(p:ℝ)*(∑ b,w b^2)^2+3*(∑ b,w b)^4) := by
      gcongr
    _ = _ := by field_simp

theorem pairSpectrum_nonprincipal_fourth_bound (g : ZMod p → ℂ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ α : MulChar (ZMod p) ℂ,
      if α=1 then 0 else ∑ a : ZMod p, ‖fourier (fun d => pairSpectrum g χ d*α d) a‖^4) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*((4:ℝ)*(correlationBound g:ℝ)^2+3/(p:ℝ)) := by
  let C : ℝ := (p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ)
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hN : 0<(Fintype.card (ZMod p)ˣ:ℝ) := by exact_mod_cast Fintype.card_pos
  have hC : 0≤C := div_nonneg hp.le hN.le
  have hr (χ : MulChar (ZMod p) ℂ) : 0≤pairFourthMass g χ := by unfold pairFourthMass; positivity
  have hrmax (χ : MulChar (ZMod p) ℂ) : pairFourthMass g χ≤C^2*(correlationBound g:ℝ)^2 := by
    exact (pairFourthMass_le g χ hg0).trans
      ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _))
  have hr2 : (∑ χ : MulChar (ZMod p) ℂ,pairFourthMass g χ^2) ≤
      2*C^3*(correlationBound g:ℝ)^2 := by
    calc
      _ ≤ ∑ χ : MulChar (ZMod p) ℂ, (C^2*(correlationBound g:ℝ)^2)*pairFourthMass g χ := by
        apply Finset.sum_le_sum
        intro χ _
        simpa only [pow_two] using mul_le_mul_of_nonneg_right (hrmax χ) (hr χ)
      _ = (C^2*(correlationBound g:ℝ)^2)*(∑ χ : MulChar (ZMod p) ℂ,pairFourthMass g χ) := by rw [Finset.mul_sum]
      _ ≤ (C^2*(correlationBound g:ℝ)^2)*(2*C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [C,mul_div_assoc] using pairFourthMass_total g hg0 hg
      _ = _ := by ring
  have hJ (χ : MulChar (ZMod p) ℂ) : (∑ b,pairWeight g χ b)^4≤C^4 := by
    rw [pairWeight_mass g χ hg0]
    exact pow_le_pow_left₀ (mul_nonneg hC (l2Sq_nonneg g))
      ((mul_le_mul_of_nonneg_left hg hC).trans_eq (mul_one _)) 4
  calc
    _ ≤ ∑ χ : MulChar (ZMod p) ℂ,
        (2*(pairFourthMass g χ)^2+3*(p:ℝ)⁻¹^2*C^4) := by
      apply Finset.sum_le_sum
      intro χ _
      have hh := fourier_nonprincipal_fourth_bound (pairSpectrum g χ) (pairWeight g χ)
        (fourier_pairSpectrum g χ) (pairWeight_nonneg g χ)
      exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hJ χ) (by positivity)))
    _ = 2*(∑ χ : MulChar (ZMod p) ℂ,pairFourthMass g χ^2)+
        (Fintype.card (ZMod p)ˣ:ℝ)*(3*(p:ℝ)⁻¹^2*C^4) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,mulChar_card,nsmul_eq_mul]
    _ ≤ 2*(2*C^3*(correlationBound g:ℝ)^2)+(Fintype.card (ZMod p)ˣ:ℝ)*(3*(p:ℝ)⁻¹^2*C^4) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hr2 (by norm_num)) le_rfl
    _ = _ := by dsimp [C]; field_simp; ring

end
end Ostmann.FiniteField

end OAI
