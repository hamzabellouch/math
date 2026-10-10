import OAI.NumberTheory.Ostmann.Tree.SpectralFourth
import OAI.NumberTheory.Ostmann.Tree.SpectralGaussBound

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def nonprincipalEnergy (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) : ℝ := by
  classical
  exact if α=1 then 0 else ‖twistedPairFourier g σ χ α a‖^2

def principalEnergy (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) : ℝ := by
  classical
  exact if α=1 then ‖twistedPairFourier g σ χ α a‖^2 else 0

theorem spectralEnergy_decomposition (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖twistedPairFourier g σ χ α a‖^2=
      nonprincipalEnergy g σ χ α a+principalEnergy g σ χ α a := by
  classical
  by_cases h : α=1 <;> simp [nonprincipalEnergy,principalEnergy,h]

theorem nonprincipalEnergy_nonneg (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) : 0≤nonprincipalEnergy g σ χ α a := by
  classical
  unfold nonprincipalEnergy
  split_ifs <;> positivity

theorem principalEnergy_nonneg (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) : 0≤principalEnergy g σ χ α a := by
  classical
  unfold principalEnergy
  split_ifs <;> positivity

theorem nonprincipalEnergy_le (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    nonprincipalEnergy g σ χ α a≤(p:ℝ)⁻¹*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  classical
  unfold nonprincipalEnergy
  split_ifs with hα
  · positivity
  · exact norm_twistedPairFourier_nonprincipal_sq_le g σ χ α hα a hg0 hg

theorem nonprincipalEnergy_fourth (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ α : MulChar (ZMod p) ℂ,
      ∑ a : ZMod p, nonprincipalEnergy g σ χ α a^2) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^3*(4*(correlationBound g:ℝ)^2+3/(p:ℝ)) := by
  classical
  have he (χ α : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, nonprincipalEnergy g σ χ α a^2) =
      if α=1 then 0 else ∑ a : ZMod p, ‖fourier (fun d => pairSpectrum g χ d*α d) a‖^4 := by
    by_cases hα : α=1
    · simp [nonprincipalEnergy,hα]
    · simp only [nonprincipalEnergy,hα,ite_false,norm_twistedPairFourier_scale,← pow_mul]
      exact (Equiv.mulLeft₀ ((σ⁻¹:(ZMod p)ˣ):ZMod p) (Units.ne_zero _)).bijective.sum_comp
        (fun a => ‖fourier (fun d => pairSpectrum g χ d*α d) a‖^4)
  simp_rw [he]
  exact pairSpectrum_nonprincipal_fourth_bound g hg0 hg

theorem pairFourthMass_basic_le (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (hg0 : g 0=0) (hg : l2Sq g≤1) :
    pairFourthMass g χ≤((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  calc
    _ ≤ (∑ a,pairWeight g χ a)^2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => pairWeight_nonneg g χ a)
    _ ≤ _ := by
      rw [pairWeight_mass g χ hg0]
      exact pow_le_pow_left₀ (mul_nonneg (by positivity) (l2Sq_nonneg g))
        ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _)) 2

end
end Ostmann.FiniteField

end OAI
