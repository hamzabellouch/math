import OAI.NumberTheory.Ostmann.Tree.PrincipalSpectrum
import OAI.NumberTheory.Ostmann.Tree.WeightedFourierGauss

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem norm_weightedCharacterSum_le (w : ZMod p → ℝ) (hw : ∀ b,0≤w b)
    (α : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖weightedCharacterSum w α a‖ ≤ ∑ b,w b := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw b)]
  exact (mul_le_mul_of_nonneg_left (mulChar_norm_le_one α (a-b)) (hw b)).trans_eq (mul_one _)

theorem norm_fourier_mulChar_sq_le (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b,fourier f b=(w b:ℂ)) (hw : ∀ b,0≤w b)
    (α : MulChar (ZMod p) ℂ) (hα : α≠1) (a : ZMod p) :
    ‖fourier (fun d => f d*α d) a‖^2 ≤ (p:ℝ)⁻¹*(∑ b,w b)^2 := by
  have hp : 0<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hf4 := norm_fourier_mulChar_fourth f w hf α hα a
  have hS : ‖weightedCharacterSum w α⁻¹ a‖^4 ≤ (∑ b,w b)^4 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_weightedCharacterSum_le w hw α⁻¹ a) 4
  have h4 := mul_le_mul_of_nonneg_left hS (sq_nonneg ((p:ℝ)⁻¹))
  rw [← hf4] at h4
  have hz : 0≤(p:ℝ)⁻¹*(∑ b,w b)^2 := by positivity
  have hz' : 0≤‖fourier (fun d => f d*α d) a‖^2 := sq_nonneg _
  nlinarith only [h4,hz,hz']

theorem norm_twistedPairFourier_nonprincipal_sq_le (g : ZMod p → ℂ)
    (σ : (ZMod p)ˣ) (χ α : MulChar (ZMod p) ℂ) (hα : α≠1)
    (a : ZMod p) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖twistedPairFourier g σ χ α a‖^2 ≤
      (p:ℝ)⁻¹*((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))^2 := by
  rw [norm_twistedPairFourier_scale]
  have hb := norm_fourier_mulChar_sq_le (pairSpectrum g χ) (pairWeight g χ)
    (fourier_pairSpectrum g χ) (pairWeight_nonneg g χ) α hα ((σ⁻¹:(ZMod p)ˣ)*a)
  rw [pairWeight_mass g χ hg0] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (mul_nonneg (by positivity) (l2Sq_nonneg g))
    ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _)) 2

end
end Ostmann.FiniteField

end OAI
