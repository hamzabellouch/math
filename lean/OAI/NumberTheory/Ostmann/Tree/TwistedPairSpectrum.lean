import OAI.NumberTheory.Ostmann.Tree.PairTotalMass
import OAI.NumberTheory.Ostmann.Tree.UniformMellin

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def twistedPairFourier (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) : ℂ :=
  fourier (fun d => pairSpectrum g χ ((σ:ZMod p)*d)*α d) a

theorem l2Sq_unitMul (f : ZMod p → ℂ) (σ : (ZMod p)ˣ) :
    l2Sq (fun d => f ((σ:ZMod p)*d))=l2Sq f := by
  unfold l2Sq
  congr 1
  exact (Equiv.mulLeft₀ (σ:ZMod p) (Units.ne_zero σ)).bijective.sum_comp (fun d => ‖f d‖^2)

theorem mulChar_norm_le_one (α : MulChar (ZMod p) ℂ) (d : ZMod p) : ‖α d‖≤1 := by
  by_cases hd : d=0
  · simp [hd,MulChar.map_zero]
  · exact le_of_eq (mulChar_norm_unit α (Units.mk0 d hd))

theorem twistedPairFourier_energy (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ‖twistedPairFourier g σ χ α a‖^2) ≤ pairFourthMass g χ := by
  rw [pairFourthMass_eq_l2Sq]
  change (∑ a, ‖fourier (fun d => pairSpectrum g χ ((σ:ZMod p)*d)*α d) a‖^2) ≤ _
  rw [fourier_parseval,← l2Sq_unitMul (pairSpectrum g χ) σ]
  unfold l2Sq
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul,mul_pow]
  have h := pow_le_pow_left₀ (norm_nonneg (α d)) (mulChar_norm_le_one α d) 2
  exact (mul_le_mul_of_nonneg_left h (sq_nonneg _)).trans_eq (by simp)

theorem twistedPairFourier_uniform (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (hσ : (σ:ZMod p)^2=1) (hg0 : g 0=0) (hg : l2Sq g≤1)
    (η : MulChar (ZMod p) ℂ) (a : ZMod p) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖twistedPairFourier g σ χ (χ*η) a‖^2) ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*
        ((correlationBound g:ℝ)^4+Real.sqrt (3/(p:ℝ))) := by
  simpa only [twistedPairFourier,MulChar.mul_apply,mul_assoc] using
    uniform_mellin_bound g η a σ hσ hg0 hg

end
end Ostmann.FiniteField

end OAI
