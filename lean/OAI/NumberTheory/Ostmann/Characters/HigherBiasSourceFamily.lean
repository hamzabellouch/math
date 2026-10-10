import OAI.NumberTheory.Ostmann.Characters.HigherBiasSelection
import OAI.NumberTheory.Ostmann.Characters.TypicalEndpoints
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionTransfer

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters
open Ostmann.Preliminaries Ostmann.Construction
open scoped BigOperators

structure HigherBiasSourceFamily (d : Decomposition) (Q : ℕ)
    (E : Finset (PrimeUpTo Q)) (δ : ℝ) where
  character : (p : PrimeUpTo Q) → MulChar (ZMod p.val) ℂ
  center : (p : PrimeUpTo Q) → ZMod p.val
  phase : PrimeUpTo Q → ℂ
  phase_unit : ∀ p, ‖phase p‖ = 1
  higher_order : ∀ p ∈ E, 2 < orderOf (character p)
  positive_mean : ∀ p ∈ E,
    δ ≤ (((d.residueSupport p.val).card : ℂ)⁻¹ *
      ∑ x ∈ d.residueSupport p.val,phase p * character p (x-center p)).re

namespace HigherBiasSourceFamily
variable {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)} {δ : ℝ}

def test (F : HigherBiasSourceFamily d Q E δ) (p : PrimeUpTo Q) (x : ZMod p.val) : ℂ :=
  F.phase p * F.character p (x-F.center p)

theorem test_norm_le_one (F : HigherBiasSourceFamily d Q E δ)
    (p : PrimeUpTo Q) (x : ZMod p.val) : ‖F.test p x‖ ≤ 1 := by
  rw [test,norm_mul,F.phase_unit,one_mul]
  exact norm_character_le_one _ _

theorem shell_residue_mean_lower (F : HigherBiasSourceFamily d Q E δ)
    (G : Finset (PrimeUpTo Q)) (hG : G ⊆ E) (hm : 0 < primeShellMass G) :
    δ ≤ ((primeShellPrior G hm).cmean (fun p =>
      (∑ x ∈ d.residueSupport p.val,F.test p x)/
        ((d.residueSupport p.val).card : ℂ))).re := by
  rw [prior_cmean_re]
  calc
    δ = (primeShellPrior G hm).mean (fun _ => δ) := ((primeShellPrior G hm).mean_const δ).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpg : p ∈ G
      · apply mul_le_mul_of_nonneg_left _ ((primeShellPrior G hm).mass_nonneg p)
        have hh := F.positive_mean p (hG hpg)
        simpa only [test,div_eq_mul_inv,mul_comm] using hh
      · simp only [primeShellPrior_mass,ite_eq_right hpg,zero_div,zero_mul,le_refl]

end HigherBiasSourceFamily

theorem exists_higherBiasSourceFamily (d : Decomposition) (Q : ℕ)
    (E : Finset (PrimeUpTo Q)) (δ : ℝ) (hδ : 0 < δ)
    (hbias : ∀ p ∈ E,δ ≤ (higherBias (d.residueSupport p.val) : ℝ)) :
    Nonempty (HigherBiasSourceFamily d Q E δ) := by
  classical
  have hchoice : ∀ p : PrimeUpTo Q,∃ χ : MulChar (ZMod p.val) ℂ,
      ∃ a : ZMod p.val,∃ z : ℂ,‖z‖=1 ∧
        (p∈E → 2 < orderOf χ ∧ δ ≤ (((d.residueSupport p.val).card : ℂ)⁻¹ *
          ∑ x ∈ d.residueSupport p.val,z*χ (x-a)).re) := by
    intro p
    by_cases hp : p ∈ E
    · obtain ⟨χ,a,z,horder,hz,_hnorm,hm⟩ :=
        exists_positive_character_test (d.residueSupport p.val) δ hδ (hbias p hp)
      exact ⟨χ,a,z,hz,fun _ => ⟨horder,hm⟩⟩
    · exact ⟨1,0,1,by simp,fun he => False.elim (hp he)⟩
  choose χ a z hz hh using hchoice
  exact ⟨⟨χ,a,z,hz,fun p hp => (hh p hp).1,fun p hp => (hh p hp).2⟩⟩

end Ostmann.Characters

end

end OAI
