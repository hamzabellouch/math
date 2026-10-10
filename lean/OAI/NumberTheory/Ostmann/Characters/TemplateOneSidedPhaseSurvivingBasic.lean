import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceSurvivorNormBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseUnitsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem primeGraphPhase_mul_conj {I : Type*} [Fintype I] [DecidableEq I]
    (B C : I → I → ℤ) (hB : ∀i,B i i=0) (hC : ∀i,C i i=0)
    (p : I → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (ν ξ : I → ℂ) :
    primeGraphPhase B p χ ν * conj (primeGraphPhase C p χ ξ) =
      primeGraphPhase (fun i h=>B i h-C i h) p χ (fun i=>ν i*conj (ξ i)) := by
  unfold primeGraphPhase
  rw [map_prod,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_mul,map_prod]
  have hh : (∏h,χ i (p h)^B i h)*(∏h,conj (χ i (p h)^C i h)) =
      ∏h,χ i (p h)^(B i h-C i h) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h _
    by_cases he : h=i
    · subst h
      simp only [hB,hC,sub_self,zpow_zero,map_one,mul_one]
    · have hn := norm_prime_character_power p hc i h (χ i) 1 (by simp [he])
      simp only [zpow_one] at hn
      have hz : χ i (p h)≠0 := by
        intro hz
        rw [hz,norm_zero] at hn
        norm_num at hn
      rw [←Complex.inv_eq_conj (by rw [norm_zpow,hn,one_zpow]),←div_eq_mul_inv]
      exact (zpow_sub₀ hz _ _).symm
  calc
    _ = (ν i*conj (ξ i))*((∏h,χ i (p h)^B i h)*(∏h,conj (χ i (p h)^C i h))) := by ring
    _ = _ := by rw [hh]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
