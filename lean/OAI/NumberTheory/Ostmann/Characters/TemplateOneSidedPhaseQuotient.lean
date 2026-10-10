import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrencePhase
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryReindex

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def permutedGraph {I : Type*} (B : I → I → ℤ) (σ : Equiv.Perm I) : I → I → ℤ :=
  fun i h=>B (σ i) (σ h)

theorem actualHistoryPhase_permutation (k j : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (a : ∀i,ZMod (p i))
    (s : ℤ) (t : HistoryReconstruction.Tree j) :
    actualHistoryPhase k j width (fun i=>p (σ.symm i))
      (fun i=>χ (σ.symm i)) (fun i=>a (σ.symm i)) s t =
      (∏i,ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i)))*
        primeGraphPhase (permutedGraph (constituentGraph k j width) σ) p χ
          (fun i=>actualHistoryUnary k width (χ i) j s t (σ i)) := by
  let : ∀i,NeZero (p i) := fun i=>⟨(Fact.out : (p i).Prime).ne_zero⟩
  unfold actualHistoryPhase
  rw [crtPhase_product_reindex σ.symm p a s]
  congr 1
  simpa only [permutedGraph,Equiv.apply_symm_apply] using
    primeGraphPhase_reindex σ.symm (permutedGraph (constituentGraph k j width) σ) p χ
      (fun i=>actualHistoryUnary k width (χ i) j s t (σ i))

theorem primeGraphPhase_div {I : Type*} [Fintype I] [DecidableEq I]
    (B C : I → I → ℤ) (hB : ∀i,B i i=0) (hC : ∀i,C i i=0)
    (p : I → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (ν ξ : I → ℂ) :
    primeGraphPhase B p χ ν / primeGraphPhase C p χ ξ =
      primeGraphPhase (fun i h=>B i h-C i h) p χ (fun i=>ν i/ξ i) := by
  unfold primeGraphPhase
  rw [←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [←div_mul_div_comm,←Finset.prod_div_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro h _
  by_cases he : h=i
  · subst h
    simp only [hB,hC,sub_self,zpow_zero,div_self one_ne_zero]
  · have hz : χ i (p h)≠0 := by
      have hn := norm_prime_character_power p hc i h (χ i) 1 (by simp [he])
      simp only [zpow_one] at hn
      intro hz
      simp only [hz,norm_zero] at hn
      norm_num at hn
    exact (zpow_sub₀ hz (B i h) (C i h)).symm

theorem actualHistoryPhase_quotient (k j : ℕ) (width : Role → ℕ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h=>(p i).Coprime (p h)))
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (a : ∀i,ZMod (p i))
    (s : ℤ) (t u : HistoryReconstruction.Tree j) :
    actualHistoryPhase k j width (fun i=>p (σ.symm i))
        (fun i=>χ (σ.symm i)) (fun i=>a (σ.symm i)) s t /
      actualHistoryPhase k j width (fun i=>p (ρ.symm i))
        (fun i=>χ (ρ.symm i)) (fun i=>a (ρ.symm i)) s u =
      primeGraphPhase
        (fun i h=>permutedGraph (constituentGraph k j width) σ i h-
          permutedGraph (constituentGraph k j width) ρ i h) p χ
        (fun i=>actualHistoryUnary k width (χ i) j s t (σ i)/
          actualHistoryUnary k width (χ i) j s u (ρ i)) := by
  rw [actualHistoryPhase_permutation,actualHistoryPhase_permutation]
  have hA : (∏i,ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i)))≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hn := (ZMod.stdAddChar:AddChar (ZMod (p i)) ℂ).norm_apply
      (-(a i*Construction.crtFrequency p s i))
    intro hz
    rw [hz,norm_zero] at hn
    norm_num at hn
  rw [mul_div_mul_left _ _ hA]
  apply primeGraphPhase_div _ _ _ _ p hc χ
  · intro i
    simp [permutedGraph,constituentGraph,liftGraph]
  · intro i
    simp [permutedGraph,constituentGraph,liftGraph]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
