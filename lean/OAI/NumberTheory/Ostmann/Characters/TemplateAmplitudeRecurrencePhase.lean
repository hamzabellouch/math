import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateInitialUnary
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseRowNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def actualHistoryPhase (k j : ℕ) (width : Role → ℕ)
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (a : ∀i,ZMod (p i))
    (s : ℤ) (t : HistoryReconstruction.Tree j) : ℂ :=
  (∏i,ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i)))*
    primeGraphPhase (constituentGraph k j width) p χ
      (fun i => actualHistoryUnary k width (χ i) j s t i)

theorem actualHistoryPhase_zero (k : ℕ) (width : Role → ℕ)
    (p : (schedule k 0).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (a : ∀i,ZMod (p i)) (s : ℤ)
    (t : HistoryReconstruction.Tree 0) :
    actualHistoryPhase k 0 width p χ a s t = initialPhase p χ a s := by
  rw [initialPhase_separate]
  have hg : constituentGraph k 0 width=
      (fun i h : (schedule k 0).Constituent width => if i=h then (0:ℤ) else 1) := by
    funext i h
    by_cases he:i=h
    · subst h; simp [constituentGraph,liftGraph]
    · rw [constituentGraph_zero k width i h he,ite_eq_right he]
  simp only [actualHistoryPhase,hg,actualHistoryUnary,historyUnary]

theorem norm_actualHistoryPhase (k j : ℕ) (width : Role → ℕ)
    (p : (schedule k j).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h => (p i).Coprime (p h)))
    (χ : ∀i,MulChar (ZMod (p i)) ℂ) (hχ : ∀i,χ i≠1)
    (a : ∀i,ZMod (p i)) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : ∀i,HistoryFrequencyUnits (p i) j s t) :
    ‖actualHistoryPhase k j width p χ a s t‖=1 := by
  have hpow (i h : (schedule k j).Constituent width) :
      ‖χ i (p h)^constituentGraph k j width i h‖=1 := by
    apply norm_prime_character_power p hc i h (χ i)
    intro he
    subst h
    simp [constituentGraph,liftGraph]
  have hadd (i : (schedule k j).Constituent width) :
      ‖ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i))‖=1 :=
    (ZMod.stdAddChar:AddChar (ZMod (p i)) ℂ).norm_apply _
  simp only [actualHistoryPhase,primeGraphPhase,norm_mul,norm_prod,hadd,hpow,
    norm_actualHistoryUnary k width _ (hχ _) j s t (ht _),Finset.prod_const_one,one_mul]

end Ostmann.Characters.Template

end

end OAI
