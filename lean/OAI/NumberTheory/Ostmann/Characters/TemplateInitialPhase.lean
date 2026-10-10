import OAI.NumberTheory.Ostmann.Characters.CharacterInitialPhase
import OAI.NumberTheory.Ostmann.Characters.TemplateConstituents

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

def primeGraphPhase {ι:Type*} [Fintype ι] (B:ι→ι→ℤ) (p:ι→ℕ)
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (ν:ι→ℂ) : ℂ :=
  ∏i,ν i*∏j,χ i (p j)^B i j

theorem complete_graph_row {ι:Type*} [Fintype ι] [DecidableEq ι]
    (z:ι→ℂ) (i:ι) :
    (∏j:ι,z j^(if i=j then (0:ℤ) else 1)) =
      ∏j∈Finset.univ.erase i,z j := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true,zpow_zero,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  simp [Ne.symm hji]

theorem initialPhase_eq_constituentGraph (k:ℕ) (width:Role→ℕ)
    (p:(schedule k 0).Constituent width→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i)) (s:ℤ) :
    initialPhase p χ a s = primeGraphPhase (constituentGraph k 0 width) p χ
      (initialUnary p χ a s) := by
  classical
  unfold initialPhase primeGraphPhase
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  have he (j:(schedule k 0).Constituent width) :
      constituentGraph k 0 width i j=if i=j then 0 else 1 := by
    by_cases h:i=j
    · subst j; simp [constituentGraph,liftGraph]
    · rw [constituentGraph_zero k width i j h,ite_eq_right h]
  simp_rw [he]
  exact (complete_graph_row _ i).symm

end Ostmann.Characters.Template

end

end OAI
