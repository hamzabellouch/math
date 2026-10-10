import OAI.NumberTheory.Ostmann.Characters.BinaryPriorExposure
import OAI.NumberTheory.Ostmann.Characters.TemplateAdaptedCoordinates
import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction BinaryHaar
attribute [local instance] Classical.propDecidable

def constantLeafMass {α : Type*} [Fintype α] (μ : FinitePrior α) :
    (j : ℕ) → Leaves α j → ℝ
  | 0,x => μ.mass x
  | j+1,x => constantLeafMass μ j x.1 * constantLeafMass μ j x.2

theorem binary_mean_eq_constantLeafMass {α : Type*} [Fintype α]
    (μ : FinitePrior α) (j : ℕ) (p : List Bool) (F : Leaves α j → ℝ) :
    BinaryPriorExposure.mean (fun _=>μ) j p F = ∑x,constantLeafMass μ j x * F x := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    change BinaryPriorExposure.mean (fun _=>μ) j (false::p)
      (fun x=>BinaryPriorExposure.mean (fun _=>μ) j (true::p) (fun y=>F (x,y))) = _
    simp_rw [ih]
    simp only [Fintype.sum_prod_type,constantLeafMass,Finset.mul_sum,mul_assoc]

theorem constantLeafMass_wordTreeEquiv {α : Type*} [Fintype α]
    (μ : FinitePrior α) (k j : ℕ) (z : WordSlot k j → α) :
    constantLeafMass μ j (wordTreeEquiv (G:=α) k j z)=∏i,μ.mass (z i) := by
  induction j with
  | zero =>
    let w : WordSlot k 0 := ⟨(.word,true),by simp [schedule,initial,InitialRole.role]⟩
    have : Subsingleton (WordSlot k 0) := ⟨fun i i'=>Subtype.ext
      ((initial_word_unique k i).trans (initial_word_unique k i').symm)⟩
    exact (Fintype.prod_subsingleton (fun i=>μ.mass (z i)) w).symm
  | succ j ih =>
    change constantLeafMass μ j (wordTreeEquiv (G:=α) k j (splitWords k j true z))*
      constantLeafMass μ j (wordTreeEquiv (G:=α) k j (splitWords k j false z))=∏i,μ.mass (z i)
    rw [ih,ih,← Finset.prod_mul_distrib]
    calc
      _ = ∏q:WordSlot k j×Bool,μ.mass (z ((wordEquiv (schedule k j) j).symm q)) := by
        simp only [Fintype.prod_prod_type,Fintype.prod_bool,splitWords]
      _ = _ := (wordEquiv (schedule k j) j).symm.prod_comp (fun i=>μ.mass (z i))

theorem productPrior_wordTree_mean {α : Type*} [Fintype α]
    (μ : FinitePrior α) (k j : ℕ) (p : List Bool) (F : (WordSlot k j → α) → ℝ) :
    (productPrior (fun _ : WordSlot k j=>μ)).mean F =
      BinaryPriorExposure.mean (fun _=>μ) j p
        (fun x=>F ((wordTreeEquiv (G:=α) k j).symm x)) := by
  rw [binary_mean_eq_constantLeafMass]
  rw [← (wordTreeEquiv (G:=α) k j).sum_comp
    (fun x=>constantLeafMass μ j x * F ((wordTreeEquiv (G:=α) k j).symm x))]
  simp only [Equiv.symm_apply_apply,constantLeafMass_wordTreeEquiv]
  rfl

end Ostmann.Characters.Template

end

end OAI
