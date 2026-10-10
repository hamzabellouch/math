import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentActions
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalPrior

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTransport
open TemplateSupportRemoval Template
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem fullProductMean_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (π : ι ≃ κ)
    (S : κ → Finset ℤ) (μ : κ → ℤ → ℝ) (f : (ι → ℤ) → ℂ) :
    fullProductMean (fun i=>S (π i)) (fun i=>μ (π i)) f =
      fullProductMean S μ (fun a=>f (fun i=>a (π i))) := by
  unfold fullProductMean
  apply Finset.sum_bij (fun a _=>fun i=>a (π.symm i))
  · intro a ha
    exact Fintype.mem_piFinset.mpr (fun i=>by
      simpa only [π.apply_symm_apply] using Fintype.mem_piFinset.mp ha (π.symm i))
  · intro a ha b hb hab
    funext i
    simpa only [π.symm_apply_apply] using congrFun hab (π i)
  · intro b hb
    refine ⟨fun i=>b (π i),Fintype.mem_piFinset.mpr (fun i=>Fintype.mem_piFinset.mp hb (π i)),?_⟩
    funext i
    exact congrArg b (π.apply_symm_apply i)
  · intro a ha
    have hp : (∏i,μ (π i) (a i)) = ∏i,μ i (a (π.symm i)) := by
      simpa only [π.symm_apply_apply] using π.prod_comp (fun i=>μ i (a (π.symm i)))
    simp only [π.symm_apply_apply,hp]

theorem fullProductMean_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm ι) (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ)
    (hS : ∀i,S (π i)=S i) (hμ : ∀i,μ (π i)=μ i) (f : (ι → ℤ) → ℂ) :
    fullProductMean S μ (fun a=>f (fun i=>a (π i)))=fullProductMean S μ f := by
  have hh := fullProductMean_reindex π S μ f
  simpa only [hS,hμ] using hh.symm

theorem fullProductMean_perm_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : Equiv.Perm ι) (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ)
    (hS : ∀i,S (π i)=S i) (hμ : ∀i,μ (π i)=μ i)
    (f g : (ι → ℤ) → ℂ) :
    ‖fullProductMean S μ (fun a=>f (fun i=>a (π i)))-
      fullProductMean S μ (fun a=>g (fun i=>a (π i)))‖ =
    ‖fullProductMean S μ f-fullProductMean S μ g‖ := by
  rw [fullProductMean_perm π S μ hS hμ f,fullProductMean_perm π S μ hS hμ g]

theorem constituentPrimePrior_assignment_error {Q : ℕ} (T : Layout) (width : Role → ℕ)
    (E : T.Constituent width → Finset (Preliminaries.PrimeUpTo Q))
    (hE : ∀i,0<primeShellMass (E i)) (π : Equiv.Perm (T.Constituent width))
    (hπ : ∀i,E (π i)=E i)
    (f g : (T.Constituent width → Preliminaries.PrimeUpTo Q) → ℂ) :
    ‖(constituentPrimePrior T width E hE).cmean (fun x=>f (constituentAssignment T width π x))-
      (constituentPrimePrior T width E hE).cmean (fun x=>g (constituentAssignment T width π x))‖ =
    ‖(constituentPrimePrior T width E hE).cmean f-
      (constituentPrimePrior T width E hE).cmean g‖ := by
  rw [constituentPrimePrior_cmean_assignment T width E hE π hπ f,
    constituentPrimePrior_cmean_assignment T width E hE π hπ g]

end Ostmann.Characters.TemplateOneSidedSupportTransport

end

end OAI
