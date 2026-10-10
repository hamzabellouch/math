import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceUnitAmplitude
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhase

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries
attribute [local instance] Classical.propDecidable

def extendUnitData {I : Type*} {Q : ℕ} (ζ : I → PrimeUpTo Q → ℂ) (i : I) (q : ℕ) : ℂ :=
  if h : q ∈ Q.primesLE then ζ i ⟨q,h⟩ else 1

@[simp] theorem extendUnitData_prime {I : Type*} {Q : ℕ}
    (ζ : I → PrimeUpTo Q → ℂ) (i : I) (p : PrimeUpTo Q) : extendUnitData ζ i p.val = ζ i p := by
  simp only [extendUnitData,dite_eq_left p.property]

theorem norm_extendUnitData {I : Type*} {Q : ℕ}
    (ζ : I → PrimeUpTo Q → ℂ) (hζ : ∀i p,‖ζ i p‖ = 1) (i : I) (q : ℕ) :
    ‖extendUnitData ζ i q‖ = 1 := by
  unfold extendUnitData
  split_ifs <;> simp [hζ]

section
variable {I : Type*} [Fintype I] [DecidableEq I]

def pairedUnitUnary (ζ : I → ℕ → ℂ) (σ ρ : Equiv.Perm I) (i : I) (q : ℕ) : ℂ :=
  ζ (σ i) q * conj (ζ (ρ i) q)

def longUnitFactor (ζ : I → ℕ → ℂ) (σ ρ : Equiv.Perm I) (p : I → ℕ)
    (L S : I) (q : ℕ) : ℂ :=
  pairedUnitUnary ζ σ ρ L q * ∏i ∈ frozenVertices L S,pairedUnitUnary ζ σ ρ i (p i)

def shortUnitFactor (ζ : I → ℕ → ℂ) (σ ρ : Equiv.Perm I) (S : I) (r : ℕ) : ℂ :=
  pairedUnitUnary ζ σ ρ S r

theorem pairedUnitProduct_split (ζ : I → ℕ → ℂ) (σ ρ : Equiv.Perm I) (p : I → ℕ)
    (L S : I) (hLS : L ≠ S) :
    (∏i,ζ i (p (σ.symm i))) * conj (∏i,ζ i (p (ρ.symm i))) =
      longUnitFactor ζ σ ρ p L S (p L) * shortUnitFactor ζ σ ρ S (p S) := by
  have hσ : (∏i,ζ i (p (σ.symm i))) = ∏i,ζ (σ i) (p i) := by
    simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp σ (fun i => ζ i (p (σ.symm i)))).symm
  have hρ : (∏i,ζ i (p (ρ.symm i))) = ∏i,ζ (ρ i) (p i) := by
    simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp ρ (fun i => ζ i (p (ρ.symm i)))).symm
  rw [hσ,hρ,map_prod,←Finset.prod_mul_distrib]
  change (∏i,pairedUnitUnary ζ σ ρ i (p i)) = _
  rw [prod_split_two L S hLS]
  simp only [longUnitFactor,shortUnitFactor]
  ring

@[simp] theorem norm_longUnitFactor (ζ : I → ℕ → ℂ) (hζ : ∀i q,‖ζ i q‖ = 1)
    (σ ρ : Equiv.Perm I) (p : I → ℕ) (L S : I) (q : ℕ) :
    ‖longUnitFactor ζ σ ρ p L S q‖ = 1 := by
  simp [longUnitFactor,pairedUnitUnary,norm_prod,hζ]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem norm_shortUnitFactor (ζ : I → ℕ → ℂ) (hζ : ∀i q,‖ζ i q‖ = 1)
    (σ ρ : Equiv.Perm I) (S : I) (r : ℕ) : ‖shortUnitFactor ζ σ ρ S r‖ = 1 := by
  simp [shortUnitFactor,pairedUnitUnary,hζ]

theorem longUnitFactor_twoPrimeAssignment (ζ : I → ℕ → ℂ) (σ ρ : Equiv.Perm I) (p : I → ℕ)
    (L S : I) (q r z : ℕ) :
    longUnitFactor ζ σ ρ (twoPrimeAssignment p L S q r) L S z = longUnitFactor ζ σ ρ p L S z := by
  unfold longUnitFactor
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [twoPrimeAssignment_frozen p L S q r i hi]
end

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
