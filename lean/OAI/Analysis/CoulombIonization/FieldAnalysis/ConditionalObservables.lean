import Mathlib
import OAI.Analysis.CoulombIonization.Variational.BlockSwap
import OAI.Analysis.CoulombIonization.FieldAnalysis.ConditionalFieldIdentity

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombNeumann

lemma weighted_coreSlice_integrable {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (F : Configuration M → ℝ)
    (hF : ∀ t : Spins N, Integrable (fun p : Configuration M × Configuration N =>
      F p.1*‖(swapBlocks ψ).value (joinLists s t) (joinLists p.1 p.2)‖^2)) :
    Integrable (fun x => F x*formMass (coreSlice ψ s x)) := by
  have hi (t : Spins N) : Integrable (fun x : Configuration M =>
      F x*(∫ y : Configuration N, ‖(coreSlice ψ s x).value t y‖^2)) := by
    simpa only [swapBlocks_value,coreSlice,integral_const_mul] using (hF t).integral_prod_left
  simpa only [formMass,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun t _ => hi t)

lemma retained_pressure_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b) (s : Spins M)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Integrable (fun x => retainedPressure b (S x) x*formMass (coreSlice ψ s x)) :=
  weighted_coreSlice_integrable ψ s _ (fun t => retained_pressure_join_integrable
    (swapBlocks_sobolev hψ) hb (fun p => S p.1) (fun i => measurable_fst (hS i)) s t)

lemma retained_direct_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b) (s : Spins M)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Integrable (fun x => retainedDirect b (S x) x*formMass (coreSlice ψ s x)) :=
  weighted_coreSlice_integrable ψ s _ (fun t => retained_direct_join_integrable
    (swapBlocks_sobolev hψ) hb (fun p => S p.1) (fun i => measurable_fst (hS i)) s t)

lemma conditionalFieldParticle_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (s : Spins M) (i : Fin M) :
    Integrable (fun x => formMass (coreSlice ψ s x)*normalizedCoreField Z lam (coreSlice ψ s x) (x i)) := by
  have hh := (((coreSlice_mass_div_integrable hψ s i).const_mul Z).sub
    (coreSlice_cross_integrable hψ s i)).sub ((hψ.coreSlice_mass_integrable s).const_mul lam)
  apply hh.congr
  filter_upwards [hψ.ae_coreSlice s] with x hx
  simp only [Pi.sub_apply]
  rw [mul_comm (formMass _),normalizedCoreField_mul_mass hx]
  ring

def conditionalRetainedFieldSum {N M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+M))
    (s : Spins M) (S : Configuration M → Finset (Fin M)) (x : Configuration M) : ℝ :=
  formMass (coreSlice ψ s x)*∑ i ∈ S x, normalizedCoreField Z lam (coreSlice ψ s x) (x i)

lemma conditionalRetainedFieldSum_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (s : Spins M)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {x | i ∈ S x}) :
    Integrable (conditionalRetainedFieldSum Z lam ψ s S) := by
  classical
  have hi (i : Fin M) := (conditionalFieldParticle_integrable hψ Z lam s i).indicator (hS i)
  have he (x : Configuration M) : conditionalRetainedFieldSum Z lam ψ s S x =
      ∑ i : Fin M, if i ∈ S x then
        formMass (coreSlice ψ s x)*normalizedCoreField Z lam (coreSlice ψ s x) (x i) else 0 := by
    simp only [conditionalRetainedFieldSum,Finset.mul_sum,Finset.sum_ite_mem,Finset.univ_inter]
  change Integrable (fun x => conditionalRetainedFieldSum Z lam ψ s S x)
  simp_rw [he]
  exact integrable_finsetSum _ (fun i _ => by
    convert hi i using 1
    funext x
    simp only [Set.indicator_apply,Set.mem_ofPred_eq])

end CoulombAtom

end

end OAI
