import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedKineticLower
import OAI.Analysis.CoulombIonization.FormDomain.BlockEnergetics

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

def blockSwap (N M : ℕ) : Fin (M+N) ≃ Fin (N+M) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin M) (Fin N)).trans finSumFinEquiv)

@[simp] lemma blockSwap_left (N M : ℕ) (i : Fin M) :
    blockSwap N M (finSumFinEquiv (Sum.inl i)) = finSumFinEquiv (Sum.inr i) := by
  simp [blockSwap]

@[simp] lemma blockSwap_right (N M : ℕ) (i : Fin N) :
    blockSwap N M (finSumFinEquiv (Sum.inr i)) = finSumFinEquiv (Sum.inl i) := by
  simp [blockSwap]

lemma joinLists_blockSwap {N M : ℕ} {α : Type*} (s : Fin M → α) (t : Fin N → α) :
    joinLists s t ∘ (blockSwap N M).symm = joinLists t s := by
  funext i
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  cases j <;> simp [Function.comp_def,blockSwap,joinLists]

def swapBlocks {N M : ℕ} (ψ : FormVector (N+M)) : FormVector (M+N) :=
  reindexForm (blockSwap N M) ψ

@[simp] lemma swapBlocks_value {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (t : Spins N) (x : Configuration M) (y : Configuration N) :
    (swapBlocks ψ).value (joinLists s t) (joinLists x y) =
      ψ.value (joinLists t s) (joinLists y x) := by
  simp only [swapBlocks,reindexForm,joinLists_blockSwap]

lemma swapBlocks_sobolev {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ) :
    SobolevVector (swapBlocks ψ) := hψ.reindex _

@[simp] lemma swapBlocks_mass {N M : ℕ} (ψ : FormVector (N+M)) :
    formMass (swapBlocks ψ) = formMass ψ := formMass_reindex _ _

lemma swapBlocks_coreKinetic {N M : ℕ} (ψ : FormVector (N+M)) :
    coreKinetic (swapBlocks ψ) = outKinetic ψ := by
  have hi (s : Spins (M+N)) (i : Fin M) (a : Fin 3) :
      (∫ x, ‖(swapBlocks ψ).gradient s (finSumFinEquiv (Sum.inl i)) a x‖^2) =
      ∫ x, ‖ψ.gradient (s ∘ (blockSwap N M).symm) (finSumFinEquiv (Sum.inr i)) a x‖^2 := by
    simpa only [swapBlocks,reindexForm,blockSwap_left] using
      integral_reindex (blockSwap N M) (fun x =>
        ‖ψ.gradient (s ∘ (blockSwap N M).symm) (finSumFinEquiv (Sum.inr i)) a x‖^2)
  unfold coreKinetic
  simp_rw [hi]
  exact congrArg (fun z : ℝ => (1/2:ℝ)*z)
    (sum_spin_reindex (blockSwap N M) (fun s => ∑ i : Fin M, ∑ a,
      ∫ x, ‖ψ.gradient s (finSumFinEquiv (Sum.inr i)) a x‖^2))

lemma swapBlocks_coreRepulsion {N M : ℕ} (ψ : FormVector (N+M)) :
    coreRepulsion (swapBlocks ψ) = outRepulsion ψ := by
  unfold coreRepulsion swapBlocks
  have he (s : Spins (M+N)) (i j : Fin M) :
      (∫ x : Configuration (M+N),
        ‖(reindexForm (blockSwap N M) ψ).value s x‖^2 /
          ‖x (finSumFinEquiv (Sum.inl i))-x (finSumFinEquiv (Sum.inl j))‖) =
      ∫ x : Configuration (N+M), ‖ψ.value (s ∘ (blockSwap N M).symm) x‖^2 /
        ‖x (finSumFinEquiv (Sum.inr i))-x (finSumFinEquiv (Sum.inr j))‖ := by
    convert integral_reindex (blockSwap N M) (fun x =>
      ‖ψ.value (s ∘ (blockSwap N M).symm) x‖^2 /
        ‖x (finSumFinEquiv (Sum.inr i))-x (finSumFinEquiv (Sum.inr j))‖) using 1
    simp only [reindexForm,Function.comp_apply,←blockSwap_left N M,
      Equiv.symm_apply_apply]
  simp_rw [he]
  exact sum_spin_reindex (blockSwap N M) (fun s => ∑ i : Fin M, ∑ j : Fin M,
    if i < j then ∫ x, ‖ψ.value s x‖^2 /
      ‖x (finSumFinEquiv (Sum.inr i))-x (finSumFinEquiv (Sum.inr j))‖ else 0)

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann

lemma weighted_coreSlice_reorder {N M : ℕ} (ψ : FormVector (N+M))
    (F : Spins M → Configuration M → ℝ)
    (hF : ∀ s : Spins M, ∀ t : Spins N,
      Integrable (fun p : Configuration M × Configuration N =>
        F s p.1*‖(swapBlocks ψ).value (joinLists s t) (joinLists p.1 p.2)‖^2)) :
    (∑ t : Spins N, ∫ y : Configuration N, ∑ s : Spins M, ∫ x : Configuration M,
      F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2) =
      ∑ s : Spins M, ∫ x : Configuration M, F s x*formMass (coreSlice ψ s x) := by
  have he (s : Spins M) (t : Spins N) :
      (∫ y : Configuration N, ∫ x : Configuration M,
        F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2) =
      ∫ x : Configuration M, F s x*(∫ y : Configuration N,
        ‖(coreSlice ψ s x).value t y‖^2) := by
    change (∫ y : Configuration N, ∫ x : Configuration M,
      F s x*‖(swapBlocks ψ).value (joinLists s t) (joinLists x y)‖^2) = _
    rw [←integral_prod_symm _ (hF s t),integral_prod _ (hF s t)]
    simp only [coreSlice,swapBlocks_value,integral_const_mul]
  have hs (t : Spins N) : (∫ y : Configuration N, ∑ s : Spins M, ∫ x : Configuration M,
      F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2) =
      ∑ s : Spins M, ∫ y : Configuration N, ∫ x : Configuration M,
        F s x*‖(coreSlice (swapBlocks ψ) t y).value s x‖^2 :=
    integral_finsetSum _ (fun s _ => (hF s t).integral_prod_right)
  simp_rw [hs,he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have hi (t : Spins N) : Integrable (fun x : Configuration M =>
      F s x*(∫ y : Configuration N, ‖(coreSlice ψ s x).value t y‖^2)) := by
    have hh := (hF s t).integral_prod_left
    simpa only [swapBlocks_value,coreSlice,integral_const_mul] using hh
  rw [←integral_finsetSum _ (fun t _ => hi t)]
  simp only [formMass,Finset.mul_sum]

lemma retained_pressure_join_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun p : Configuration N × Configuration M =>
      retainedPressure b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedPressure_measurable_param b S Prod.fst hS measurable_fst
  apply hi.bdd_mul hm.aestronglyMeasurable
  exact Eventually.of_forall (fun p => by
    change ‖retainedPressure b (S p) p.1‖ ≤ b⁻¹^2*(N:ℝ)^(5/3:ℝ)
    rw [Real.norm_of_nonneg (retainedPressure_nonneg hb _ _)]
    exact (retainedPressure_le_average hb _ _).trans (physicalPressureAverage_le b p.1))

lemma retained_direct_join_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) {b : ℝ} (hb : 0 < b)
    (S : Configuration N × Configuration M → Finset (Fin N))
    (hS : ∀ i, MeasurableSet {p | i ∈ S p}) (s : Spins N) (t : Spins M) :
    Integrable (fun p : Configuration N × Configuration M =>
      retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
  have hi := integrable_join (N := N) (M := M) (hψ.1 (joinLists s t)).norm.integrable_sq
  have hm := retainedDirect_measurable_param b S Prod.fst hS measurable_fst
  apply ((pointRepulsion_join_integrable hψ s t).add
    (hi.const_mul (((2*Real.pi+1)/2)*(N:ℝ)/b))).mono'
    (hm.aestronglyMeasurable.mul hi.aestronglyMeasurable)
  have hn : ∀ᵐ p : Configuration N × Configuration M, Function.Injective p.1 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.ae ((configuration_ae_nonsingular N).mono (fun _ h => h.2))
  filter_upwards [hn] with p hp
  change ‖retainedDirect b (S p) p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2‖ ≤
    pointRepulsion p.1*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2+
      (((2*Real.pi+1)/2)*(N:ℝ)/b)*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2
  rw [Real.norm_of_nonneg (mul_nonneg (retainedDirect_nonneg hb _ _) (sq_nonneg _)),←add_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hh := retained_physical_coulomb_lower hb (S p) p.1 hp
  change retainedDirect b (S p) p.1-_ ≤ pointRepulsion p.1 at hh
  linarith

end CoulombAtom

end

end OAI
