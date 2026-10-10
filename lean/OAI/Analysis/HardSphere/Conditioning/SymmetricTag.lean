import Mathlib
import OAI.Analysis.HardSphere.Comparison.IntegratedFiber
import OAI.Analysis.HardSphere.Conditioning.BathPhase
import OAI.Analysis.HardSphere.Allocation.TaggedReference

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
local instance permSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
local instance permSingleton (n : ℕ) : MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ ↦ trivial⟩

def tagOrderPerm (i : Fin (n+1)) (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' 0).trans ((Equiv.optionCongr τ).trans (finSuccEquiv' i).symm)
@[simp] lemma tagOrderPerm_zero (i : Fin (n+1)) (τ : Equiv.Perm (Fin n)) :
    tagOrderPerm i τ 0=i := by simp [tagOrderPerm]
@[simp] lemma tagOrderPerm_succ (i : Fin (n+1)) (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    tagOrderPerm i τ j.succ=i.succAbove (τ j) := by
  change (finSuccEquiv' i).symm ((Equiv.optionCongr τ) ((finSuccEquiv' 0) j.succ))=_
  have hh : (finSuccEquiv' (0:Fin (n+1))) j.succ=some j := by
    simpa only [Fin.succAbove_zero] using finSuccEquiv'_succAbove (0:Fin (n+1)) j
  simp [hh]

def splitFirst (x : Fin (n+1)→E) : E×(Fin n→E) := (x 0,fun j ↦ x j.succ)
lemma splitFirst_measurable : Measurable (splitFirst (E:=E) (n:=n)) := by
  unfold splitFirst
  fun_prop

def orderedObservation (i : Fin (n+1)) (p : (Fin (n+1)→E)×Equiv.Perm (Fin n)) : E×(Fin n→E) :=
  (p.1 i,fun j ↦ p.1 (i.succAbove (p.2 j)))
lemma orderedObservation_measurable (i : Fin (n+1)) : Measurable (orderedObservation (E:=E) i) := by
  unfold orderedObservation
  have he (j : Fin n) : Measurable (fun p : (Fin (n+1)→E)×Equiv.Perm (Fin n) ↦ p.1 (i.succAbove (p.2 j))) := by
    exact measurable_from_prod_countable_left (fun τ ↦ show Measurable (fun x : Fin (n+1)→E ↦ x (i.succAbove (τ j))) from measurable_pi_apply _)
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk (Measurable.of_eval he)

omit [MeasurableSpace E] in
lemma orderedObservation_eq (i : Fin (n+1)) (x : Fin (n+1)→E) (τ : Equiv.Perm (Fin n)) :
    orderedObservation i (x,τ)=splitFirst (fun j ↦ x (tagOrderPerm i τ j)) := by
  simp [orderedObservation,splitFirst]

lemma ordered_symmetric_law (μ : Measure (Fin (n+1)→E)) [SFinite μ]
    (hμ : ∀σ : Equiv.Perm (Fin (n+1)),MeasurePreserving (fun x j ↦ x (σ j)) μ μ)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    (μ.prod β).map (orderedObservation i)=μ.map splitFirst := by
  ext s hs
  rw [Measure.map_apply (orderedObservation_measurable i) hs,Measure.map_apply splitFirst_measurable hs]
  rw [Measure.prod_apply_symm ((orderedObservation_measurable i) hs)]
  have hh (τ : Equiv.Perm (Fin n)) : μ ((fun x : Fin (n+1)→E ↦ (x,τ)) ⁻¹' (orderedObservation i ⁻¹' s))=μ (splitFirst ⁻¹' s) := by
    have he : ((fun x : Fin (n+1)→E ↦ (x,τ)) ⁻¹' (orderedObservation i ⁻¹' s))=
        (fun x j ↦ x (tagOrderPerm i τ j)) ⁻¹' (splitFirst ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage,orderedObservation_eq]
    rw [he]
    exact (hμ (tagOrderPerm i τ)).measure_preimage ((splitFirst_measurable hs).nullMeasurableSet)
  simp_rw [hh]
  simp

lemma ground_ordered_law {L : Length} (u : Jet (n+1) L) (hb : bosonic u.1) (hu : ‖u.1‖=1)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    ((groundPositionLaw (n+1) L u).prod β).map (orderedObservation i)=
      (groundPositionLaw (n+1) L u).map splitFirst := by
  let := groundPositionLaw_probability u hu
  apply ordered_symmetric_law
  intro σ
  exact groundPositionLaw_permute u hb σ
lemma ground_first_density {L : Length} (u : Jet (n+1) L) :
    (groundPositionLaw (n+1) L u).map splitFirst=
      ((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)) := by
  let c : Torus L×Configuration n L → Configuration (n+1) L := fun p ↦ Fin.cons p.1 p.2
  have hc : Measurable c := by unfold c; fun_prop
  have hcP : MeasurePreserving c ((volume : Measure (Torus L)).prod volume) volume :=
    (cons_preserving L).comp Measure.measurePreserving_swap
  let g : Configuration (n+1) L→ℝ≥0∞ := fun X ↦ ENNReal.ofReal (‖u.1 X‖^2)
  have hg : Measurable g := ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
  have he := map_density_comp ((volume : Measure (Torus L)).prod volume) c hc g hg
  rw [hcP.map_eq] at he
  change _=groundPositionLaw (n+1) L u at he
  rw [←he,Measure.map_map splitFirst_measurable hc]
  have hid : splitFirst ∘ c=id := by
    funext p
    simp [c,splitFirst]
  rw [hid,Measure.map_id]
  rfl

def orderedKernel (β : Measure (Equiv.Perm (Fin n))) (i : Fin (n+1)) :
    Kernel (Fin (n+1)→E) (E×(Fin n→E)) :=
  (Kernel.id ×ₖ Kernel.const _ β).map (orderedObservation i)
instance orderedKernel_markov (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β]
    (i : Fin (n+1)) : IsMarkovKernel (orderedKernel (E:=E) β i) :=
  Kernel.IsMarkovKernel.map _ (orderedObservation_measurable i)
lemma orderedKernel_comp (μ : Measure (Fin (n+1)→E)) [SFinite μ]
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    orderedKernel β i ∘ₘ μ=(μ.prod β).map (orderedObservation i) := by
  unfold orderedKernel
  rw [←Measure.map_comp _ _ (orderedObservation_measurable i),←Measure.compProd_eq_comp_prod,
    Measure.compProd_const]

lemma ground_ordered_bind {L : Length} (u : Jet (n+1) L) (hb : bosonic u.1) (hu : ‖u.1‖=1)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    orderedKernel β i ∘ₘ groundPositionLaw (n+1) L u=
      ((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)) := by
  let := groundPositionLaw_probability u hu
  rw [orderedKernel_comp,ground_ordered_law u hb hu,ground_first_density]

lemma all_tags_reference {L : Length} {Y : Type*} [MeasurableSpace Y]
    (u : Jet (n+1) L) (hb : bosonic u.1) (hu : ‖u.1‖=1)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β]
    (post : Kernel (Torus L×Configuration n L) Y) :
    (∑i : Fin (n+1),(post ∘ₖ orderedKernel β i) ∘ₘ groundPositionLaw (n+1) L u)=
      (n+1) • (post ∘ₘ (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)))) := by
  simp_rw [←Measure.comp_assoc,ground_ordered_bind u hb hu β]
  simp

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
attribute [local instance] HardSphere.Comparison.permSpace HardSphere.Comparison.permSingleton
namespace HardSphere.Comparison
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma comp_comap_map (μ : Measure A) (f : A→B) (hf : Measurable f) (κ : Kernel B C) :
    κ.comap f hf ∘ₘ μ=κ ∘ₘ μ.map f := by
  rw [←Kernel.comp_deterministic_eq_comap,←Measure.comp_assoc,Measure.deterministic_comp_eq_map]

lemma allocation_slice_law {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) (T : ℝ) (hT : 0≤T) (q : Wiener.Time)
    {Z : Type*} [MeasurableSpace Z]
    (κ : Kernel (ConfigurationPath N L) Z) [IsMarkovKernel κ] :
    ((groundPathLaw N L a T u) ⊗ₘ κ).map
      (fun p : ConfigurationPath N L×Z ↦ p.1 q)=groundPositionLaw N L u := by
  let := hu.groundPathLaw_probability hT
  have he : (fun p : ConfigurationPath N L×Z ↦ p.1 q)=
      (fun ω : ConfigurationPath N L ↦ ω q) ∘ Prod.fst := rfl
  rw [he,←Measure.map_map (continuous_eval_const q).measurable measurable_fst]
  change ((groundPathLaw N L a T u ⊗ₘ κ).fst).map _=_
  rw [Measure.fst_compProd]
  exact (hu.groundPathLaw_marginal T hT q).map_eq

end HardSphere.Comparison

namespace HardSphere.Groups
open Sampling Wiener PathCutoff Comparison

lemma physical_group_tag_reference {n K M G : ℕ} {L : Length} {a : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L a u)
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ T : ℝ)
    (hT : 0≤T) (q : Time)
    {Y : Type*} [MeasurableSpace Y]
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β]
    (post : Kernel (Torus L×Configuration n L) Y) :
    let Q := groundPathLaw (n+1) L a T u ⊗ₘ
      physicalAllocationKernel (N:=n+1) (K:=K) m (M*G) r R C S s₀ q
    let read := fun i : Fin (n+1) ↦ (post ∘ₖ orderedKernel β i).comap
      (fun p : ConfigurationPath (n+1) L×((Fin 3→Fin K)→Allocation (M*G) (Fin (n+1))) ↦ p.1 q)
      ((continuous_eval_const q).measurable.comp measurable_fst)
    (∑g : Fin G,allocatedTagLaw Q (allocatedPhysicalGroup m r R C S s₀ q) read g)≤
      (n+1) • (post ∘ₘ (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)))) := by
  dsimp only
  refine (allocatedPhysicalTag_sum_le hL hK m r R C S s₀ q _ _).trans ?_
  simp_rw [comp_comap_map,allocation_slice_law hu T hT q]
  exact le_of_eq (all_tags_reference u hu.2.1 hu.2.2.1 β post)

end HardSphere.Groups

end
end

end

end OAI
