import Mathlib
import OAI.Analysis.HardSphere.Conditioning.SymmetricTag

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma restrict_kernel_comp (κ : Kernel X Y) (μ : Measure X) {s : Set Y}
    (hs : MeasurableSet s) : κ.restrict hs ∘ₘ μ=(κ ∘ₘ μ).restrict s := by
  ext t ht
  rw [Measure.bind_apply ht (κ.restrict hs).aemeasurable,
    Measure.restrict_apply ht,Measure.bind_apply (ht.inter hs) κ.aemeasurable]
  congr 1
  funext x
  exact Kernel.restrict_apply' κ hs x ht

def cellExtraKernel (ν : Measure X) (A B : Set X) (hA : MeasurableSet A) :
    Kernel (X×Y) ((X×Y)×X) :=
  (Kernel.id ×ₖ Kernel.const _ (ν.restrict B)).restrict
    (hA.preimage (measurable_fst.comp measurable_fst))

lemma cellExtraKernel_comp (μ : Measure (X×Y)) [SFinite μ]
    (ν : Measure X) [SFinite ν] (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    cellExtraKernel (Y:=Y) ν A B hA ∘ₘ μ=
      (μ.prod ν).restrict {p | p.1.1∈A ∧ p.2∈B} := by
  rw [cellExtraKernel,restrict_kernel_comp,←Measure.compProd_eq_comp_prod,
    Measure.compProd_const]
  have hp : μ.prod (ν.restrict B)=(μ.prod ν).restrict (univ×ˢB) := by
    simpa only [Measure.restrict_univ] using Measure.prod_restrict (μ:=μ) (ν:=ν) univ B
  rw [hp,Measure.restrict_restrict' (MeasurableSet.univ.prod hB)]
  congr 1
  ext p
  simp

lemma cellExtraKernel_density (μ : Measure (X×Y)) [SFinite μ]
    (ν : Measure X) [SFinite ν] (g : X×Y→ℝ≥0∞) (hg : Measurable g)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cellExtraKernel (Y:=Y) ν A B hA ∘ₘ μ.withDensity g=
      ((μ.prod ν).withDensity (fun p ↦ g p.1)).restrict {p | p.1.1∈A ∧ p.2∈B} := by
  rw [cellExtraKernel_comp _ ν A B hA hB,prod_withDensity_left hg]

end HardSphere.Comparison

namespace HardSphere.Groups
open Sampling Wiener PathCutoff Comparison
attribute [local instance] HardSphere.Comparison.permSpace HardSphere.Comparison.permSingleton

lemma physical_group_cell_reference {n K M G : ℕ} {L : Length} {a : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L a u)
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ T : ℝ)
    (hT : 0≤T) (q : Time)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β]
    (A B : Set (Torus L)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    let Q := groundPathLaw (n+1) L a T u ⊗ₘ
      physicalAllocationKernel (N:=n+1) (K:=K) m (M*G) r R C S s₀ q
    let read := fun i : Fin (n+1) ↦ ((cellExtraKernel volume A B hA) ∘ₖ orderedKernel β i).comap
      (fun p : ConfigurationPath (n+1) L×((Fin 3→Fin K)→Allocation (M*G) (Fin (n+1))) ↦ p.1 q)
      ((continuous_eval_const q).measurable.comp measurable_fst)
    (∑g : Fin G,allocatedTagLaw Q (allocatedPhysicalGroup m r R C S s₀ q) read g)≤
      (n+1) • (((((volume : Measure (Torus L)).prod (volume : Measure (Configuration n L))).prod volume).withDensity
        (fun p : (Torus L×Configuration n L)×Torus L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1.1 p.1.2)‖^2))).restrict
          {p | p.1.1∈A ∧ p.2∈B}) := by
  have hc : Measurable (fun p : Torus L×Configuration n L ↦ (Fin.cons p.1 p.2 : Configuration (n+1) L)) := by fun_prop
  have hg : Measurable (fun p : Torus L×Configuration n L ↦
      ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)) :=
    (((Lp.stronglyMeasurable u.1).measurable.comp hc).norm.pow_const 2).ennreal_ofReal
  have h := physical_group_tag_reference (M:=M) (G:=G) hu hL hK m r R C S s₀ T hT q β
    (cellExtraKernel volume A B hA)
  dsimp only at h ⊢
  rw [cellExtraKernel_density _ _ _ hg A B hA hB] at h
  exact h

end HardSphere.Groups

end
end

end

end OAI
