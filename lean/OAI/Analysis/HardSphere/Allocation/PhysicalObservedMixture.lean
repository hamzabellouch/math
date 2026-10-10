import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalMixedObservation

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def physicalObservedMixture {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (b : Bool) : Kernel (PhysicalDatum (N+1) K M G L) (Torus L×Torus L×(Fin N→Torus L)) :=
  ((physicalMixedRoutes hL g m t r R C S u particle hxy ν) ⊗ₖ
    physicalCodeObserver particle hxy b).snd
instance physicalObservedMixture_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (b : Bool) : IsFiniteKernel (physicalObservedMixture hL g m t r R C S u particle hxy ν b) := by
  unfold physicalObservedMixture; infer_instance

theorem physicalObservedMixture_same {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin (N+1)) (d : PhysicalDatum (N+1) K M G L) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (ha : ∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) :
    physicalObservedMixture hL g m t r R C S u particle hxy ν true d =
    physicalObservedMixture hL g m t r R C S u particle hxy ν false d := by
  ext A hA
  simp only [physicalObservedMixture,Kernel.snd_apply' _ _ hA,Kernel.compProd_apply (measurable_snd hA)]
  have hex (b : Bool) :
      (∫⁻w,(physicalCodeObserver particle hxy b) (d,w) A ∂physicalMixedRoutes hL g m t r R C S u particle hxy ν d)=
      ∫⁻c,∫⁻w,(physicalCodeObserver particle hxy b) (d,(c,w)) A
        ∂physicalCodedRoute hL g m t r R C S u particle hxy c d
        ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d := by
    rw [physicalMixedRoutes,Kernel.lintegral_compProd]
    rfl
    exact (physicalCodeObserver particle hxy b).measurable_coe hA |>.comp measurable_prodMk_left
  change (∫⁻w,(physicalCodeObserver particle hxy true) (d,w) A ∂physicalMixedRoutes hL g m t r R C S u particle hxy ν d)=
    (∫⁻w,(physicalCodeObserver particle hxy false) (d,w) A ∂physicalMixedRoutes hL g m t r R C S u particle hxy ν d)
  rw [hex true,hex false]
  apply lintegral_congr_ae
  rw [Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [ha] with p hp
  filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
  have H := congrArg (fun μ ↦ μ A) (physicalCodedRoute_same_observed hL g m t r R C S ht u particle d hxy p z hz hp)
  simpa only [Measure.bind_apply hA (Kernel.aemeasurable _),Kernel.comap_apply] using H

theorem physicalObservedMixture_same_joint {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum (N+1) K M G L))
    (ha : ∀ᵐd ∂μ.restrict E,∀ᵐp ∂ν d,∀i : Fin p.val.length,
      (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) :
    (μ.restrict E).compProd (physicalObservedMixture hL g m t r R C S u particle hxy ν true)=
    (μ.restrict E).compProd (physicalObservedMixture hL g m t r R C S u particle hxy ν false) := by
  apply Measure.compProd_congr
  filter_upwards [ha] with d hd
  exact physicalObservedMixture_same hL g m t r R C S ht u particle d hxy ν hd

end HardSphere.Groups
end
end

end OAI
