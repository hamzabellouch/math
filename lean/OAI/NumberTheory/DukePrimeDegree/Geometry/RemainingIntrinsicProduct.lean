import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingEuclideanCoordinates
import OAI.NumberTheory.PrimePackets.AmbientLeaves

namespace OAI

/-! # The intrinsic root product on each remaining subgroup

Its coordinates are actual matrix entries, so the measure is independent
of the Gaussian elimination chain used to define the coordinate chart.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D E : Finset (Fin n)}

def remainingIntrinsicProduct (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)) :=
  (Measure.pi fun p : ↥(allPositiveRoots n \ P) =>
    intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x).map
      (c.remainingGroupCoordinates hP hfinal).symm

lemma remainingGroupCoordinates_eq (c : EliminationChain P D) (e : EliminationChain P E)
    (hP : InitialRootPattern P) (hc : c.finalEntries = allPositiveRoots n)
    (he : e.finalEntries = allPositiveRoots n) :
    c.remainingGroupCoordinates hP hc = e.remainingGroupCoordinates hP he := by
  apply Homeomorph.ext
  intro g
  funext p
  rw [c.remainingGroupCoordinates_apply,e.remainingGroupCoordinates_apply]

lemma remainingIntrinsicProduct_chain_independent (c : EliminationChain P D)
    (e : EliminationChain P E) (hP : InitialRootPattern P)
    (hc : c.finalEntries = allPositiveRoots n) (he : e.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    c.remainingIntrinsicProduct hP hc μ x = e.remainingIntrinsicProduct hP he μ x := by
  unfold remainingIntrinsicProduct
  rw [c.remainingGroupCoordinates_eq e hP hc he]

lemma remainingIntrinsicProduct_done (c : EliminationChain (allPositiveRoots n) D)
    (hP : InitialRootPattern (allPositiveRoots n)) (hc : c.finalEntries = allPositiveRoots n)
    (μ : Measure (X n)) [IsFiniteMeasure μ] (x : X n) :
    c.remainingIntrinsicProduct hP hc μ x = Measure.dirac 1 := by
  let : IsEmpty ↥(allPositiveRoots n \ allPositiveRoots n) :=
    ⟨fun p => by simpa only [Finset.sdiff_self,Finset.notMem_empty] using p.prop⟩
  unfold remainingIntrinsicProduct
  rw [Measure.pi_of_empty _ (c.remainingGroupCoordinates hP hc 1),
    Measure.map_dirac' (c.remainingGroupCoordinates hP hc).symm.measurable,
    Homeomorph.symm_apply_apply]

theorem ae_remainingIntrinsicProduct_locallyFinite (d : ℕ)
    {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, IsLocallyFiniteMeasure (c.remainingIntrinsicProduct hP hfinal μ x) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H (p : ↥(allPositiveRoots (d+1) \ P)) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  filter_upwards [ae_all_iff.mpr H] with x hx
  let ν := Measure.pi fun p : ↥(allPositiveRoots (d+1) \ P) =>
    intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x
  let : ∀ p : ↥(allPositiveRoots (d+1) \ P), IsLocallyFiniteMeasure
      (intrinsicRootLeaf (ne_of_lt (Finset.mem_filter.mp (Finset.mem_sdiff.mp p.prop).1).2) μ x) :=
    fun p => (hx p).1
  let F := (c.remainingGroupCoordinates hP hfinal).symm
  change IsLocallyFiniteMeasure (ν.map F)
  constructor
  intro u
  obtain ⟨V,hu,hV,hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (F.symm u)
  refine ⟨F '' V,(F.isOpenMap _ hV).mem_nhds ⟨F.symm u,hu,F.apply_symm_apply u⟩,?_⟩
  rw [Measure.map_apply F.measurable (F.isOpenMap _ hV).measurableSet,F.injective.preimage_image]
  exact hfin

end EliminationChain
end DukePrimeDegree

end

end OAI
