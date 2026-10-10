import OAI.NumberTheory.DukePrimeDegree.Geometry.NextProductChain

namespace OAI

/-! # Local finiteness of the intrinsic product on the next subgroup -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace InitialRootStep

theorem ae_nextIntrinsicProduct_locallyFinite (d : ℕ) (q : InitialRootStep (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ x ∂μ, IsLocallyFiniteMeasure (q.nextIntrinsicProduct d μ x) := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have H (p : q.NextRoot) := ae_intrinsicRootLeaf_spec
    (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ
    ((ae_root_stabilizer_trivial d μ hA).mono fun _ hx => hx _ _ _)
  filter_upwards [ae_all_iff.mpr H] with x hx
  let ν := Measure.pi fun p : q.NextRoot =>
    intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x
  let : ∀ p : q.NextRoot, IsLocallyFiniteMeasure
      (intrinsicRootLeaf (ne_of_lt (q.remaining_positive p.val (Finset.mem_erase.mp p.prop).2)) μ x) :=
    fun p => (hx p).1
  let F := q.nextGroupCoordinates.symm
  change IsLocallyFiniteMeasure (ν.map F)
  constructor
  intro u
  obtain ⟨V,hu,hV,hfin⟩ := Measure.exists_isOpen_measure_lt_top ν (F.symm u)
  refine ⟨F '' V,(F.isOpenMap _ hV).mem_nhds ⟨F.symm u,hu,F.apply_symm_apply u⟩,?_⟩
  rw [Measure.map_apply F.measurable (F.isOpenMap _ hV).measurableSet,F.injective.preimage_image]
  exact hfin

end InitialRootStep
end DukePrimeDegree

end

end OAI
