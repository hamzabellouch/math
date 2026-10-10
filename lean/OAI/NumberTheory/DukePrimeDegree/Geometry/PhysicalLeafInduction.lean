import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalWindowIntrinsic
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixWindowProportionality
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProductMass

namespace OAI

/-! # The actual remaining-group leaf-product induction step -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {d : ℕ} {q : InitialRootStep (d+1)} {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) q.processed T} {g : G (d+1)}
    {D D' : Finset (Fin (d+1))} {c : EliminationChain q.processed D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}

theorem ae_basedLeaf_eq_intrinsic_of_next
    (A : RootPrefixBox C c q.initial hf g) (R : ℝ)
    (hAR : A.time ⊆ c.remainingWindow R 0)
    (c' : EliminationChain (insert q.root q.processed) D')
    (hf' : c'.finalEntries = allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (hIH : ∀ m, ∀ B ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
        c' q.next_initial hf' g 1 m,
      ∀ᵐ z ∂B.coordinateMeasure μ,
        c'.remainingGroupLeafMeasure q.next_initial hf' (B.basedLeaf (1+m) μ z) =
          c'.remainingIntrinsicProduct q.next_initial hf' μ
            ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c' q.next_initial hf' g z)) :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      c.remainingGroupLeafMeasure q.initial hf (A.basedLeaf R μ z) =
        c.remainingIntrinsicProduct q.initial hf μ (C.timeParam c q.initial hf g z) := by
  let F := C.physicalWindowFamily q g c hf R
  have H : ∀ᵐ z ∂A.coordinateMeasure μ, ∀ m, ∀ B ∈ F m,
      z.1 ∈ B.rectangle.first → ∃ a : ℝ≥0∞,
        (c.remainingGroupLeafMeasure q.initial hf (A.basedLeaf R μ z)).restrict
          (c.remainingGroupCenter q.initial hf z.2 '' (B.toBox c hf).time) =
        a • (c.remainingIntrinsicProduct q.initial hf μ (C.timeParam c q.initial hf g z)).restrict
          (c.remainingGroupCenter q.initial hf z.2 '' (B.toBox c hf).time) := by
    apply ae_all_iff.mpr
    intro m
    apply (ae_ball_iff (C.physicalWindowFamily_countable q g c hf R m)).mpr
    intro B hB
    have hAD : A.time ⊆ (B.toBox c hf).time :=
      hAR.trans ((c.remainingWindow_mono R (Nat.zero_le m)).trans
        (C.physicalWindowFamily_time q g c hf R m B hB))
    apply A.ae_basedGroup_proportional_window R hAR (B.toBox c hf) hAD μ hfree
      (c.remainingIntrinsicProduct q.initial hf μ)
    simpa only [c.remainingGroupCenter_image] using
      B.centeredConditional_intrinsic c hf c' hf' μ hfree hIH
  filter_upwards [H,A.ae_basedLeaf_spec R hAR μ hfree,
    A.ae_coordinate_of_ambient μ (c.ae_remainingIntrinsicProduct_unit d q.initial hf μ),
    A.ae_coordinate_of_ambient μ hfree] with z hz hν hη hfz
  let W := c.remainingWordHomeomorph q.initial hf
  let G := c.remainingGroupCenter q.initial hf z.2
  let ν := c.remainingGroupLeafMeasure q.initial hf (A.basedLeaf R μ z)
  let η := c.remainingIntrinsicProduct q.initial hf μ (C.timeParam c q.initial hf g z)
  have hνU : ν (W '' c.cube 1) = 1 := by
    rw [c.remainingGroupLeafMeasure_apply q.initial hf _ (c.cube_open 1).measurableSet]
    exact hν.2
  have hbfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) v =
        Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2) → v = 1 := by
    apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots (d+1)))
      (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) (c.word z.2)
      (positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hf z.2))
    simpa only [C.timeParam_eq_action] using hfz
  have hcover : ⋃ m : ℕ, W '' c.remainingWindow 1 m = univ := by
    rw [←image_iUnion,c.remainingWindow_cover,image_univ]
    exact W.surjective.range_eq
  apply eq_of_exhausting_proportional_windows ν η (W '' c.cube 1)
    (W.isOpenMap _ (c.cube_open 1)).measurableSet hνU hη
    (fun m => W '' c.remainingWindow 1 m)
    (fun m => (W.isOpenMap _ (c.remainingWindow_open 1 m)).measurableSet)
    (fun i j hij => image_mono (c.remainingWindow_mono 1 hij)) hcover
  intro m
  let K := G.symm '' (W '' c.closedCube (1+m))
  have hK : IsCompact K := ((c.closedCube_compact (1+m)).image W.continuous).image G.symm.continuous
  obtain ⟨r,hr⟩ := c.compact_subset_remainingWindow K hK R
  obtain ⟨B,hB,hsB⟩ := C.physicalWindowFamily_covers q g c hf R r z.1 hbfree
  have hbig : W '' c.closedCube (1+m) ⊆ G '' (B.toBox c hf).time := by
    intro w hw
    refine ⟨G.symm w,?_,G.apply_symm_apply w⟩
    apply C.physicalWindowFamily_time q g c hf R r B hB
    exact hr ⟨w,hw,rfl⟩
  obtain ⟨a,ha⟩ := hz r B hB hsB
  refine ⟨G '' (B.toBox c hf).time,a,?_,?_,ha⟩
  · apply Subset.trans (image_mono (c.cube_mono
      (show (1:ℝ) ≤ 1+(m:ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg m))))
    exact (image_mono (c.cube_subset_closedCube (1+m))).trans hbig
  · exact (image_mono (c.cube_subset_closedCube (1+m))).trans hbig

end RootPrefixBox
end DukePrimeDegree

end

end OAI
