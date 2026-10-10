import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalIndependentBoxes
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixBoundedRegions

namespace OAI

/-! # Independent physical rectangles with compact time bounds -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_shifted_root_rectangle_within
    {T B : Type*} [TopologicalSpace T] [TopologicalSpace B]
    {D : Set (T × B)} (hD : IsOpen D)
    {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (e : D → RootSlice a b k) (he : Topology.IsOpenEmbedding e)
    (τ : D → ℝ) (hτ : Continuous τ) (z : D) (t : ℝ)
    (V : Set B) (hV : IsOpen V) (hzV : z.val.2 ∈ V)
    (I : Set ℝ) (hI : IsOpen I) (htI : t ∈ I) :
    ∃ (Q : RootTransverseRectangle D) (A : RootBox hab k) (R : ℝ) (J : Set ℝ),
      IsOpen J ∧ z.val ∈ Q.first ×ˢ Q.second ∧ t ∈ J ∧
      Q.second ⊆ V ∧ J ⊆ I ∧
      A.transverse = Set.range (e ∘ Q.inclusion) ∧
      A.time ⊆ rootLeafWindow R 0 ∧
      ∀ w : Q.first × Q.second, (Homeomorph.addRight (τ (Q.inclusion w))) '' J ⊆ A.time := by
  let D' := D ∩ (univ ×ˢ V)
  have hD' : IsOpen D' := hD.inter (isOpen_univ.prod hV)
  let i : D' → D := Set.inclusion inter_subset_left
  have hi : Topology.IsOpenEmbedding i := Topology.IsOpenEmbedding.inclusion inter_subset_left
    (hD'.preimage continuous_subtype_val)
  let z' : D' := ⟨z.val,⟨z.prop,mem_univ _,hzV⟩⟩
  obtain ⟨Q',A,R,J,hJ,hz,ht,hcover,hbound,hw⟩ := exists_shifted_root_rectangle hD'
    hab (e ∘ i) (he.comp hi) (τ ∘ i) (hτ.comp hi.continuous) z' t
  let Q : RootTransverseRectangle D :=
    ⟨Q'.first,Q'.second,Q'.first_open,Q'.second_open,fun _ hx => (Q'.inside hx).1⟩
  refine ⟨Q,A,R,J ∩ I,hJ.inter hI,hz,⟨ht,htI⟩,?_,inter_subset_right,?_,hbound,?_⟩
  · intro w hw
    exact (Q'.inside (show (z.val.1,w) ∈ Q'.first ×ˢ Q'.second from ⟨hz.1,hw⟩)).2.2
  · exact hcover
  · intro w u hu
    obtain ⟨r,hr,rfl⟩ := hu
    exact hw w ⟨r,hr.1,rfl⟩

theorem exists_bounded_remainingRoot_physical_independent_box
    (d : ℕ) (q : InitialRootStep (d+1))
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    (z : C.factorPivotDomain q g k) (t : ℝ)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∃ Q : RootTransverseRectangle (C.factorPivotDomain q g k), ∃ hQ : Nonempty Q.second,
      letI := hQ
      haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
      ∃ (A : RootBox q.distinct k) (R : ℝ) (J : Set ℝ)
        (K : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (I : Set ℝ),
        IsOpen J ∧ z.val ∈ Q.first ×ˢ Q.second ∧ t ∈ J ∧
        IsCompact K ∧ Q.second ⊆ K ∧ IsCompact I ∧ J ⊆ I ∧
        A.time ⊆ rootLeafWindow R 0 ∧
        A.transverse = Set.range (C.rectangleSlice q g k Q) ∧
        (∀ w : Q.first × Q.second,
          (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) ∧
        let σ := shiftedRootFactorPullback q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
        haveI := shiftedRootFactorPullback_finite q.distinct A μ
          (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
          (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
        let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
        ∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd := by
  let E := q.nextGroupCoordinates
  let V := E ⁻¹' Metric.ball (E z.val.2) 1
  let K := E.symm '' Metric.closedBall (E z.val.2) 1
  have hV : IsOpen V := Metric.isOpen_ball.preimage E.continuous
  have hzV : z.val.2 ∈ V := by simp only [V,mem_preimage,Metric.mem_ball,dist_self]; norm_num
  have hK : IsCompact K := (isCompact_closedBall (E z.val.2) 1).image E.symm.continuous
  have hVK : V ⊆ K := by
    intro w hw
    exact ⟨E w,Metric.mem_closedBall.mpr (Metric.mem_ball.mp hw).le,E.symm_apply_apply w⟩
  obtain ⟨Q,A,R,J,hJ,hz,ht,hQV,hJI,hcover,hbound,hw⟩ :=
    exists_shifted_root_rectangle_within (C.factorPivotDomain_open q g k) q.distinct
      (C.factorSlice q g k) (C.factorSlice_isOpenEmbedding q g k)
      (C.factorTime q g k) (C.continuous_factorTime q g k) z t V hV hzV
      (Ioo (t-1) (t+1)) isOpen_Ioo (by constructor <;> linarith)
  let : Nonempty Q.second := ⟨⟨z.val.2,hz.2⟩⟩
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  refine ⟨Q,inferInstance,A,R,J,K,Icc (t-1) (t+1),hJ,hz,ht,hK,hQV.trans hVK,
    isCompact_Icc,hJI.trans Ioo_subset_Icc_self,hbound,hcover,hw,?_⟩
  let σ := shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  apply conditional_restrict_rectangle_product σ J hJ.measurableSet
  exact remainingRootBox_conditional_product d q C g k Q A R hbound
    (by rw [hcover]; exact subset_rfl) J hJ.measurableSet hw μ hA

end DukePrimeDegree

end

end OAI
