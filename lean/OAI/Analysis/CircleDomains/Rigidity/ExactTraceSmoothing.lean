import OAI.Analysis.CircleDomains.Rigidity.SamplingTraceContinuity
import OAI.Analysis.CircleDomains.Sobolev.RefinedShrinkingRectanglePartition

namespace OAI

/-! Smooth the original continuous Sobolev test on its open domain while
retaining every boundary value exactly. The derivative error can be prescribed. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem exists_exact_trace_smoothing
    (Ω : TopologicalSpace.Opens EuclideanPlane) (hne : (Ω : Set EuclideanPlane)ᶜ.Nonempty)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (hs : HasCompactSupport u)
    (hunit : ∀ x, u x ∈ Icc 0 1) (hw : DeGiorgi.MemW1pWitness 2 u Ω)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ v : EuclideanPlane → ℝ, Continuous v ∧ HasCompactSupport v ∧
      ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧ (∀ x, v x ∈ Icc 0 1) ∧
      EqOn v u (Ω : Set EuclideanPlane)ᶜ ∧
      ∀ i : Fin 2, MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1)) 2
        (volume.restrict Ω) ∧
        eLpNorm (fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)
          2 (volume.restrict Ω) < ε := by
  classical
  let N : Ω → Set EuclideanPlane := fun x => ball x.val (1 / 2)
  obtain ⟨ι, hι, ρ, center, a, b, c, d, _, hrect, hsub, hsmall, _⟩ :=
    exists_small_shrinking_partition_refining_neighborhoods Ω id continuousOn_id
      (Ω : Set EuclideanPlane)ᶜ Ω.isOpen.isClosed_compl hne
      (fun x hx hn => hn hx) N (fun _ => isOpen_ball) (fun x => mem_ball_self (by norm_num))
  let : Countable ι := hι
  let W : ι → Set EuclideanPlane := fun j =>
    euclideanPlaneCoordinates ⁻¹' (Ioo (a j) (b j) ×ˢ Ioo (c j) (d j))
  have hW (j : ι) : IsOpen (W j) :=
    (isOpen_Ioo.prod isOpen_Ioo).preimage euclideanPlaneCoordinates.continuous
  have hclosed (j : ι) : W j ⊆
      euclideanPlaneCoordinates ⁻¹' (Icc (a j) (b j) ×ˢ Icc (c j) (d j)) := by
    intro x hx
    exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩
  have hWU (j : ι) : W j ⊆ Ω := fun _ hx => (hrect j (hclosed j hx)).1
  let H (j : ι) := hw.restrict (hW j) (hWU j)
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ι
  obtain ⟨w, hws, hwu, hband, herr⟩ := exists_positive_partition_smoothing
    ρ W hW hsub u H (fun _ x _ => hunit x) δ hδ
  let v := boundaryPaste Ω u w
  have hvc : Continuous v := boundaryPaste_continuous ρ W hu hws.continuousOn
    (by
      intro x hx j hj y hy
      exact hsmall j x (hclosed j (hsub j (subset_tsupport _ hj))) y (hclosed j hy)) hband
  have hvon : EqOn v w Ω := by
    intro x hx
    simp only [v, boundaryPaste, ite_eq_left hx]
  have hvoff : EqOn v u (Ω : Set EuclideanPlane)ᶜ := by
    intro x hx
    simp only [v, boundaryPaste, ite_eq_right hx]
  have hvd : ContDiffOn ℝ (⊤ : ℕ∞) v Ω := hws.congr hvon
  have hvgrad (x : EuclideanPlane) (hx : x ∈ Ω) : fderiv ℝ v x = fderiv ℝ w x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact hvon hy
  have hvs : HasCompactSupport v := by
    apply HasCompactSupport.intro' (K := cthickening 1 (tsupport u)) (hs.isCompact.cthickening)
      isClosed_cthickening
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · rw [hvon hxΩ]
      have hrange : w x ∈ Icc 0 0 := by
        apply hband x hxΩ
        intro j hj y hy
        have hxj := hclosed j (hsub j (subset_tsupport _ hj))
        have hyj := hclosed j hy
        have hxy : dist x y ≤ 1 := by
          have hxC : dist x (center j).val < 1 / 2 := (hrect j hxj).2
          have hyC : dist y (center j).val < 1 / 2 := (hrect j hyj).2
          calc
            dist x y ≤ dist x (center j).val + dist (center j).val y := dist_triangle _ _ _
            _ ≤ 1 := by rw [dist_comm (center j).val y]; linarith
        have huy : u y = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hyu
          exact hx (mem_cthickening_of_dist_le x y 1 (tsupport u) hyu hxy)
        simp only [huy, mem_Icc, le_refl, and_self]
      exact le_antisymm hrange.2 hrange.1
    · rw [hvoff hxΩ]
      apply image_eq_zero_of_notMem_tsupport
      intro hxu
      exact hx (self_subset_cthickening (δ := 1) (tsupport u) hxu)
  refine ⟨v, hvc, hvs, hvd, ?_, hvoff, ?_⟩
  · intro x
    by_cases hx : x ∈ Ω
    · rw [hvon hx]
      exact hwu x hx
    · rw [hvoff hx]
      exact hunit x
  · intro i
    have hsumG (x : EuclideanPlane) (hx : x ∈ Ω) :
        (∑ᶠ j, ρ.weight j x * (H j).weakGrad x i) = hw.weakGrad x i := by
      change (∑ᶠ j, ρ.weight j x * hw.weakGrad x i) = _
      rw [← finsum_mul, ρ.sum_one ⟨x, hx⟩, one_mul]
    have he : eLpNorm (fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 (volume.restrict Ω) < ε := by
      apply lt_of_le_of_lt _ hsum
      convert herr i using 1
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
      rw [hvgrad x hx, hsumG x hx]
    have hE : MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1) - hw.weakGrad x i)
        2 (volume.restrict Ω) := he.trans_le (le_top)
    have hL := hE.add (hw.weakGrad_component_memLp i)
    refine ⟨?_, he⟩
    convert hL using 1
    funext x
    exact (sub_add_cancel _ _).symm

end CircleDomainRigidity

end

end OAI
