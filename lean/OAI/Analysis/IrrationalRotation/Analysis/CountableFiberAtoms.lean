import Mathlib

namespace OAI

open Set Filter MeasureTheory

namespace InvariantProjection.CountableFiberAtoms

variable {X Y : Type*} [MeasurableSpace X]
variable {μ : Measure X} {f : X → Y} {C : Set Y}

theorem ae_fiber_measure_ne_zero (hC : C.Countable)
    (hf : ∀ᵐ x ∂μ, f x ∈ C) :
    ∀ᵐ x ∂μ, μ (f ⁻¹' {f x}) ≠ 0 := by
  have havoid : ∀ᵐ x ∂μ, ∀ y ∈ C, μ (f ⁻¹' {y}) = 0 → f x ≠ y := by
    apply (ae_ball_iff hC).2
    intro y hy
    by_cases hz : μ (f ⁻¹' {y}) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with x hx
      intro _
      simpa using hx
    · exact Filter.Eventually.of_forall (fun _ h => (hz h).elim)
  filter_upwards [hf, havoid] with x hx havoid
  intro hz
  exact havoid (f x) hx hz rfl

theorem ae_mem_positive_fiber_union (hC : C.Countable)
    (hf : ∀ᵐ x ∂μ, f x ∈ C) :
    ∀ᵐ x ∂μ, x ∈ ⋃ y ∈ {y ∈ C | μ (f ⁻¹' {y}) ≠ 0}, f ⁻¹' {y} := by
  filter_upwards [hf, ae_fiber_measure_ne_zero hC hf] with x hx hpos
  exact Set.mem_iUnion.2 ⟨f x, Set.mem_iUnion.2 ⟨⟨hx, hpos⟩, rfl⟩⟩

omit [MeasurableSpace X] in

theorem pairwise_disjoint_fibers (f : X → Y) :
    Pairwise (fun y z => Disjoint (f ⁻¹' {y}) (f ⁻¹' {z})) := by
  intro y z hyz
  rw [Set.disjoint_left]
  intro x hxy hxz
  exact hyz (hxy.symm.trans hxz)

theorem exists_nontrivial_fiber [IsProbabilityMeasure μ]
    (hC : C.Countable) (hf : ∀ᵐ x ∂μ, f x ∈ C)
    (hnonconstant : ¬ ∃ y : Y, f =ᵐ[μ] fun _ => y) :
    ∃ y ∈ C, μ (f ⁻¹' {y}) ≠ 0 ∧ μ (f ⁻¹' {y})ᶜ ≠ 0 := by
  obtain ⟨x, hxC, hx⟩ := (hf.and (ae_fiber_measure_ne_zero hC hf)).exists
  refine ⟨f x, hxC, hx, ?_⟩
  intro hnull
  apply hnonconstant
  refine ⟨f x, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz
  simpa only [Set.mem_compl_iff, not_not, Set.mem_preimage,
    Set.mem_singleton_iff] using hz


variable [mY : MeasurableSpace Y] [MeasurableSingletonClass Y]

omit [MeasurableSpace X] in

theorem measurableAtom_comap (f : X → Y) (x : X) :
    @measurableAtom X (mY.comap f) x = f ⁻¹' {f x} := by
  apply Set.Subset.antisymm
  · exact @measurableAtom_subset X (mY.comap f) (f ⁻¹' {f x}) x
      ⟨{f x}, measurableSet_singleton _, rfl⟩ rfl
  · intro z hz
    simp only [measurableAtom, Set.mem_iInter]
    intro s hx hs
    obtain ⟨t, ht, rfl⟩ := hs
    change f z ∈ t
    change f x ∈ t at hx
    change f z = f x at hz
    simpa [hz] using hx

omit [MeasurableSpace X] [MeasurableSingletonClass Y] in

theorem fiber_subset_or_disjoint {s : Set X}
    (hs : MeasurableSet[mY.comap f] s) (y : Y) :
    f ⁻¹' {y} ⊆ s ∨ Disjoint (f ⁻¹' {y}) s := by
  obtain ⟨t, ht, rfl⟩ := hs
  by_cases hy : y ∈ t
  · left
    intro x hx
    change f x ∈ t
    change f x = y at hx
    simpa [hx] using hy
  · right
    rw [Set.disjoint_left]
    intro x hx hxt
    change f x = y at hx
    exact hy (hx ▸ hxt)

omit [MeasurableSingletonClass Y] in

theorem exists_positive_fiber_subset (hC : C.Countable)
    (hf : ∀ᵐ x ∂μ, f x ∈ C) {s : Set X}
    (hs : MeasurableSet[mY.comap f] s) (hμs : μ s ≠ 0) :
    ∃ y ∈ C, μ (f ⁻¹' {y}) ≠ 0 ∧ f ⁻¹' {y} ⊆ s := by
  have hfreq : ∃ᵐ x ∂μ, x ∈ s := frequently_ae_mem_iff.2 hμs
  obtain ⟨x, hxs, hxC, hxpos⟩ :=
    (hfreq.and_eventually (hf.and (ae_fiber_measure_ne_zero hC hf))).exists
  refine ⟨f x, hxC, hxpos, ?_⟩
  rcases fiber_subset_or_disjoint hs (f x) with hsub | hdisj
  · exact hsub
  · exact (Set.disjoint_left.1 hdisj rfl hxs).elim

theorem ae_measurableAtom_comap_measure_ne_zero (hC : C.Countable)
    (hf : ∀ᵐ x ∂μ, f x ∈ C) :
    ∀ᵐ x ∂μ, μ (@measurableAtom X (mY.comap f) x) ≠ 0 := by
  simpa only [measurableAtom_comap] using ae_fiber_measure_ne_zero hC hf

theorem map_eq_sum_dirac (hC : C.Countable) (hf : Measurable f)
    (hmem : ∀ᵐ x ∂μ, f x ∈ C) :
    μ.map f = Measure.sum (fun y : C => μ (f ⁻¹' {y.val}) • Measure.dirac y.val) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hf hs, Measure.sum_apply _ hs]
  calc
    μ (f ⁻¹' s) = μ ((f ⁻¹' C) ∩ (f ⁻¹' s)) := by
      apply measure_congr
      filter_upwards [hmem] with x hx
      change (f x ∈ s) = (f x ∈ C ∧ f x ∈ s)
      simp only [hx, true_and]
    _ = (μ.restrict (f ⁻¹' s)) (f ⁻¹' C) :=
      (Measure.restrict_apply (hf hC.measurableSet)).symm
    _ = ∑' y : C, (μ.restrict (f ⁻¹' s)) (f ⁻¹' {y.val}) :=
      (tsum_measure_preimage_singleton hC (fun y _ => hf (measurableSet_singleton y))).symm
    _ = ∑' y : C, (μ (f ⁻¹' {y.val}) • Measure.dirac y.val) s := by
      apply tsum_congr
      intro y
      rw [Measure.restrict_apply (hf (measurableSet_singleton _)),
        Measure.smul_apply, Measure.dirac_apply' _ hs]
      by_cases hy : y.val ∈ s
      · rw [Set.indicator_of_mem hy]
        simp only [Pi.one_apply, smul_eq_mul, mul_one]
        apply congrArg μ
        apply Set.inter_eq_left.2
        intro x hx
        change f x = y.val at hx
        change f x ∈ s
        simpa [hx] using hy
      · rw [Set.indicator_of_notMem hy]
        simp only [smul_eq_mul, mul_zero]
        have hdisj : Disjoint (f ⁻¹' {y.val}) (f ⁻¹' s) := by
          rw [Set.disjoint_left]
          intro x hx hxs
          change f x = y.val at hx
          exact hy (hx ▸ hxs)
        rw [Set.disjoint_iff_inter_eq_empty.1 hdisj, measure_empty]


end InvariantProjection.CountableFiberAtoms

end OAI
