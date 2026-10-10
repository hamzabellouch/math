import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Conservative

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators

namespace InvariantProjection.PolarStructure

theorem countable_finite_drop_values {ι : Type*} [Countable ι] (c : ι → ℝ) :
    (Set.range (fun s : Finset ι => Real.exp (-(∑ i ∈ s, c i)))).Countable :=
  Set.countable_range _

theorem ae_countable_range_of_finite_drops {X ι : Type*} [MeasurableSpace X]
    [Countable ι] {μ : Measure X} (c : ι → ℝ) (f : X → ℝ)
    (hf : ∀ᵐ x ∂μ, ∃ s : Finset ι, f x = Real.exp (-(∑ i ∈ s, c i))) :
    ∃ S : Set ℝ, S.Countable ∧ ∀ᵐ x ∂μ, f x ∈ S := by
  refine ⟨Set.range (fun s : Finset ι => Real.exp (-(∑ i ∈ s, c i))),
    countable_finite_drop_values c, ?_⟩
  filter_upwards [hf] with x hx
  obtain ⟨s, hs⟩ := hx
  exact ⟨s, hs.symm⟩

theorem ae_countable_joint_range {X I Y : Type*} [MeasurableSpace X] [Finite I]
    {μ : Measure X} (f : I → X → Y)
    (hf : ∀ i, ∃ S : Set Y, S.Countable ∧ ∀ᵐ x ∂μ, f i x ∈ S) :
    ∃ R : Set (I → Y), R.Countable ∧ ∀ᵐ x ∂μ, (fun i => f i x) ∈ R := by
  classical
  choose S hS using hf
  refine ⟨{v | ∀ i, v i ∈ S i}, Set.countable_pi (fun i => (hS i).1), ?_⟩
  exact ae_all_iff.2 (fun i => (hS i).2)

theorem ae_countable_joint_range_of_measurePreserving
    {X I Y : Type*} [MeasurableSpace X] [Finite I] {μ : Measure X}
    (σ : I → X → X) (hσ : ∀ i, MeasurePreserving (σ i) μ μ) (f : X → Y)
    (hf : ∃ S : Set Y, S.Countable ∧ ∀ᵐ x ∂μ, f x ∈ S) :
    ∃ R : Set (I → Y), R.Countable ∧ ∀ᵐ x ∂μ, (fun i => f (σ i x)) ∈ R := by
  apply ae_countable_joint_range
  intro i
  obtain ⟨S, hS, hf⟩ := hf
  exact ⟨S, hS, (hσ i).quasiMeasurePreserving.ae hf⟩

theorem ae_nonzero_fiber_of_ae_countable_range
    {X Y : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → Y}
    {S : Set Y} (hS : S.Countable) (hf : ∀ᵐ x ∂μ, f x ∈ S) :
    ∀ᵐ x ∂μ, μ (f ⁻¹' {f x}) ≠ 0 := by
  have := hS.to_subtype
  have hnull : ∀ y : S, ∀ᵐ x ∂μ, μ (f ⁻¹' {(y : Y)}) = 0 → f x ≠ y := by
    intro y
    by_cases hy : μ (f ⁻¹' {(y : Y)}) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hy] with x hx
      intro _
      simpa using hx
    · exact Filter.Eventually.of_forall (fun _ h => (hy h).elim)
  filter_upwards [hf, ae_all_iff.2 hnull] with x hx hforall
  exact fun hzero => hforall ⟨f x, hx⟩ hzero rfl

theorem measure_eq_sum_dirac_of_ae_mem_countable
    {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    {ν : Measure Y} {S : Set Y} (hS : S.Countable) (hν : ∀ᵐ y ∂ν, y ∈ S) :
    ν = Measure.sum (fun y : S => ν {(y : Y)} • Measure.dirac (y : Y)) := by
  classical
  have := hS.to_subtype
  ext t ht
  rw [Measure.sum_apply _ ht]
  calc
    ν t = ν (S ∩ t) := (Measure.measure_inter_eq_of_ae hν).symm
    _ = ν (⋃ y : S, t ∩ {(y : Y)}) := by
      congr 1
      ext y
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hyS, hyt⟩
        exact ⟨⟨y, hyS⟩, hyt, rfl⟩
      · rintro ⟨z, hyt, rfl⟩
        exact ⟨z.property, hyt⟩
    _ = ∑' y : S, ν (t ∩ {(y : Y)}) := by
      apply measure_iUnion
      · intro y z hyz
        apply Set.disjoint_left.2
        intro x hx hy
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff] at hx hy
        exact hyz (Subtype.ext (hx.2.symm.trans hy.2))
      · intro y
        exact ht.inter (measurableSet_singleton _)
    _ = ∑' y : S, (ν {(y : Y)} • Measure.dirac (y : Y)) t := by
      apply tsum_congr
      intro y
      by_cases hy : (y : Y) ∈ t
      · simp [Measure.smul_apply, ht, hy,
          Set.inter_eq_right.mpr (Set.singleton_subset_iff.2 hy)]
      · have hdisj : t ∩ {(y : Y)} = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hx hxy
          exact hy (hxy ▸ hx)
        simp [Measure.smul_apply, ht, hy, hdisj]

theorem map_eq_sum_dirac_of_ae_countable_range
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    {μ : Measure X} {f : X → Y} (hf : AEMeasurable f μ)
    {S : Set Y} (hS : S.Countable) (h : ∀ᵐ x ∂μ, f x ∈ S) :
    μ.map f = Measure.sum (fun y : S => μ (f ⁻¹' {(y : Y)}) • Measure.dirac (y : Y)) := by
  have hmap : ∀ᵐ y ∂μ.map f, y ∈ S := (ae_map_iff hf hS.measurableSet).2 h
  rw [measure_eq_sum_dirac_of_ae_mem_countable hS hmap]
  congr 1
  funext y
  rw [Measure.map_apply_of_aemeasurable hf (measurableSet_singleton _)]

theorem mem_iff_of_eq_of_measurable_comap
    {X Y : Type*} [MeasurableSpace Y] (f : X → Y) {t : Set X}
    (ht : MeasurableSet[MeasurableSpace.comap f inferInstance] t)
    {x z : X} (hxz : f x = f z) : x ∈ t ↔ z ∈ t := by
  obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht
  change f x ∈ B ↔ f z ∈ B
  rw [hxz]

theorem fiber_is_atom_in_comap
    {X Y : Type*} [MeasurableSpace Y] (f : X → Y) (y : Y)
    {t : Set X} (ht : MeasurableSet[MeasurableSpace.comap f inferInstance] t)
    (htsub : t ⊆ f ⁻¹' {y}) : t = ∅ ∨ t = f ⁻¹' {y} := by
  by_cases ht0 : t = ∅
  · exact Or.inl ht0
  · right
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 ht0
    apply Set.Subset.antisymm htsub
    intro z hz
    have hxy : f x = y := htsub hx
    have hzy : f z = y := hz
    exact (mem_iff_of_eq_of_measurable_comap f ht (hxy.trans hzy.symm)).1 hx

theorem countable_atomic_fiber_partition
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {μ : Measure X} {f : X → Y}
    (hf : Measurable f) {S : Set Y} (hS : S.Countable)
    (hrange : ∀ᵐ x ∂μ, f x ∈ S) :
    ∃ C : Set Y, C.Countable ∧ (∀ᵐ x ∂μ, f x ∈ C) ∧
      (∀ y ∈ C, MeasurableSet (f ⁻¹' {y}) ∧ μ (f ⁻¹' {y}) ≠ 0 ∧
        ∀ t : Set X, MeasurableSet[MeasurableSpace.comap f inferInstance] t →
          t ⊆ f ⁻¹' {y} → t = ∅ ∨ t = f ⁻¹' {y}) := by
  refine ⟨{y ∈ S | μ (f ⁻¹' {y}) ≠ 0}, hS.mono (fun _ h => h.1), ?_, ?_⟩
  · filter_upwards [hrange, ae_nonzero_fiber_of_ae_countable_range hS hrange] with x hx hpos
    exact ⟨hx, hpos⟩
  · intro y hy
    exact ⟨hf (measurableSet_singleton y), hy.2, fun _ ht hsub =>
      fiber_is_atom_in_comap f y ht hsub⟩

theorem finite_family_atomic_fiber_partition
    {X I Y : Type*} [MeasurableSpace X] [Finite I] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] {μ : Measure X} (f : I → X → Y)
    (hf : ∀ i, Measurable (f i))
    (hrange : ∀ i, ∃ S : Set Y, S.Countable ∧ ∀ᵐ x ∂μ, f i x ∈ S) :
    ∃ C : Set (I → Y), C.Countable ∧ (∀ᵐ x ∂μ, (fun i => f i x) ∈ C) ∧
      (∀ v ∈ C, MeasurableSet {x | (fun i => f i x) = v} ∧
        μ {x | (fun i => f i x) = v} ≠ 0 ∧
        ∀ t : Set X, MeasurableSet[⨆ i, MeasurableSpace.comap (f i) inferInstance] t →
          t ⊆ {x | (fun i => f i x) = v} →
            t = ∅ ∨ t = {x | (fun i => f i x) = v}) := by
  obtain ⟨S, hS, hvalue⟩ := ae_countable_joint_range f hrange
  obtain ⟨C, hC, hcover, hatom⟩ := countable_atomic_fiber_partition
    (Measurable.of_eval hf) hS hvalue
  refine ⟨C, hC, hcover, ?_⟩
  intro v hv
  obtain ⟨hm, hp, hsmall⟩ := hatom v hv
  refine ⟨hm, hp, ?_⟩
  intro t ht hsub
  apply hsmall t _ hsub
  rwa [MeasurableSpace.comap_process_pi]

theorem not_ae_invariant_of_totalErgodic
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {σ : X → X} (hσ : ∀ n : ℕ, 0 < n → Ergodic σ^[n] μ)
    {s : Set X} (hs : NullMeasurableSet s μ) (hs0 : μ s ≠ 0) (hs1 : μ s ≠ 1)
    {n : ℕ} (hn : 0 < n) : ¬ (σ^[n] ⁻¹' s =ᵐ[μ] s) := by
  intro heq
  rcases (hσ n hn).quasiErgodic.ae_empty_or_univ₀ hs heq with h | h
  · exact hs0 (by simpa using measure_congr h)
  · exact hs1 (by simpa using measure_congr h)

theorem exists_positive_proper_orbit_overlap
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {σ : X → X} (hσ : ∀ n : ℕ, 0 < n → Ergodic σ^[n] μ)
    {s : Set X} (hs : NullMeasurableSet s μ) (hs0 : μ s ≠ 0) (hs1 : μ s ≠ 1) :
    ∃ n : ℕ, 0 < n ∧ μ (s ∩ σ^[n] ⁻¹' s) ≠ 0 ∧ μ (s \ σ^[n] ⁻¹' s) ≠ 0 := by
  have hpres : MeasurePreserving σ μ μ := by
    simpa using (hσ 1 (by omega)).toMeasurePreserving
  obtain ⟨n, hn, hinter⟩ :=
    hpres.conservative.exists_gt_measure_inter_ne_zero hs hs0 0
  refine ⟨n, hn, hinter, ?_⟩
  intro hdiff
  have hle : s ≤ᵐ[μ] σ^[n] ⁻¹' s := ae_le_set.2 hdiff
  rcases (hσ n hn).ae_empty_or_univ_of_ae_le_preimage hs hle with h | h
  · exact hs0 (by simpa using measure_congr h)
  · exact hs1 (by simpa using measure_congr h)

theorem measure_eq_one_of_atom_orbit
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {σ : X → X} (hσ : ∀ n : ℕ, 0 < n → Ergodic σ^[n] μ)
    {s : Set X} (hs : NullMeasurableSet s μ) (hs0 : μ s ≠ 0)
    (horbit : ∀ n : ℕ, 0 < n →
      (σ^[n] ⁻¹' s =ᵐ[μ] s) ∨ AEDisjoint μ s (σ^[n] ⁻¹' s)) : μ s = 1 := by
  by_contra hs1
  obtain ⟨n, hn, hinter, -⟩ := exists_positive_proper_orbit_overlap hσ hs hs0 hs1
  rcases horbit n hn with heq | hdisj
  · exact not_ae_invariant_of_totalErgodic hσ hs hs0 hs1 hn heq
  · exact hinter hdisj

theorem invariant_family_has_no_measure_atoms
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {σ : X → X} (hσ : ∀ n : ℕ, 0 < n → Ergodic σ^[n] μ)
    (A : Set (Set X)) (hmeas : ∀ s ∈ A, NullMeasurableSet s μ)
    (hinter : ∀ s ∈ A, ∀ t ∈ A, s ∩ t ∈ A)
    (hpre : ∀ s ∈ A, σ ⁻¹' s ∈ A)
    (hnontrivial : ∃ b ∈ A, μ b ≠ 0 ∧ μ b ≠ 1) :
    ∀ s ∈ A, μ s ≠ 0 → ∃ t ∈ A, t ⊆ s ∧ μ t ≠ 0 ∧ μ (s \ t) ≠ 0 := by
  intro s hs hs0
  by_cases hs1 : μ s = 1
  · obtain ⟨b, hb, hb0, hb1⟩ := hnontrivial
    have hsfull : ∀ᵐ x ∂μ, x ∈ s := by
      exact ae_iff.2 ((prob_compl_eq_zero_iff₀ (hmeas s hs)).2 hs1)
    refine ⟨s ∩ b, hinter s hs b hb, Set.inter_subset_left, ?_, ?_⟩
    · rwa [Measure.measure_inter_eq_of_ae hsfull]
    · have hset : s \ (s ∩ b) = s ∩ bᶜ := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [hset, Measure.measure_inter_eq_of_ae hsfull]
      exact fun h => hb1 ((prob_compl_eq_zero_iff₀ (hmeas b hb)).1 h)
  · obtain ⟨n, hn, hn0, hndiff⟩ :=
      exists_positive_proper_orbit_overlap hσ (hmeas s hs) hs0 hs1
    have hiter : ∀ k : ℕ, σ^[k] ⁻¹' s ∈ A := by
      intro k
      induction k with
      | zero => simpa using hs
      | succ k ih =>
          simpa only [Function.iterate_succ, Set.preimage_comp] using hpre _ ih
    refine ⟨s ∩ σ^[n] ⁻¹' s, hinter s hs _ (hiter n), Set.inter_subset_left, hn0, ?_⟩
    have hset : s \ (s ∩ σ^[n] ⁻¹' s) = s \ σ^[n] ⁻¹' s := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rwa [hset]

end InvariantProjection.PolarStructure

end OAI
