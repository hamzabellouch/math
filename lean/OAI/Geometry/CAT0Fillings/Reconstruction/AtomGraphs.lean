import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.FiniteAtoms

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
lemma zeroChart_exists_supported_atom [Nonempty X] (C : IntegerChart X 0) :
    ∃ a : ℤ, ∃ x : X, (a ≠ 0 → x ∈ C.image) ∧ C.action = atomCurrent a x := by
  by_cases h : (0 : Euc 0) ∈ C.domain
  · exact ⟨C.multiplicity 0, C.param ⟨0, h⟩,
      fun _ => ⟨⟨0, h⟩, rfl⟩, C.zero_action h⟩
  · refine ⟨0, Classical.arbitrary X, fun ha => (ha rfl).elim, ?_⟩
    rw [C.zero_action_eq_zero h]
    funext b π
    simp only [atomCurrent, Int.cast_zero, zero_mul, ite_self, Pi.zero_apply]

theorem integerRectifiable_zero_distinct_representation [CompactSpace X] [Nonempty X]
    {T : Functional X 0} (hT : IsMetricCurrent T) (hI : IntegerRectifiable T) :
    ∃ (m : ℕ) (a : Fin m → ℤ) (x : Fin m → X),
      (∀ i, a i ≠ 0) ∧ Function.Injective x ∧
      ∀ b π, T b π = ∑ i, atomCurrent (a i) (x i) b π := by
  classical
  obtain ⟨C, hd, hC, hCS, heq⟩ := hI
  choose a x hsupp hact using fun i => zeroChart_exists_supported_atom (C i)
  have hmass i : mass (C i).action = |(a i : ℝ)| := by
    rw [hact i, mass_atomCurrent]
  have haS : Summable (fun i => |(a i : ℝ)|) := by simpa only [hmass] using hCS
  have hfinite := finite_support_int_of_summable_abs a haS
  let s := hfinite.toFinset
  have hs : ∀ i, i ∈ s ↔ a i ≠ 0 := fun i => hfinite.mem_toFinset
  let e := s.equivFin.symm
  have hezero : ∀ i, a (e i) ≠ 0 := fun i => (hs _).mp (e i).property
  refine ⟨s.card, fun i => a (e i), fun i => x (e i), hezero, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    by_contra hne
    have hi : x (e i) ∈ (C (e i)).image := hsupp _ (hezero i)
    have hj : x (e i) ∈ (C (e j)).image := by
      simpa only [hij] using hsupp _ (hezero j)
    exact Set.disjoint_left.mp (hd hne) hi hj
  · intro b π
    by_cases hadm : Admissible b π
    · rw [heq]
      simp_rw [hact]
      rw [tsum_eq_sum (s := s) (fun i hi => by
        have hai : a i = 0 := not_not.mp (fun hn => hi ((hs i).mpr hn))
        simp only [atomCurrent, hai, Int.cast_zero, zero_mul, ite_self])]
      rw [← Finset.sum_attach]
      exact (e.sum_comp (fun i : s => atomCurrent (a i) (x i) b π)).symm
    · simp only [hT.offDomain b π hadm, atomCurrent, ite_eq_right hadm, Finset.sum_const_zero]

def atomicTent (p : X) (r : ℝ) (z : X) : ℝ :=
  min (dist z p) (max 0 (r - dist z p))

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_lipschitz (p : X) (r : ℝ) : LipschitzWith 1 (atomicTent p r) := by
  have hdist : LipschitzWith 1 (fun z : X => dist z p) := LipschitzWith.dist_left p
  have hsub : LipschitzWith 1 (fun z : X => r - dist z p) := by
    simpa using (LipschitzWith.const r).sub hdist
  have hother : LipschitzWith 1 (fun z : X => max 0 (r - dist z p)) :=
    hsub.const_max 0
  change LipschitzWith 1 (fun z : X => min (dist z p) (max 0 (r - dist z p)))
  simpa only [max_self] using hdist.min hother

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_unit_bound (p : X) {r : ℝ} (hr : r ≤ 1) (z : X) :
    |atomicTent p r z| ≤ 1 := by
  have h0 : 0 ≤ atomicTent p r z := le_min dist_nonneg (le_max_left _ _)
  rw [abs_of_nonneg h0]
  exact (min_le_right _ _).trans (max_le (by norm_num)
    ((sub_le_self _ dist_nonneg).trans hr))

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma atomicTent_center (p : X) (r : ℝ) : atomicTent p r p = 0 := by
  simp [atomicTent]

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_near {p z : X} {r : ℝ} (h : 2 * dist z p ≤ r) :
    atomicTent p r z = dist z p := by
  exact min_eq_left ((by linarith : dist z p ≤ r - dist z p).trans (le_max_right _ _))

omit [MeasurableSpace X] [BorelSpace X] in
lemma atomicTent_far {p z : X} {r : ℝ} (h : r ≤ dist z p) :
    atomicTent p r z = 0 := by
  simp only [atomicTent, max_eq_left (sub_nonpos.mpr h), min_eq_right dist_nonneg]

omit [MeasurableSpace X] [BorelSpace X] in
lemma matched_atom_distance_le {m : ℕ} {S U : Functional X 0}
    (a a' : Fin m → ℤ) (x y : Fin m → X)
    (hS : ∀ b π, S b π = ∑ j, atomCurrent (a j) (x j) b π)
    (hU : ∀ b π, U b π = ∑ j, atomCurrent (a' j) (y j) b π)
    (i : Fin m) (hai : a' i ≠ 0) {r D : ℝ} (hr : r ≤ 1)
    (hnear : 2 * dist (y i) (x i) ≤ r)
    (hx : ∀ j, j ≠ i → r ≤ dist (x j) (x i))
    (hy : ∀ j, j ≠ i → r ≤ dist (y j) (x i))
    (hD : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      |S b (fun j => Fin.elim0 j) - U b (fun j => Fin.elim0 j)| ≤ D) :
    dist (x i) (y i) ≤ D := by
  classical
  let b := atomicTent (x i) r
  have hbl : BoundedLip b :=
    ⟨⟨1, atomicTent_lipschitz _ _⟩, 1, atomicTent_unit_bound _ hr⟩
  have hbx j : b (x j) = 0 := by
    by_cases hji : j = i
    · subst j; exact atomicTent_center _ _
    · exact atomicTent_far (hx j hji)
  have hby (j : Fin m) (hji : j ≠ i) : b (y j) = 0 := atomicTent_far (hy j hji)
  have hsi : S b (fun j => Fin.elim0 j) = 0 := by
    rw [hS]
    apply Finset.sum_eq_zero
    intro j _
    rw [atomCurrent_apply _ _ hbl, hbx, mul_zero]
  have hui : U b (fun j => Fin.elim0 j) = (a' i : ℝ) * dist (y i) (x i) := by
    rw [hU, Finset.sum_eq_single i]
    · rw [atomCurrent_apply _ _ hbl]
      change _ * atomicTent (x i) r (y i) = _
      rw [atomicTent_near hnear]
    · intro j _ hji
      rw [atomCurrent_apply _ _ hbl, hby j hji, mul_zero]
    · simp
  have hbound := hD b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hr)
  rw [hsi, hui, zero_sub, abs_neg, abs_mul, abs_of_nonneg dist_nonneg] at hbound
  have ha1 : (1 : ℝ) ≤ |(a' i : ℝ)| := by exact_mod_cast Int.one_le_abs hai
  calc
    dist (x i) (y i) = 1 * dist (y i) (x i) := by simp [dist_comm]
    _ ≤ |(a' i : ℝ)| * dist (y i) (x i) := mul_le_mul_of_nonneg_right ha1 dist_nonneg
    _ ≤ D := hbound

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def UnitRepresentation {m : ℕ} (S : Functional X 0) (a : Fin m → ℤ) (x : Fin m → X) : Prop :=
  ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
    S b (fun j => Fin.elim0 j) = ∑ j, (a j : ℝ) * b (x j)

abbrev AtomCode := Σ m : ℕ, (Fin m → ℤ) × (Fin m → ℕ) × ℚ
namespace AtomCode
abbrev size (c : AtomCode) := c.1
abbrev weights (c : AtomCode) : Fin c.size → ℤ := c.2.1
abbrev centers (c : AtomCode) : Fin c.size → ℕ := c.2.2.1
abbrev radius (c : AtomCode) : ℝ := (c.2.2.2 : ℝ)

def Valid [SeparableSpace X] [Nonempty X] (c : AtomCode) : Prop :=
  0 < c.radius ∧ 4 * c.radius ≤ 1 ∧ (∀ i, c.weights i ≠ 0) ∧
    ∀ i j, i ≠ j → 8 * c.radius ≤
      dist (TopologicalSpace.denseSeq X (c.centers i)) (TopologicalSpace.denseSeq X (c.centers j))
end AtomCode

lemma atomCode_countable : Countable AtomCode := inferInstance

omit [MeasurableSpace X] [BorelSpace X] in
lemma exists_separated_center_code [SeparableSpace X] [Nonempty X]
    {m : ℕ} (x : Fin m → X) (hx : Function.Injective x) :
    ∃ (r : ℚ) (c : Fin m → ℕ), 0 < (r : ℝ) ∧ 4 * (r : ℝ) ≤ 1 ∧
      (∀ i, dist (x i) (TopologicalSpace.denseSeq X (c i)) ≤ (r : ℝ)) ∧
      ∀ i j, i ≠ j → 8 * (r : ℝ) ≤
        dist (TopologicalSpace.denseSeq X (c i)) (TopologicalSpace.denseSeq X (c j)) := by
  have he : ∀ᶠ r : ℝ in 𝓝 0, r < 1 / 4 ∧
      ∀ i j : Fin m, i ≠ j → 10 * r < dist (x i) (x j) := by
    refine (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).and ?_
    simp only [Filter.eventually_all]
    intro i j hij
    have hd : 0 < dist (x i) (x j) := dist_pos.mpr (fun h => hij (hx h))
    filter_upwards [eventually_lt_nhds (by positivity : (0 : ℝ) < dist (x i) (x j) / 10)] with r hr
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨r, hr0, hrδ⟩ := exists_pos_rat_lt hδ
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hr := hball (show (r : ℝ) ∈ ball (0 : ℝ) δ by
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr0'] using hrδ)
  choose c hc using fun i : Fin m =>
    (TopologicalSpace.denseRange_denseSeq X).exists_dist_lt (x i) hr0'
  refine ⟨r, c, hr0', by linarith [hr.1], fun i => (hc i).le, ?_⟩
  intro i j hij
  have hd := hr.2 i j hij
  have htri : dist (x i) (x j) ≤
      dist (x i) (TopologicalSpace.denseSeq X (c i)) +
      dist (TopologicalSpace.denseSeq X (c i)) (TopologicalSpace.denseSeq X (c j)) +
      dist (x j) (TopologicalSpace.denseSeq X (c j)) := by
    calc
      _ ≤ dist (x i) (TopologicalSpace.denseSeq X (c i)) +
          dist (TopologicalSpace.denseSeq X (c i)) (x j) := dist_triangle _ _ _
      _ ≤ _ := by
        have := dist_triangle (TopologicalSpace.denseSeq X (c i))
          (TopologicalSpace.denseSeq X (c j)) (x j)
        rw [dist_comm (TopologicalSpace.denseSeq X (c j)) (x j)] at this
        linarith
  linarith [hc i, hc j]

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitRepresentation_matched_distance [SeparableSpace X] [Nonempty X]
    {S U : Functional X 0} (c : AtomCode) (hc : c.Valid (X := X))
    (x y : Fin c.size → X)
    (hx : ∀ i, dist (x i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius)
    (hy : ∀ i, dist (y i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius)
    (hS : UnitRepresentation S c.weights x) (hU : UnitRepresentation U c.weights y)
    {D : ℝ}
    (hD : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      |S b (fun j => Fin.elim0 j) - U b (fun j => Fin.elim0 j)| ≤ D)
    (i : Fin c.size) : dist (x i) (y i) ≤ D := by
  classical
  let p j := TopologicalSpace.denseSeq X (c.centers j)
  have hnear : 2 * dist (y i) (x i) ≤ 4 * c.radius := by
    have ht := dist_triangle_right (y i) (x i) (p i)
    linarith [hx i, hy i]
  have hfar (z : Fin c.size → X) (hz : ∀ j, dist (z j) (p j) ≤ c.radius)
      (j : Fin c.size) (hji : j ≠ i) : 4 * c.radius ≤ dist (z j) (x i) := by
    have ht : dist (p j) (p i) ≤ dist (z j) (p j) + dist (z j) (x i) + dist (x i) (p i) := by
      calc
        _ ≤ dist (p j) (z j) + dist (z j) (p i) := dist_triangle _ _ _
        _ ≤ _ := by
          have := dist_triangle (z j) (x i) (p i)
          rw [dist_comm (p j) (z j)]
          linarith
    linarith [hc.2.2.2 j i hji, hz j, hx i, hc.1]
  let b := atomicTent (x i) (4 * c.radius)
  have hbx j : b (x j) = 0 := by
    by_cases hji : j = i
    · subst j; exact atomicTent_center _ _
    · exact atomicTent_far (hfar x hx j hji)
  have hsi : S b (fun j => Fin.elim0 j) = 0 := by
    rw [hS b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hc.2.1)]
    apply Finset.sum_eq_zero
    intro j _
    rw [hbx, mul_zero]
  have hui : U b (fun j => Fin.elim0 j) = (c.weights i : ℝ) * dist (y i) (x i) := by
    rw [hU b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hc.2.1), Finset.sum_eq_single i]
    · change _ * atomicTent _ _ _ = _
      rw [atomicTent_near hnear]
    · intro j _ hji
      change _ * atomicTent _ _ _ = _
      rw [atomicTent_far (hfar y hy j hji), mul_zero]
    · simp
  have hbound := hD b (atomicTent_lipschitz _ _) (atomicTent_unit_bound _ hc.2.1)
  rw [hsi, hui, zero_sub, abs_neg, abs_mul, abs_of_nonneg dist_nonneg] at hbound
  have ha1 : (1 : ℝ) ≤ |(c.weights i : ℝ)| := by exact_mod_cast Int.one_le_abs (hc.2.2.1 i)
  calc
    dist (x i) (y i) = 1 * dist (y i) (x i) := by simp [dist_comm]
    _ ≤ |(c.weights i : ℝ)| * dist (y i) (x i) := mul_le_mul_of_nonneg_right ha1 dist_nonneg
    _ ≤ D := hbound

variable {P : Type*} [MetricSpace P]

def atomDomain [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) : Set P :=
  {t | t ∈ E ∧ c.Valid (X := X) ∧ ∃ x : Fin c.size → X,
    (∀ i, dist (x i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius) ∧
    UnitRepresentation (S t) c.weights x}

omit [MeasurableSpace X] [BorelSpace X] [MetricSpace P] in
lemma atomDomain_subset [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) : atomDomain S E c ⊆ E :=
  fun _ h => h.1

omit [MeasurableSpace X] [BorelSpace X] in
lemma isCompact_atomDomain [CompactSpace X] [Nonempty X]
    (S : P → Functional X 0) {E : Set P} (hE : IsCompact E) (c : AtomCode)
    (hS : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      ContinuousOn (fun t => S t b (fun j => Fin.elim0 j)) E) :
    IsCompact (atomDomain S E c) := by
  apply hE.of_isClosed_subset _ (atomDomain_subset S E c)
  apply IsSeqClosed.isClosed
  intro z t hz hzt
  have htE : t ∈ E := hE.isClosed.mem_of_tendsto hzt (Eventually.of_forall fun j => (hz j).1)
  choose x hx hrepr using fun j => (hz j).2.2
  obtain ⟨y, φ, hφ, hy⟩ := CompactSpace.tendsto_subseq x
  have hyi i : Tendsto (fun j => x (φ j) i) atTop (𝓝 (y i)) :=
    (continuous_apply i).tendsto _ |>.comp hy
  refine ⟨htE, (hz 0).2.1, y, ?_, ?_⟩
  · intro i
    exact le_of_tendsto ((hyi i).dist tendsto_const_nhds)
      (Eventually.of_forall fun j => hx (φ j) i)
  · intro b hb hb1
    have hztE : Tendsto z atTop (𝓝[E] t) := tendsto_nhdsWithin_iff.mpr
      ⟨hzt, Eventually.of_forall fun j => (hz j).1⟩
    have hL := ((hS b hb hb1 t htE).tendsto.comp hztE).comp hφ.tendsto_atTop
    have hR : Tendsto (fun j => ∑ i, (c.weights i : ℝ) * b (x (φ j) i)) atTop
        (𝓝 (∑ i, (c.weights i : ℝ) * b (y i))) := by
      apply tendsto_finsetSum
      intro i _
      exact tendsto_const_nhds.mul ((hb.continuous.tendsto _).comp (hyi i))
    have hL' : Tendsto (fun j => ∑ i, (c.weights i : ℝ) * b (x (φ j) i)) atTop
        (𝓝 (S t b (fun j => Fin.elim0 j))) := by
      convert hL using 1
      funext j
      exact (hrepr (φ j) b hb hb1).symm
    exact tendsto_nhds_unique hL' hR

omit [MetricSpace P] in
lemma integral_mem_atomDomain [CompactSpace X] [Nonempty X]
    (S : P → Functional X 0) {E : Set P} {t : P} (ht : t ∈ E)
    (hI : IsIntegral 0 (S t)) : ∃ c : AtomCode, t ∈ atomDomain S E c := by
  classical
  obtain ⟨m, a, x, ha, hinj, hrepr⟩ := integerRectifiable_zero_distinct_representation hI.1 hI.2
  obtain ⟨r, centers, hr0, hr1, hx, hsep⟩ := exists_separated_center_code x hinj
  let c : AtomCode := ⟨m, a, centers, r⟩
  refine ⟨c, ht, ⟨hr0, hr1, ha, hsep⟩, x, hx, ?_⟩
  intro b hb hb1
  rw [hrepr]
  apply Finset.sum_congr rfl
  intro i _
  exact atomCurrent_apply _ _ ⟨⟨1, hb⟩, 1, hb1⟩

noncomputable def selectedAtom [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode)
    (t : atomDomain S E c) : Fin c.size → X := Classical.choose t.property.2.2

omit [MeasurableSpace X] [BorelSpace X] [MetricSpace P] in
lemma selectedAtom_spec [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) (t : atomDomain S E c) :
    (∀ i, dist (selectedAtom S E c t i) (TopologicalSpace.denseSeq X (c.centers i)) ≤ c.radius) ∧
    UnitRepresentation (S t) c.weights (selectedAtom S E c t) := Classical.choose_spec t.property.2.2

omit [MeasurableSpace X] [BorelSpace X] in
lemma selectedAtom_lipschitz [SeparableSpace X] [Nonempty X]
    (S : P → Functional X 0) (E : Set P) (c : AtomCode) {K : ℝ≥0}
    (hS : ∀ b : X → ℝ, LipschitzWith 1 b → (∀ z, |b z| ≤ 1) →
      LipschitzOnWith K (fun t => S t b (fun j => Fin.elim0 j)) E)
    (i : Fin c.size) : LipschitzWith K (fun t : atomDomain S E c => selectedAtom S E c t i) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro s t
  apply unitRepresentation_matched_distance c s.property.2.1
    (selectedAtom S E c s) (selectedAtom S E c t)
    (selectedAtom_spec S E c s).1 (selectedAtom_spec S E c t).1
    (selectedAtom_spec S E c s).2 (selectedAtom_spec S E c t).2
  intro b hb hb1
  simpa only [Real.dist_eq, Subtype.dist_eq] using (hS b hb hb1).dist_le_mul s s.property.1 t t.property.1

end CAT0Fillings.SliceReconstruction
end

end OAI
