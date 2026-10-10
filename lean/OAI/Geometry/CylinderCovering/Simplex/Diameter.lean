import OAI.Geometry.CylinderCovering.Simplex.DiameterDefinitions

namespace OAI

open Set Metric

namespace CylinderCovering.SimplexDiameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma chordLength_zero {S : Set E} (hS : S.Nonempty) (u : E) :
    ChordLength S u 0 := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨le_rfl, x, hx, by simpa using hx⟩

lemma chordLength_le_diam {S : Set E} {u : E} {r : ℝ}
    (hS : Bornology.IsBounded S) (hu : ‖u‖ = 1) (hr : ChordLength S u r) :
    r ≤ diam S := by
  obtain ⟨hr, x, hx, hy⟩ := hr
  have hd := dist_le_diam_of_mem hS hy hx
  simpa [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hu] using hd

lemma chordLength_segment {S : Set E} {u : E} {r : ℝ}
    (hS : Convex ℝ S) (hr : ChordLength S u r) :
    ∃ x ∈ S, segment ℝ x (x + r • u) ⊆ S := by
  obtain ⟨_, x, hx, hy⟩ := hr
  exact ⟨x, hx, hS.segment_subset hx hy⟩

lemma chordLengths_compact {S : Set E} (hS : IsCompact S) {u : E}
    (hu : ‖u‖ = 1) : IsCompact {r : ℝ | ChordLength S u r} := by
  let K : Set (E × ℝ) := (S ×ˢ Icc 0 (diam S)) ∩
    {p | p.1 + p.2 • u ∈ S}
  have hK : IsCompact K := by
    apply (hS.prod isCompact_Icc).inter_right
    exact hS.isClosed.preimage (continuous_fst.add (continuous_snd.smul continuous_const))
  have heq : {r : ℝ | ChordLength S u r} = Prod.snd '' K := by
    ext r
    constructor
    · intro hr
      obtain ⟨hr0, x, hx, hxr⟩ := hr
      exact ⟨(x, r), ⟨⟨hx, hr0, chordLength_le_diam hS.isBounded hu
        ⟨hr0, x, hx, hxr⟩⟩, hxr⟩, rfl⟩
    · rintro ⟨⟨x, s⟩, ⟨⟨hx, hs0, _⟩, hxs⟩, rfl⟩
      exact ⟨hs0, x, hx, hxs⟩
  rw [heq]
  exact hK.image continuous_snd

lemma maxChord_attained {S : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    {u : E} (hu : ‖u‖ = 1) : ChordLength S u (maxChord S u) := by
  exact (chordLengths_compact hS hu).sSup_mem ⟨0, chordLength_zero hne u⟩

lemma maxChord_nonneg {S : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    {u : E} (hu : ‖u‖ = 1) : 0 ≤ maxChord S u :=
  (maxChord_attained hS hne hu).1

lemma maxChord_le_diam {S : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    {u : E} (hu : ‖u‖ = 1) : maxChord S u ≤ diam S :=
  chordLength_le_diam hS.isBounded hu (maxChord_attained hS hne hu)

lemma chordLength_le_maxChord {S : Set E} (hS : IsCompact S)
    {u : E} (hu : ‖u‖ = 1) {r : ℝ} (hr : ChordLength S u r) :
    r ≤ maxChord S u := by
  exact le_csSup (chordLengths_compact hS hu).bddAbove hr

omit [NormedSpace ℝ E] in
lemma compact_diameter_attained {S : Set E} (hS : IsCompact S) (hne : S.Nonempty) :
    ∃ x ∈ S, ∃ y ∈ S, dist x y = diam S := by
  obtain ⟨⟨x, y⟩, hxy, hmax⟩ := (hS.prod hS).exists_isMaxOn
    (hne.prod hne) (continuous_fst.dist continuous_snd).continuousOn
  refine ⟨x, hxy.1, y, hxy.2, le_antisymm
    (dist_le_diam_of_mem hS.isBounded hxy.1 hxy.2) ?_⟩
  apply diam_le_of_forall_dist_le (dist_nonneg (x := x) (y := y))
  intro a ha b hb
  exact hmax (show (a, b) ∈ S ×ˢ S from ⟨ha, hb⟩)

lemma exists_maxChord_eq_diam {S : Set E} (hS : IsCompact S) (hne : S.Nonempty)
    (hd : 0 < diam S) : ∃ u : E, ‖u‖ = 1 ∧ maxChord S u = diam S := by
  obtain ⟨x, hx, y, hy, hxy⟩ := compact_diameter_attained hS hne
  have hn : ‖y - x‖ = diam S := by
    simpa [dist_eq_norm, norm_sub_rev] using hxy
  have hne0 : y - x ≠ 0 := norm_pos_iff.mp (hn ▸ hd)
  let u := NormedSpace.normalize (y - x)
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hne0
  refine ⟨u, hu, le_antisymm (maxChord_le_diam hS hne hu) ?_⟩
  apply chordLength_le_maxChord hS hu
  refine ⟨hd.le, x, hx, ?_⟩
  rw [← hn, show u = NormedSpace.normalize (y - x) from rfl,
    NormedSpace.norm_smul_normalize]
  simpa using hy

lemma convexHull_pair_distance {ι : Type*} (v : ι → E) {x y : E}
    (hx : x ∈ convexHull ℝ (range v)) (hy : y ∈ convexHull ℝ (range v)) :
    ∃ i j, dist x y ≤ dist (v i) (v j) := by
  obtain ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, h⟩ :=
    convexHull_exists_dist_ge2 hx hy
  exact ⟨i, j, h⟩

lemma finite_convexHull_diameter_attained {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → E) : ∃ i j, diam (convexHull ℝ (range v)) = dist (v i) (v j) := by
  have hc : IsCompact (range v) := (finite_range v).isCompact
  obtain ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, h⟩ := compact_diameter_attained hc
    (range_nonempty v)
  exact ⟨i, j, by simpa using h.symm⟩

lemma regular_convexHull_diameter {ι : Type*} [Finite ι] [Nontrivial ι]
    (v : ι → E) {edge : ℝ} (he : 0 ≤ edge)
    (hv : ∀ i j, i ≠ j → dist (v i) (v j) = edge) :
    diam (convexHull ℝ (range v)) = edge := by
  rw [convexHull_diam]
  apply le_antisymm
  · apply diam_le_of_forall_dist_le he
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    by_cases hij : i = j
    · simpa [hij] using he
    · exact (hv i j hij).le
  · obtain ⟨i, j, hij⟩ := exists_pair_ne ι
    rw [← hv i j hij]
    exact dist_le_diam_of_mem (finite_range v).isBounded (mem_range_self i)
      (mem_range_self j)

lemma maxChord_pos_of_interior {S : Set E} (hS : IsCompact S)
    (hint : (interior S).Nonempty) {u : E} (hu : ‖u‖ = 1) :
    0 < maxChord S u := by
  obtain ⟨x, hx⟩ := hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hhalf : ChordLength S u (ε / 2) := by
    refine ⟨by positivity, x, mem_of_mem_of_subset hx interior_subset, hball ?_⟩
    rw [mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu, mul_one]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  exact (by positivity : 0 < ε / 2).trans_le (chordLength_le_maxChord hS hu hhalf)

lemma projection_minimum_of_chord_identity {S : Set E} (hS : IsCompact S)
    (hne : S.Nonempty) (hd : 0 < diam S) (A : E → ℝ) (C : ℝ)
    (hA : ∀ u, ‖u‖ = 1 → 0 ≤ A u)
    (hidentity : ∀ u, ‖u‖ = 1 → A u * maxChord S u = C) :
    IsLeast {a : ℝ | ∃ u : E, ‖u‖ = 1 ∧ A u = a} (C / diam S) := by
  obtain ⟨u, hu, hmax⟩ := exists_maxChord_eq_diam hS hne hd
  have hmin : A u = C / diam S := by
    apply (eq_div_iff hd.ne').mpr
    simpa [hmax] using hidentity u hu
  refine ⟨⟨u, hu, hmin⟩, ?_⟩
  rintro a ⟨v, hv, rfl⟩
  apply (div_le_iff₀ hd).mpr
  rw [← hidentity v hv]
  exact mul_le_mul_of_nonneg_left (maxChord_le_diam hS hne hv) (hA v hv)

lemma finite_edge_maxChord {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → E) (hd : 0 < diam (convexHull ℝ (range v))) :
    ∃ i j, i ≠ j ∧
      ‖NormedSpace.normalize (v j - v i)‖ = 1 ∧
      maxChord (convexHull ℝ (range v)) (NormedSpace.normalize (v j - v i)) =
        diam (convexHull ℝ (range v)) := by
  let S := convexHull ℝ (range v)
  have hc : IsCompact S := (finite_range v).isCompact_convexHull ℝ
  have hne : S.Nonempty := (range_nonempty v).mono (subset_convexHull ℝ _)
  obtain ⟨i, j, hdij⟩ := finite_convexHull_diameter_attained v
  have hn : ‖v j - v i‖ = diam S := by
    simpa [S, dist_eq_norm, norm_sub_rev] using hdij.symm
  have hn0 : v j - v i ≠ 0 := norm_pos_iff.mp (hn ▸ hd)
  have hij : i ≠ j := by
    intro h
    apply hn0
    simp [h]
  have hu : ‖NormedSpace.normalize (v j - v i)‖ = 1 :=
    NormedSpace.norm_normalize hn0
  refine ⟨i, j, hij, hu, le_antisymm (maxChord_le_diam hc hne hu) ?_⟩
  apply chordLength_le_maxChord hc hu
  refine ⟨hd.le, v i, subset_convexHull ℝ _ (mem_range_self i), ?_⟩
  rw [← hn, NormedSpace.norm_smul_normalize]
  simpa using subset_convexHull ℝ (range v) (mem_range_self j)

lemma finite_edge_projection_minimizer {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → E) (hd : 0 < diam (convexHull ℝ (range v)))
    (A : E → ℝ) (C : ℝ) (hA : ∀ u, ‖u‖ = 1 → 0 ≤ A u)
    (hidentity : ∀ u, ‖u‖ = 1 → A u * maxChord (convexHull ℝ (range v)) u = C) :
    ∃ i j, i ≠ j ∧
      ‖NormedSpace.normalize (v j - v i)‖ = 1 ∧
      A (NormedSpace.normalize (v j - v i)) = C / diam (convexHull ℝ (range v)) ∧
      ∀ u, ‖u‖ = 1 → A (NormedSpace.normalize (v j - v i)) ≤ A u := by
  obtain ⟨i, j, hij, hu, hchord⟩ := finite_edge_maxChord v hd
  have hval : A (NormedSpace.normalize (v j - v i)) =
      C / diam (convexHull ℝ (range v)) := by
    apply (eq_div_iff hd.ne').mpr
    simpa [hchord] using hidentity _ hu
  refine ⟨i, j, hij, hu, hval, ?_⟩
  intro u hu'
  rw [hval]
  exact (projection_minimum_of_chord_identity
    ((finite_range v).isCompact_convexHull ℝ)
    ((range_nonempty v).mono (subset_convexHull ℝ _)) hd A C hA hidentity).2
      ⟨u, hu', rfl⟩

lemma affineIndependent_diameter_pos {ι : Type*} [Finite ι] [Nontrivial ι]
    {v : ι → E} (hv : AffineIndependent ℝ v) :
    0 < diam (convexHull ℝ (range v)) := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  apply Metric.diam_pos
  · exact ⟨v i, subset_convexHull ℝ _ (mem_range_self i),
      v j, subset_convexHull ℝ _ (mem_range_self j), fun h => hij (hv.injective h)⟩
  · exact ((finite_range v).isCompact_convexHull ℝ).isBounded

lemma regular_edge_maxChord {ι : Type*} [Finite ι] [Nontrivial ι]
    (v : ι → E) {edge : ℝ} (he : 0 < edge)
    (hv : ∀ i j, i ≠ j → dist (v i) (v j) = edge)
    {i j : ι} (hij : i ≠ j) :
    ‖NormedSpace.normalize (v j - v i)‖ = 1 ∧
    maxChord (convexHull ℝ (range v)) (NormedSpace.normalize (v j - v i)) = edge := by
  have hn : ‖v j - v i‖ = edge := by
    simpa [dist_eq_norm, norm_sub_rev] using hv i j hij
  have hvne : v j - v i ≠ 0 := norm_pos_iff.mp (hn ▸ he)
  have hu := NormedSpace.norm_normalize hvne
  have hc := (finite_range v).isCompact_convexHull ℝ
  have hne := (range_nonempty v).mono (subset_convexHull ℝ _)
  refine ⟨hu, le_antisymm ?_ ?_⟩
  · exact (maxChord_le_diam hc hne hu).trans_eq (regular_convexHull_diameter v he.le hv)
  · apply chordLength_le_maxChord hc hu
    refine ⟨he.le, v i, subset_convexHull ℝ _ (mem_range_self i), ?_⟩
    rw [← hn, NormedSpace.norm_smul_normalize]
    simpa using subset_convexHull ℝ (range v) (mem_range_self j)

end CylinderCovering.SimplexDiameter

end OAI
