import OAI.Combinatorics.PlanarL1.Columns

namespace OAI

section

namespace PlanarL1
namespace Columns
namespace Model

variable {n : ℕ} (M : Model n)
namespace Point

variable {M} {J : Set ℝ} {root : Fin n}

lemma paths_nonempty (x y : M.Point J root) : Nonempty (M.Path J x.column y.column) := by
  obtain ⟨p⟩ := x.reachable.symm.trans y.reachable
  obtain ⟨q, _⟩ := Path.exists_word p
  exact ⟨q⟩

noncomputable def distance (x y : M.Point J root) : ℝ :=
  ⨅ p : M.Path J x.column y.column, p.length x.height y.height

lemma lengths_bddBelow (x y : M.Point J root) :
    BddBelow (Set.range fun p : M.Path J x.column y.column => p.length x.height y.height) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact p.length_nonneg _ _⟩

lemma distance_le (x y : M.Point J root) (p : M.Path J x.column y.column) :
    x.distance y ≤ p.length x.height y.height :=
  ciInf_le (x.lengths_bddBelow y) p

lemma distance_nonneg (x y : M.Point J root) : 0 ≤ x.distance y := by
  have :=  x.paths_nonempty y
  exact le_ciInf (fun p => p.length_nonneg _ _)

lemma height_change_le (x y : M.Point J root) : |x.height - y.height| ≤ x.distance y := by
  have :=  x.paths_nonempty y
  exact le_ciInf (fun p => p.height_change_le _ _)

lemma distance_self (x : M.Point J root) : x.distance x = 0 := by
  apply le_antisymm _ (x.distance_nonneg x)
  simpa only [Path.length, sub_self, abs_zero] using x.distance_le x (.nil _)

lemma distance_triangle (x y z : M.Point J root) :
    x.distance z ≤ x.distance y + y.distance z := by
  have :=  x.paths_nonempty y
  have :=  y.paths_nonempty z
  apply le_ciInf_add
  intro p
  apply le_add_ciInf
  intro q
  exact (x.distance_le z (p.append q)).trans (p.length_append_le q _ _ _)

lemma distance_comm (x y : M.Point J root) : x.distance y = y.distance x := by
  have :=  x.paths_nonempty y
  have :=  y.paths_nonempty x
  suffices ∀ x y : M.Point J root, x.distance y ≤ y.distance x by
    exact le_antisymm (this x y) (this y x)
  intro x y
  have :=  y.paths_nonempty x
  apply le_ciInf
  intro p
  simpa only [Path.length_reverse] using x.distance_le y p.reverse

noncomputable instance : PseudoMetricSpace (M.Point J root) where
  dist := distance
  dist_self := distance_self
  dist_comm := distance_comm
  dist_triangle := distance_triangle

/-- The full vertical interval is isometric, before or after the quotient.
No path's vertical variation can improve upon direct travel. -/
lemma dist_same_column (x y : M.Point J root) (h : x.column = y.column) :
    dist x y = |x.height - y.height| := by
  rcases x with ⟨i, a, ha, hx⟩
  rcases y with ⟨j, b, hb, hy⟩
  change i = j at h
  subst j
  let x : M.Point J root := ⟨i, a, ha, hx⟩
  let y : M.Point J root := ⟨i, b, hb, hy⟩
  exact le_antisymm (x.distance_le y (.nil i)) (x.height_change_le y)

/-- Vertical motion on a chosen column representative. -/
def withHeight (x : M.Point J root) (H : ℝ) (hH : H ∈ J) : M.Point J root :=
  ⟨x.column, H, hH, x.reachable⟩

@[simp] lemma withHeight_self (x : M.Point J root) :
    x.withHeight x.height x.inBand = x := rfl

lemma dist_withHeight (x : M.Point J root) (H : ℝ) (hH : H ∈ J) :
    dist x (x.withHeight H hH) = |x.height - H| := x.dist_same_column _ rfl

lemma dist_le_switch (x y : M.Point J root) {H : ℝ} (hH : H ∈ J)
    (hs : H ∈ M.heights x.column y.column) :
    dist x y ≤ |x.height - H| + |H - y.height| :=
  x.distance_le y (.cons H hH hs (.nil _))

/-- The source's adjacent-midpoint estimate: one available switch costs at
most the width of the band. -/
lemma dist_midpoints_le (x y : M.Point J root) {H a : ℝ}
    (hx : x.height = H) (hy : y.height = H)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (h : (M.activeGraph J).Adj x.column y.column) : dist x y ≤ a := by
  obtain ⟨T, hT, hs⟩ := h
  have hd := x.dist_le_switch y hT hs
  rw [hx, hy, abs_sub_comm T H] at hd
  linarith [hhalf T hT]

/-- Lengths realized by words with no repeated column. -/
def simpleLengths (x y : M.Point J root) : Set ℝ :=
  ⋃ w : (M.activeGraph J).Path x.column y.column,
    Set.range (fun s : M.Schedule J w.val => s.toPath.length x.height y.height)

lemma mem_simpleLengths (x y : M.Point J root) (p : M.Path J x.column y.column)
    (hp : p.word.IsPath) : p.length x.height y.height ∈ x.simpleLengths y := by
  apply Set.mem_iUnion.mpr
  refine ⟨⟨p.word, hp⟩, ?_⟩
  exact ⟨Schedule.ofPath p, by simp only [Schedule.toPath_ofPath]⟩

lemma simpleLengths_nonempty (x y : M.Point J root) : (x.simpleLengths y).Nonempty := by
  obtain ⟨p⟩ := x.paths_nonempty y
  obtain ⟨q, hq, _⟩ := p.simple_replacement x.height y.height
  exact ⟨q.length x.height y.height, x.mem_simpleLengths y q hq⟩

lemma isCompact_simpleLengths (hJ : IsClosed J) (x y : M.Point J root) :
    IsCompact (x.simpleLengths y) := by
  classical
  apply isCompact_iUnion
  intro w
  let := Schedule.compactSpace hJ w.val
  exact isCompact_range (Schedule.continuous_length w.val _ _ id
    continuous_const continuous_const continuous_id)

/-- Geometry, `geo:geodesics`: finite intrinsic distances are attained by a
switching path with no repeated column. Compactness is required of the actual
switch-height sets, rather than of an artificial discretization. -/
lemma exists_shortest (hJ : IsClosed J) (x y : M.Point J root) :
    ∃ p : M.Path J x.column y.column,
      p.word.IsPath ∧ p.length x.height y.height = dist x y := by
  have hc := x.isCompact_simpleLengths hJ y
  have hm := hc.isLeast_sInf (x.simpleLengths_nonempty y)
  obtain ⟨w, s, hs⟩ := Set.mem_iUnion.mp hm.1
  change s.toPath.length x.height y.height = sInf (x.simpleLengths y) at hs
  refine ⟨s.toPath, ?_, ?_⟩
  · rw [Schedule.word_toPath]
    exact w.property
  · apply le_antisymm _ (x.distance_le y s.toPath)
    have := x.paths_nonempty y
    apply le_ciInf
    intro p
    obtain ⟨q, hq, hlen⟩ := p.simple_replacement x.height y.height
    rw [hs]
    exact (hm.2 (x.mem_simpleLengths y q hq)).trans hlen

/-- Two short paths whose projected words meet on a column give a short
connection, with only one band-width paid for the vertical transfer. -/
lemma dist_le_of_shared_column (x y : M.Point J root) {i j v : Fin n}
    (p : M.Path J x.column i) (q : M.Path J y.column j)
    {H T a : ℝ} (hH : H ∈ J) (hT : T ∈ J)
    (hwidth : ∀ r ∈ J, ∀ s ∈ J, |r - s| ≤ a)
    (hpv : v ∈ p.word.support) (hqv : v ∈ q.word.support) :
    dist x y ≤ p.length x.height H + q.length y.height T + a := by
  obtain ⟨A, hA, p₁, p₂, hp⟩ := p.split_at_column x.inBand hH hpv
  obtain ⟨B, hB, q₁, q₂, hq⟩ := q.split_at_column y.inBand hT hqv
  have hd := x.distance_le y (p₁.append q₁.reverse)
  have ha := p₁.length_append_le q₁.reverse x.height B y.height
  have he := p₁.length_end_le x.height A B
  rw [q₁.length_reverse] at ha
  have hw := hwidth A hA B hB
  have hn₁ := p₂.length_nonneg A H
  have hn₂ := q₂.length_nonneg B T
  change x.distance y ≤ _
  linarith

/-- The source's quotient identifies precisely finite chains of switches at a
single height. This verifies that metric separation has not introduced any
extra quotient relations. -/
lemma zero_distance_iff (hJ : IsClosed J) (x y : M.Point J root) :
    dist x y = 0 ↔ x.height = y.height ∧
      (M.activeGraph {x.height}).Reachable x.column y.column := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
    exact p.zero_length_identifies _ _ (hp.trans h)
  · rintro ⟨hxy, ⟨w⟩⟩
    obtain ⟨p, hp⟩ := Path.exists_zero_path x.height x.inBand w
    apply le_antisymm _ dist_nonneg
    have h := x.distance_le y p
    rwa [← hxy, hp] at h

/-- Exact shortest paths to a fixed-height column stay in its distance
sublevel after projection to column indices. This is the metric assertion
underlying `geo:sublevel`, not merely a graph-connectivity assumption. -/
lemma shortest_sublevel (hJ : IsClosed J) (o y : M.Point J root) :
    ∃ p : M.Path J o.column y.column,
      p.length o.height y.height = dist o y ∧
      ∀ v ∈ p.word.support, ∃ hv : (M.activeGraph J).Reachable root v,
        dist o (⟨v, y.height, y.inBand, hv⟩ : M.Point J root) ≤ dist o y := by
  obtain ⟨p, _, hp⟩ := o.exists_shortest hJ y
  refine ⟨p, hp, ?_⟩
  intro v hv
  obtain ⟨H, _, q, r, hqr⟩ := p.split_at_column o.inBand y.inBand hv
  refine ⟨o.reachable.trans q.word.reachable, ?_⟩
  let z : M.Point J root := ⟨v, y.height, y.inBand, o.reachable.trans q.word.reachable⟩
  have h1 := o.distance_le z q
  have h2 := q.length_end_le o.height H y.height
  have h3 := r.height_change_le H y.height
  change o.distance z ≤ dist o y
  linarith

/-- The fixed-height radial sublevel in the active column graph. Columns
outside the chosen component are absent, as for the source's value `+∞`. -/
def sublevel (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) : Set (Fin n) :=
  {i | ∃ hi : (M.activeGraph J).Reachable root i,
    dist o (⟨i, H, hH, hi⟩ : M.Point J root) ≤ t}

lemma mem_sublevel_iff (o x : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) :
    x.column ∈ o.sublevel H hH t ↔ dist o (x.withHeight H hH) ≤ t := by
  constructor
  · rintro ⟨_, hd⟩
    exact hd
  · intro hd
    exact ⟨x.reachable, hd⟩

lemma sublevel_preconnected (hJ : IsClosed J) (o : M.Point J root)
    (H : ℝ) (hH : H ∈ J) (t : ℝ) :
    ((M.activeGraph J).induce (o.sublevel H hH t)).Preconnected := by
  intro x y
  obtain ⟨hx, hdx⟩ := x.property
  obtain ⟨hy, hdy⟩ := y.property
  obtain ⟨p, _, hp⟩ := o.shortest_sublevel hJ ⟨x.val, H, hH, hx⟩
  obtain ⟨q, _, hq⟩ := o.shortest_sublevel hJ ⟨y.val, H, hH, hy⟩
  have hmem : ∀ v ∈ (p.word.reverse.append q.word).support,
      v ∈ o.sublevel H hH t := by
    intro v hv
    rcases (p.word.reverse.mem_support_append_iff q.word).mp hv with hv | hv
    · have hv' : v ∈ p.word.support := by simpa using hv
      obtain ⟨hvr, hdv⟩ := hp v hv'
      exact ⟨hvr, hdv.trans hdx⟩
    · obtain ⟨hvr, hdv⟩ := hq v hv
      exact ⟨hvr, hdv.trans hdy⟩
  exact ⟨(p.word.reverse.append q.word).induce _ hmem⟩

/-- Geometry, Lemma `geo:sublevel`, including the actual nonemptiness
hypothesis and connectivity in the induced graph, not merely in the ambient
component. -/
lemma sublevel_connected (hJ : IsClosed J) (o : M.Point J root)
    (H : ℝ) (hH : H ∈ J) (t : ℝ) (hne : (o.sublevel H hH t).Nonempty) :
    ((M.activeGraph J).induce (o.sublevel H hH t)).Connected := by
  have : Nonempty (o.sublevel H hH t) := hne.to_subtype
  exact ⟨o.sublevel_preconnected hJ H hH t⟩

/-- The short connector in the portal argument. We use the connected
fixed-height sublevel at `t - 12a`; this changes the source's intermediate
13a estimate to 14a, still strictly below the required 100a separation. -/
lemma short_connector (hJ : IsClosed J) (o x : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a) (ht : 30 * a ≤ t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (hx : t ≤ dist o (x.withHeight H hH)) (hnear : dist o x < t + a) :
    ∃ v ∈ o.sublevel H hH (t - 12 * a), ∃ T ∈ J,
      ∃ p : M.Path J x.column v, p.length x.height T ≤ 14 * a := by
  let S := o.sublevel H hH (t - 12 * a)
  have hxo : x.column ∉ S := by
    intro h
    have hd := (o.mem_sublevel_iff x H hH (t - 12 * a)).mp h
    linarith
  have hoo : o.column ∈ S := by
    apply (o.mem_sublevel_iff o H hH (t - 12 * a)).mpr
    rw [o.dist_withHeight, abs_sub_comm]
    linarith [hhalf o.height o.inBand]
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ o
  obtain ⟨u, v, T, hT, hs, hu, hv, q, r, hqr⟩ :=
    p.crosses_set S hxo hoo x.height o.height
  let z : M.Point J root := ⟨u, T, hT, x.reachable.trans q.word.reachable⟩
  have hout : t - 12 * a < dist o (z.withHeight H hH) := by
    apply lt_of_not_ge
    intro h
    exact hu ((o.mem_sublevel_iff z H hH _).mpr h)
  have hz : dist o z ≤ r.length T o.height := by
    have hh := z.distance_le o (.cons T hT hs r)
    rw [dist_comm o z]
    change z.distance o ≤ r.length T o.height
    simpa only [Path.length, z, sub_self, abs_zero, zero_add] using hh
  have hvshift : dist z (z.withHeight H hH) ≤ a / 2 := by
    rw [z.dist_withHeight]
    change |T - H| ≤ a / 2
    rw [abs_sub_comm]
    exact hhalf T hT
  have htri := dist_triangle o z (z.withHeight H hH)
  have hlen : q.length x.height T ≤ 14 * a := by
    rw [hp, dist_comm x o] at hqr
    linarith
  refine ⟨v, hv, T, hT, q.snoc T hT hs, ?_⟩
  simpa only [Path.length_snoc, sub_self, abs_zero, add_zero] using hlen

/-- Quantitative exclusion behind the two-portals lemma: three entrance-range
midpoints in a connected high set cannot be mutually more than 100 widths
apart. No minor-exclusion or short-connector hypothesis is assumed. -/
lemma no_three_far_entrances (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    {C : Set (Fin n)} (hC : ((M.activeGraph J).induce C).Preconnected)
    (hhigh : ∀ z : M.Point J root, z.column ∈ C → t ≤ dist o (z.withHeight H hH))
    (x : Fin 3 → M.Point J root) (hxc : ∀ i, (x i).column ∈ C)
    (hnear : ∀ i, dist o (x i) < t + a)
    (hfar : Pairwise (fun i j => 100 * a < dist (x i) (x j))) : False := by
  by_cases ht : 30 * a ≤ t
  · let L := o.sublevel H hH (t - 12 * a)
    have hCL : Disjoint C L := by
      apply Set.disjoint_left.mpr
      rintro v hv ⟨hr, hd⟩
      let z : M.Point J root := ⟨v, H, hH, hr⟩
      have hz := hhigh z hv
      change t ≤ dist o z at hz
      linarith
    have hno : ∀ u ∈ C, ∀ v ∈ L, ¬ (M.activeGraph J).Adj u v := by
      rintro u hu v ⟨hr, hd⟩ huv
      let y : M.Point J root := ⟨v, H, hH, hr⟩
      let z : M.Point J root := ⟨u, H, hH,
        hr.trans (SimpleGraph.Adj.reachable huv.symm)⟩
      have hz := hhigh z hu
      change t ≤ dist o z at hz
      have hzy := z.dist_midpoints_le y rfl rfl hhalf huv
      have hh := dist_triangle o y z
      rw [dist_comm y z] at hh
      change dist o y ≤ t - 12 * a at hd
      linarith
    have hcon := fun i => o.short_connector hJ (x i) hH ha ht hhalf
      (hhigh (x i) (hxc i)) (hnear i)
    choose v hv T hT p hp using hcon
    have hwidth : ∀ r ∈ J, ∀ s ∈ J, |r - s| ≤ a := by
      intro r hr s hs
      have hb := abs_sub_le r H s
      rw [abs_sub_comm r H] at hb
      linarith [hhalf r hr, hhalf s hs]
    have hdis : Pairwise (fun i j => Disjoint
        {w | w ∈ (p i).word.support} {w | w ∈ (p j).word.support}) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro w hwi hwj
      have hd := (x i).dist_le_of_shared_column (x j) (p i) (p j)
        (hT i) (hT j) hwidth hwi hwj
      have hf := hfar hij
      linarith [hp i, hp j]
    exact ColumnOrder.no_three_connectors (M.active_noncrossing J) hC
      (o.sublevel_preconnected hJ H hH (t - 12 * a)) hCL hno
      (fun i => (x i).column) v hxc hv (fun i => (p i).word) hdis
  · have hf := hfar (show (0 : Fin 3) ≠ 1 by decide)
    have hd := dist_triangle (x 0) o (x 1)
    rw [dist_comm (x 0) o] at hd
    linarith [hnear 0, hnear 1]

/-- Two entrances cover all entrance midpoints. The two chosen values may
coincide, representing the one-portal case; both are actual entrances. -/
lemma two_portal_midpoints (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    {C : Set (Fin n)} (hC : ((M.activeGraph J).induce C).Preconnected)
    (hhigh : ∀ z : M.Point J root, z.column ∈ C → t ≤ dist o (z.withHeight H hH))
    {E : Set (M.Point J root)} (hne : E.Nonempty)
    (heC : ∀ x ∈ E, x.column ∈ C) (hnear : ∀ x ∈ E, dist o x < t + a) :
    ∃ p ∈ E, ∃ q ∈ E, ∀ x ∈ E, dist x p ≤ 100 * a ∨ dist x q ≤ 100 * a := by
  classical
  obtain ⟨p, hp⟩ := hne
  by_cases hex : ∃ q ∈ E, 100 * a < dist p q
  · obtain ⟨q, hq, hpq⟩ := hex
    refine ⟨p, hp, q, hq, ?_⟩
    intro z hz
    by_contra h
    push Not at h
    apply o.no_three_far_entrances hJ hH ha hhalf hC hhigh ![p, q, z]
    · intro i
      fin_cases i
      · exact heC p hp
      · exact heC q hq
      · exact heC z hz
    · intro i
      fin_cases i
      · exact hnear p hp
      · exact hnear q hq
      · exact hnear z hz
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [dist_comm]
  · refine ⟨p, hp, p, hp, ?_⟩
    intro x hx
    left
    rw [dist_comm]
    exact le_of_not_gt (fun h => hex ⟨x, hx, h⟩)

/-- Geometry `geo:portals`, the full-column covering conclusion with the
stated 200a constant. The entrance-range hypothesis is derived from adjacency
by `dist_midpoints_le`; the two portal centers are selected from `E` itself. -/
lemma two_portals (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    {C : Set (Fin n)} (hC : ((M.activeGraph J).induce C).Preconnected)
    (hhigh : ∀ z : M.Point J root, z.column ∈ C → t ≤ dist o (z.withHeight H hH))
    {E : Set (M.Point J root)} (hne : E.Nonempty)
    (heC : ∀ x ∈ E, x.column ∈ C) (hnear : ∀ x ∈ E, dist o x < t + a) :
    ∃ p ∈ E, ∃ q ∈ E, ∀ x : M.Point J root, x.withHeight H hH ∈ E →
      dist x p ≤ 200 * a ∨ dist x q ≤ 200 * a := by
  obtain ⟨p, hp, q, hq, hcover⟩ := o.two_portal_midpoints hJ hH ha hhalf hC hhigh
    hne heC hnear
  refine ⟨p, hp, q, hq, ?_⟩
  intro x hx
  have hv : dist x (x.withHeight H hH) ≤ a / 2 := by
    rw [x.dist_withHeight, abs_sub_comm]
    exact hhalf x.height x.inBand
  rcases hcover _ hx with h | h
  · left
    linarith [dist_triangle x (x.withHeight H hH) p]
  · right
    linarith [dist_triangle x (x.withHeight H hH) q]

/-- Radial superlevels contain exactly the reachable columns whose midpoints
have radial value at least the threshold. -/
def superlevel (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) : Set (Fin n) :=
  {i | ∃ hi : (M.activeGraph J).Reachable root i,
    t ≤ dist o (⟨i, H, hH, hi⟩ : M.Point J root)}

lemma mem_superlevel_iff (o x : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ) :
    x.column ∈ o.superlevel H hH t ↔ t ≤ dist o (x.withHeight H hH) := by
  constructor
  · rintro ⟨_, hd⟩
    exact hd
  · intro hd
    exact ⟨x.reachable, hd⟩

/-- The actual entrance midpoints of a radial high component. The adjacent
low column, rather than a separate entrance-range hypothesis, is part of the
definition. -/
def entrances (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (t : ℝ)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    Set (M.Point J root) :=
  {x | x.height = H ∧ x.column ∈ ColumnOrder.componentColumns C ∧
    ∃ y : M.Point J root, y.height = H ∧
      (M.activeGraph J).Adj x.column y.column ∧ dist o y < t}

lemma entrance_radial (o : M.Point J root) {H a t : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    {x : M.Point J root} (hx : x ∈ o.entrances H hH t C) :
    t ≤ dist o x ∧ dist o x < t + a := by
  obtain ⟨hxH, hxC, y, hyH, hxy, hy⟩ := hx
  have hhigh := (o.mem_superlevel_iff x H hH t).mp
    (ColumnOrder.componentColumns_subset C hxC)
  have heq : x.withHeight H hH = x := by
    simpa only [← hxH] using x.withHeight_self
  rw [heq] at hhigh
  have hd := x.dist_midpoints_le y hxH hyH hhalf hxy
  have htri := dist_triangle o y x
  rw [dist_comm y x] at htri
  exact ⟨hhigh, by linarith⟩

/-- Exit a high component along an attained shortest path. The final high
column is an actual entrance. The estimate retains the distance to the radial
threshold, and is the geometric input for both cell diameters and portal levels. -/
lemma exit_superlevel (hJ : IsClosed J) (o x : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ht : a / 2 < t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C) :
    ∃ z : M.Point J root, z.withHeight H hH ∈ o.entrances H hH t C ∧
      dist x z ≤ dist o x - t + a / 2 := by
  let S := ColumnOrder.componentColumns C
  have hoo : o.column ∉ S := by
    intro ho
    have hh := (o.mem_superlevel_iff o H hH t).mp
      (ColumnOrder.componentColumns_subset C ho)
    rw [o.dist_withHeight, abs_sub_comm] at hh
    linarith [hhalf o.height o.inBand]
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ o
  obtain ⟨u, v, T, hT, hs, hu, hv, q, r, hqr⟩ :=
    p.crosses_set Sᶜ (by simpa only [Set.mem_compl_iff, not_not] using hx)
      hoo x.height o.height
  have huC : u ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hu
  have huv : (M.activeGraph J).Adj u v := ⟨T, hT, hs⟩
  let z : M.Point J root := ⟨u, T, hT, x.reachable.trans q.word.reachable⟩
  let y : M.Point J root := ⟨v, H, hH, z.reachable.trans huv.reachable⟩
  have hy : dist o y < t := by
    apply lt_of_not_ge
    intro h
    exact hv (ColumnOrder.componentColumns_adj C huC huv ⟨y.reachable, h⟩)
  have hentrance : z.withHeight H hH ∈ o.entrances H hH t C :=
    ⟨rfl, huC, y, rfl, huv, hy⟩
  refine ⟨z, hentrance, ?_⟩
  have hhigh := (o.mem_superlevel_iff z H hH t).mp
    (ColumnOrder.componentColumns_subset C huC)
  have hvshift : dist z (z.withHeight H hH) ≤ a / 2 := by
    rw [z.dist_withHeight, abs_sub_comm]
    exact hhalf T hT
  have hz : dist o z ≤ r.length T o.height := by
    have hh := z.distance_le o (.cons T hT hs r)
    rw [dist_comm o z]
    change z.distance o ≤ r.length T o.height
    simpa only [Path.length, z, sub_self, abs_zero, zero_add] using hh
  have htri := dist_triangle o z (z.withHeight H hH)
  have hdx := x.distance_le z q
  change dist x z ≤ q.length x.height T at hdx
  rw [hp, dist_comm x o] at hqr
  linarith

/-- Nonempty radial high components have entrances above the initial
half-width. This discharges the existence clause of `geo:portals`. -/
lemma entrances_nonempty (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ht : a / 2 < t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    (o.entrances H hH t C).Nonempty := by
  obtain ⟨i, hi⟩ := C.nonempty_supp
  obtain ⟨hr, _⟩ := i.property
  let x : M.Point J root := ⟨i.val, H, hH, hr⟩
  obtain ⟨z, hz, _⟩ := o.exit_superlevel hJ x hH ht hhalf C ⟨i, hi, rfl⟩
  exact ⟨z.withHeight H hH, hz⟩

/-- Geometry `geo:portals` with the actual radial component and actual
entrances. In particular no covering or radial-range conclusion is assumed. -/
lemma component_two_portals (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hne : (o.entrances H hH t C).Nonempty) :
    ∃ p ∈ o.entrances H hH t C, ∃ q ∈ o.entrances H hH t C,
      (t ≤ dist o p ∧ dist o p < t + a) ∧
      (t ≤ dist o q ∧ dist o q < t + a) ∧
      ∀ x : M.Point J root, x.withHeight H hH ∈ o.entrances H hH t C →
        dist x p ≤ 200 * a ∨ dist x q ≤ 200 * a := by
  obtain ⟨p, hp, q, hq, hcover⟩ := o.two_portals hJ hH ha hhalf
    (ColumnOrder.componentColumns_connected C).preconnected
    (fun z hz => (o.mem_superlevel_iff z H hH t).mp
      (ColumnOrder.componentColumns_subset C hz)) hne
    (fun _ hx => hx.2.1) (fun _ hx => (o.entrance_radial hH hhalf C hx).2)
  exact ⟨p, hp, q, hq, o.entrance_radial hH hhalf C hp,
    o.entrance_radial hH hhalf C hq, hcover⟩

/-- The geodesic-to-root estimate behind radial cells: every point of a
high component whose radial distance is bounded is close to a chosen portal. -/
lemma component_portal_cover (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a) (ht : a / 2 < t)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    ∃ p ∈ o.entrances H hH t C, ∃ q ∈ o.entrances H hH t C,
      ∀ x : M.Point J root, x.column ∈ ColumnOrder.componentColumns C →
        dist x p ≤ dist o x - t + 201 * a ∨
        dist x q ≤ dist o x - t + 201 * a := by
  obtain ⟨p, hp, q, hq, _, _, hc⟩ := o.component_two_portals hJ hH ha hhalf C
    (o.entrances_nonempty hJ hH ht hhalf C)
  refine ⟨p, hp, q, hq, ?_⟩
  intro x hx
  obtain ⟨z, hz, hd⟩ := o.exit_superlevel hJ x hH ht hhalf C hx
  rcases hc z hz with hz | hz
  · left
    linarith [dist_triangle x z p]
  · right
    linarith [dist_triangle x z q]

/-- The half-open radial layer of the source. Its connected components,
not components of the ambient graph, are the cell column sets. -/
def layer (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (q D : ℝ) : Set (Fin n) :=
  {i | ∃ hi : (M.activeGraph J).Reachable root i,
    q ≤ dist o (⟨i, H, hH, hi⟩ : M.Point J root) ∧
    dist o (⟨i, H, hH, hi⟩ : M.Point J root) < q + D}

lemma layer_subset_superlevel (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (q D : ℝ) :
    o.layer H hH q D ⊆ o.superlevel H hH q := by
  rintro i ⟨hr, hlow, _⟩
  exact ⟨hr, hlow⟩

lemma mem_layer_iff (o x : M.Point J root) (H : ℝ) (hH : H ∈ J) (q D : ℝ) :
    x.column ∈ o.layer H hH q D ↔
      q ≤ dist o (x.withHeight H hH) ∧ dist o (x.withHeight H hH) < q + D := by
  constructor
  · rintro ⟨_, hd⟩
    exact hd
  · intro hd
    exact ⟨x.reachable, hd⟩

/-- The weak-diameter assertion of `geo:cells` for the literal full-column
cell. Paths measuring distance may leave the cell, exactly as in the source. -/
lemma radial_cell_diameter (hJ : IsClosed J) (o : M.Point J root)
    {H a q D : ℝ} (hH : H ∈ J) (ha : 0 < a) (hthin : a ≤ D / 1000)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (x y : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hy : y.column ∈ ColumnOrder.componentColumns C) : dist x y ≤ 10 * D := by
  classical
  have hD : 0 < D := by linarith
  have hup : ∀ z : M.Point J root, z.column ∈ ColumnOrder.componentColumns C →
      dist o z < q + D + a / 2 := by
    intro z hz
    have hr := (o.mem_layer_iff z H hH q D).mp
      (ColumnOrder.componentColumns_subset C hz)
    have hv := hhalf z.height z.inBand
    have hd := dist_triangle o (z.withHeight H hH) z
    rw [dist_comm (z.withHeight H hH) z, z.dist_withHeight, abs_sub_comm] at hd
    linarith [hr.2]
  by_cases hq : q ≤ 30 * a
  · have hd := dist_triangle x o y
    rw [dist_comm x o] at hd
    linarith [hup x hx, hup y hy]
  · let Cplus := ColumnOrder.componentAbove (o.layer_subset_superlevel H hH q D) C
    have hsub := ColumnOrder.componentColumns_above (o.layer_subset_superlevel H hH q D) C
    have ht : a / 2 < q := by linarith
    obtain ⟨p, _, r, _, hc⟩ := o.component_portal_cover hJ hH ha ht hhalf Cplus
    let f : ColumnOrder.componentColumns C → M.Point J root := fun i =>
      ⟨i.val, H, hH, (ColumnOrder.componentColumns_subset C i.property).choose⟩
    have hedge : ∀ i j, ((M.activeGraph J).induce (ColumnOrder.componentColumns C)).Adj i j →
        dist (f i) (f j) ≤ a := by
      intro i j hij
      exact (f i).dist_midpoints_le (f j) rfl rfl hhalf hij
    have hcover : ∀ i, dist (f i) p ≤ D + 210 * a ∨ dist (f i) r ≤ D + 210 * a := by
      intro i
      have hfi : (f i).column ∈ ColumnOrder.componentColumns C := i.property
      have hu := hup (f i) hfi
      rcases hc (f i) (hsub hfi) with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    have hd := ColumnOrder.connected_two_balls
      (ColumnOrder.componentColumns_connected C).preconnected f p r
      (show 0 ≤ D + 210 * a by positivity) ha.le hedge hcover ⟨x.column, hx⟩ ⟨y.column, hy⟩
    have hvx : dist x (f ⟨x.column, hx⟩) ≤ a / 2 := by
      change dist x (x.withHeight H hH) ≤ a / 2
      rw [x.dist_withHeight, abs_sub_comm]
      exact hhalf x.height x.inBand
    have hvy : dist (f ⟨y.column, hy⟩) y ≤ a / 2 := by
      change dist (y.withHeight H hH) y ≤ a / 2
      rw [dist_comm, y.dist_withHeight, abs_sub_comm]
      exact hhalf y.height y.inBand
    have ht₁ := dist_triangle x (f ⟨x.column, hx⟩) y
    have ht₂ := dist_triangle (f ⟨x.column, hx⟩) (f ⟨y.column, hy⟩) y
    linarith

/-- Changing to the fixed midheight costs at most one band width in any
radial comparison. This also controls all zero-distance representatives. -/
lemma radial_difference_le (o x y : M.Point J root) {H a : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) :
    |dist o (x.withHeight H hH) - dist o (y.withHeight H hH)| ≤ dist x y + a := by
  have hx : dist x (x.withHeight H hH) ≤ a / 2 := by
    rw [x.dist_withHeight, abs_sub_comm]
    exact hhalf x.height x.inBand
  have hy : dist y (y.withHeight H hH) ≤ a / 2 := by
    rw [y.dist_withHeight, abs_sub_comm]
    exact hhalf y.height y.inBand
  have h₁ := abs_dist_sub_le (x.withHeight H hH) (y.withHeight H hH) o
  rw [dist_comm (x.withHeight H hH) o, dist_comm (y.withHeight H hH) o] at h₁
  have h₂ := dist_triangle (x.withHeight H hH) x (y.withHeight H hH)
  have h₃ := dist_triangle x y (y.withHeight H hH)
  rw [dist_comm (x.withHeight H hH) x] at h₂
  linarith

/-- A column visited by a short switching path has a nearby radial midpoint.
The conclusion uses the actual path prefix, rather than a shortest path
constrained to a radial cell. -/
lemma path_radial_bound (o x y : M.Point J root) {H a : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (p : M.Path J x.column y.column)
    {i : Fin n} (hi : i ∈ p.word.support) :
    ∃ hr : (M.activeGraph J).Reachable root i,
      |dist o (⟨i, H, hH, hr⟩ : M.Point J root) - dist o (x.withHeight H hH)| ≤
        p.length x.height y.height + a := by
  obtain ⟨T, hT, q, r, hqr⟩ := p.split_at_column x.inBand y.inBand hi
  let z : M.Point J root := ⟨i, T, hT, x.reachable.trans q.word.reachable⟩
  have hd : dist x z ≤ p.length x.height y.height := by
    have hq := x.distance_le z q
    have hr := r.length_nonneg T y.height
    change dist x z ≤ q.length x.height T at hq
    linarith
  refine ⟨z.reachable, ?_⟩
  have hb := o.radial_difference_le z x hH hhalf
  rw [dist_comm z x] at hb
  change |dist o (z.withHeight H hH) - dist o (x.withHeight H hH)| ≤ _
  linarith

/-- Deterministic padding in one actual radial layer. All representatives of
all endpoints are covered because the lemma is stated on the pseudometric
space of representatives. -/
lemma radial_cell_padding (o x y : M.Point J root) {H a q D ρ : ℝ}
    (hH : H ∈ J) (ha : 0 ≤ a) (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hlow : q + ρ + 2 * a < dist o (x.withHeight H hH))
    (hupp : dist o (x.withHeight H hH) < q + D - ρ - 2 * a)
    (p : M.Path J x.column y.column) (hp : p.length x.height y.height ≤ ρ) :
    y.column ∈ ColumnOrder.componentColumns C := by
  apply ColumnOrder.componentColumns_of_walk C p.word hx
  intro i hi
  obtain ⟨hr, hb⟩ := o.path_radial_bound x y hH hhalf p hi
  obtain ⟨h₁, h₂⟩ := abs_le.mp hb
  refine ⟨hr, ?_, ?_⟩ <;> linarith

lemma radial_ball_padding (hJ : IsClosed J) (o x y : M.Point J root)
    {H a q D ρ : ℝ} (hH : H ∈ J) (ha : 0 ≤ a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hlow : q + ρ + 2 * a < dist o (x.withHeight H hH))
    (hupp : dist o (x.withHeight H hH) < q + D - ρ - 2 * a)
    (hxy : dist x y ≤ ρ) : y.column ∈ ColumnOrder.componentColumns C := by
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  exact o.radial_cell_padding x y hH ha hhalf C hx hlow hupp p (hp ▸ hxy)

/-- The literal full-column frontier of a column cell in the active graph. -/
def frontier (C : Set (Fin n)) : Set (Fin n) :=
  {i | i ∈ C ∧ ∃ j, (M.activeGraph J).Adj i j ∧ j ∉ C}

/-- A frontier midpoint is within one width of a layer threshold. The
neighbor cannot be in the same layer, since the cell is a component there. -/
lemma frontier_radial (o z : M.Point J root) {H a q D : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hz : z.column ∈ frontier (M := M) (J := J) (ColumnOrder.componentColumns C)) :
    dist o (z.withHeight H hH) < q + a ∨
      q + D - a ≤ dist o (z.withHeight H hH) := by
  obtain ⟨hzc, j, hzj, hj⟩ := hz
  let w : M.Point J root := ⟨j, H, hH, z.reachable.trans hzj.reachable⟩
  have hnot : j ∉ o.layer H hH q D := by
    intro h
    exact hj (ColumnOrder.componentColumns_adj C hzc hzj h)
  have hd : dist (z.withHeight H hH) w ≤ a :=
    (z.withHeight H hH).dist_midpoints_le w rfl rfl hhalf hzj
  have hw : ¬ (q ≤ dist o w ∧ dist o w < q + D) := by
    intro h
    exact hnot ⟨w.reachable, h⟩
  have ht₁ := dist_triangle o (z.withHeight H hH) w
  have ht₂ := dist_triangle o w (z.withHeight H hH)
  rw [dist_comm w (z.withHeight H hH)] at ht₂
  by_cases hq : dist o w < q
  · exact Or.inl (by linarith)
  · exact Or.inr (by have h := not_lt.mp hq; have h' : q + D ≤ dist o w :=
                         le_of_not_gt (fun hu => hw ⟨h, hu⟩); linarith)

/-- Exact strict avoidance of the frontier, the second assertion of
`geo:padding`. The empty-frontier case is automatic, not assigned distance 0. -/
lemma radial_frontier_distance (o x z : M.Point J root) {H a q D ρ : ℝ}
    (hH : H ∈ J) (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.layer H hH q D)).ConnectedComponent)
    (hlow : q + ρ + 2 * a < dist o (x.withHeight H hH))
    (hupp : dist o (x.withHeight H hH) < q + D - ρ - 2 * a)
    (hz : z.column ∈ frontier (M := M) (J := J) (ColumnOrder.componentColumns C)) :
    ρ < dist x z := by
  obtain h | h := o.frontier_radial z hH hhalf C hz
  · have hb := (abs_le.mp (o.radial_difference_le x z hH hhalf)).2
    linarith
  · have hb := (abs_le.mp (o.radial_difference_le x z hH hhalf)).1
    linarith


/-- Every fixed column is an isometric copy of its allowed height interval. -/
def columnMap (i : Fin n) (hi : (M.activeGraph J).Reachable root i) : J → M.Point J root :=
  fun H => ⟨i, H.val, H.property, hi⟩

lemma columnMap_isometry (i : Fin n) (hi : (M.activeGraph J).Reachable root i) :
    Isometry (columnMap i hi) := by
  apply Isometry.of_dist_eq
  intro H T
  exact (columnMap i hi H).dist_same_column (columnMap i hi T) rfl

/-- Compactness of any full-column subset in a compact band, including the
literal radial cells and their frontiers. This argument works before taking
the separation quotient and does not require a false Hausdorff assumption. -/
lemma fullColumns_compact (hJ : IsCompact J) (C : Set (Fin n)) :
    IsCompact {x : M.Point J root | x.column ∈ C} := by
  classical
  let : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  let I := {i : Fin n // i ∈ C ∧ (M.activeGraph J).Reachable root i}
  have heq : {x : M.Point J root | x.column ∈ C} =
      ⋃ i : I, Set.range (columnMap i.val i.property.2) := by
    ext x
    constructor
    · intro hx
      refine Set.mem_iUnion.mpr ⟨⟨x.column, hx, x.reachable⟩, ?_⟩
      exact ⟨⟨x.height, x.inBand⟩, rfl⟩
    · intro hx
      obtain ⟨i, H, rfl⟩ := Set.mem_iUnion.mp hx
      exact i.property.1
  rw [heq]
  exact isCompact_iUnion (fun i => isCompact_range (columnMap_isometry i.val i.property.2).continuous)

/-- A continuous scalar frontier constraint attains its infimum whenever
there is a frontier point. Used by the main raise-or-descend test. -/
lemma frontier_minimizer (hJ : IsCompact J) (C : Set (Fin n))
    (s : M.Point J root → ℝ) (hs : Continuous s) (x : M.Point J root) (c : ℝ)
    (hne : ∃ z : M.Point J root, z.column ∈ frontier (M := M) (J := J) C) :
    ∃ z : M.Point J root, z.column ∈ frontier (M := M) (J := J) C ∧
      ∀ w : M.Point J root, w.column ∈ frontier (M := M) (J := J) C →
        s z + c * dist x z ≤ s w + c * dist x w := by
  have hc := fullColumns_compact (M := M) (root := root) hJ
    (frontier (M := M) (J := J) C)
  have hf : Continuous (fun z : M.Point J root => s z + c * dist x z) :=
    hs.add (continuous_const.mul (continuous_const.dist continuous_id))
  obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn hne hf.continuousOn
  exact ⟨z, hz, hmin⟩


/-- The metric interpolation property of an actual attained shortest path.
This is the geodesic fact used by the small-ball and descending-path arguments. -/
lemma exists_between (hJ : IsClosed J) (hconv : Set.OrdConnected J)
    (x y : M.Point J root) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hlen : ℓ ≤ dist x y) :
    ∃ z : M.Point J root, dist x z = ℓ ∧ dist z y = dist x y - ℓ := by
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  obtain ⟨k, T, hT, q, r, hq, hr⟩ := p.split_at_length hconv x.inBand y.inBand hℓ
    (hp ▸ hlen)
  let z : M.Point J root := ⟨k, T, hT, x.reachable.trans q.word.reachable⟩
  have h₁ : dist x z ≤ ℓ := by
    have h := x.distance_le z q
    exact h.trans_eq hq
  have h₂ : dist z y ≤ dist x y - ℓ := by
    have h := z.distance_le y r
    exact h.trans_eq (hr.trans (by rw [hp]))
  have ht := dist_triangle x z y
  exact ⟨z, by linarith, by linarith⟩

/-- Every point on a shortest descending path retains the endpoint's deficit
bound. This is `main:ray-prefix`, expressed by exact arclength distances. -/
lemma descent_along_shortest {s : M.Point J root → ℝ} {ε : ℝ}
    (hs : ∀ u v, s u - s v ≤ dist u v) (x z v : M.Point J root)
    (hshort : dist x v + dist v z = dist x z)
    (hdrop : s z ≤ s x - dist x z + ε) :
    s v ≤ s x - dist x v + ε := by
  linarith [hs v z]


/-- All representatives of the intrinsic closed ball, projected to columns.
Using representatives includes columns identified by zero-length paths. -/
def ballColumns (x : M.Point J root) (ρ : ℝ) : Set (Fin n) :=
  {i | ∃ y : M.Point J root, y.column = i ∧ dist x y ≤ ρ}

lemma mem_ballColumns (x y : M.Point J root) {ρ : ℝ} (hy : dist x y ≤ ρ) :
    y.column ∈ x.ballColumns ρ := ⟨y, rfl, hy⟩

lemma path_ballColumns (x y : M.Point J root) (p : M.Path J x.column y.column)
    {ρ : ℝ} (hp : p.length x.height y.height ≤ ρ) :
    ∀ v ∈ p.word.support, v ∈ x.ballColumns ρ := by
  intro v hv
  obtain ⟨T, hT, q, r, hqr⟩ := p.split_at_column x.inBand y.inBand hv
  let z : M.Point J root := ⟨v, T, hT, x.reachable.trans q.word.reachable⟩
  refine ⟨z, rfl, ?_⟩
  have h := x.distance_le z q
  have hr := r.length_nonneg T y.height
  change dist x z ≤ q.length x.height T at h
  linarith

/-- The projection of an actual closed ball is induced-connected. This is
not an assumed graph property in the local interpolation argument. -/
lemma ballColumns_preconnected (hJ : IsClosed J) (x : M.Point J root) (ρ : ℝ) :
    ((M.activeGraph J).induce (x.ballColumns ρ)).Preconnected := by
  intro i j
  obtain ⟨y, hy, hxy⟩ := i.property
  obtain ⟨z, hz, hxz⟩ := j.property
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  obtain ⟨q, _, hq⟩ := x.exists_shortest hJ z
  have hm : ∀ v ∈ (p.word.reverse.append q.word).support,
      v ∈ x.ballColumns ρ := by
    intro v hv
    rcases (p.word.reverse.mem_support_append_iff q.word).mp hv with h | h
    · exact x.path_ballColumns y p (hp ▸ hxy) v (by simpa using h)
    · exact x.path_ballColumns z q (hq ▸ hxz) v h
  have hreach := (p.word.reverse.append q.word).induce _ hm
  exact ⟨hreach.copy (Subtype.ext hy) (Subtype.ext hz)⟩

lemma ballColumns_nonempty (x : M.Point J root) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (x.ballColumns ρ).Nonempty :=
  ⟨x.column, x.mem_ballColumns x (by simpa using hρ)⟩

/-- The sharper `2ρ+a` version of the source's `2ρ+2a` radial spread. -/
lemma ball_radial_spread (o x y z : M.Point J root) {H a ρ : ℝ} (hH : H ∈ J)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (hy : dist x y ≤ ρ) (hz : dist x z ≤ ρ) :
    |dist o (y.withHeight H hH) - dist o (z.withHeight H hH)| ≤ 2 * ρ + a := by
  have h := o.radial_difference_le y z hH hhalf
  have ht := dist_triangle y x z
  rw [dist_comm y x] at ht
  linarith

/-- A shortest path to any point outside a high component reaches an actual
entrance within its total length. Unlike `exit_superlevel`, no radial decrease
to the root is needed. -/
lemma exit_superlevel_to (hJ : IsClosed J) (o x y : M.Point J root)
    {H t : ℝ} (hH : H ∈ J)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hy : y.column ∉ ColumnOrder.componentColumns C) :
    ∃ z : M.Point J root, z.withHeight H hH ∈ o.entrances H hH t C ∧
      dist x z ≤ dist x y := by
  let S := ColumnOrder.componentColumns C
  obtain ⟨p, _, hp⟩ := x.exists_shortest hJ y
  obtain ⟨u, v, T, hT, hs, hu, hv, q, r, hqr⟩ :=
    p.crosses_set Sᶜ (by simpa only [Set.mem_compl_iff, not_not] using hx)
      hy x.height y.height
  have huC : u ∈ S := by simpa only [Set.mem_compl_iff, not_not] using hu
  have huv : (M.activeGraph J).Adj u v := ⟨T, hT, hs⟩
  let z : M.Point J root := ⟨u, T, hT, x.reachable.trans q.word.reachable⟩
  let w : M.Point J root := ⟨v, H, hH, z.reachable.trans huv.reachable⟩
  have hw : dist o w < t := by
    apply lt_of_not_ge
    intro h
    exact hv (ColumnOrder.componentColumns_adj C huC huv ⟨w.reachable, h⟩)
  refine ⟨z, ⟨rfl, huC, w, rfl, huv, hw⟩, ?_⟩
  have hdx := x.distance_le z q
  change dist x z ≤ q.length x.height T at hdx
  have hr := r.length_nonneg T y.height
  linarith

/-- Any point in a high component and within `L` of a point outside it is
within `L+200a` of one of its two fixed entrance portals. -/
lemma near_component_portal (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent)
    (hne : (o.entrances H hH t C).Nonempty) :
    ∃ p ∈ o.entrances H hH t C, ∃ q ∈ o.entrances H hH t C,
      ∀ x y : M.Point J root, x.column ∈ ColumnOrder.componentColumns C →
        y.column ∉ ColumnOrder.componentColumns C →
        dist x p ≤ dist x y + 200 * a ∨ dist x q ≤ dist x y + 200 * a := by
  obtain ⟨p, hp, q, hq, _, _, hc⟩ := o.component_two_portals hJ hH ha hhalf C hne
  refine ⟨p, hp, q, hq, ?_⟩
  intro x y hx hy
  obtain ⟨z, hz, hdist⟩ := o.exit_superlevel_to hJ x y hH C hx hy
  rcases hc z hz with h | h
  · exact Or.inl (by linarith [dist_triangle x z p])
  · exact Or.inr (by linarith [dist_triangle x z q])


/-- The fixed-height radial profile attains its minimum among the finite
set of columns represented in a nonempty closed ball. -/
lemma ball_radial_minimum (o x : M.Point J root) {H ρ : ℝ} (hH : H ∈ J)
    (hρ : 0 ≤ ρ) :
    ∃ y : M.Point J root, dist x y ≤ ρ ∧
      ∀ z : M.Point J root, dist x z ≤ ρ →
        dist o (y.withHeight H hH) ≤ dist o (z.withHeight H hH) := by
  let R := {i : Fin n // (M.activeGraph J).Reachable root i}
  let S : Set R := {i | i.val ∈ x.ballColumns ρ}
  let f : R → ℝ := fun i => dist o ⟨i.val, H, hH, i.property⟩
  have hne : S.Nonempty :=
    ⟨⟨x.column, x.reachable⟩, x.mem_ballColumns x (by simpa using hρ)⟩
  obtain ⟨i, hi, hmin⟩ := Set.exists_min_image S f (Set.toFinite _) hne
  obtain ⟨y, hy, hxy⟩ := hi
  refine ⟨y, hxy, ?_⟩
  intro z hz
  have heq : (⟨i.val, H, hH, i.property⟩ : M.Point J root) = y.withHeight H hH := by
    cases y
    simp_all only [withHeight]
  have h := hmin ⟨z.column, z.reachable⟩ (x.mem_ballColumns z hz)
  change dist o _ ≤ dist o (z.withHeight H hH) at h
  rwa [heq] at h

/-- The exact geometric content of the one-chain small-ball argument:
there are only two consecutive radial layer depths in a sufficiently small
ball, and all its representatives lie in one node at the lower depth. -/
lemma ball_two_layers (hJ : IsClosed J) (o x : M.Point J root)
    {H a ρ δ : ℝ} (hH : H ∈ J) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (hsmall : 2 * ρ + a < δ) :
    ∃ k : ℕ, ∃ y : M.Point J root,
      ∃ C : ((M.activeGraph J).induce (o.superlevel H hH (k * δ))).ConnectedComponent,
        dist x y ≤ ρ ∧ dist o (y.withHeight H hH) < (k + 1) * δ ∧
        (∀ z : M.Point J root, dist x z ≤ ρ →
          z.column ∈ ColumnOrder.componentColumns C ∧
          (k : ℝ) * δ ≤ dist o (z.withHeight H hH) ∧
          dist o (z.withHeight H hH) < (k + 2) * δ) := by
  obtain ⟨y, hy, hmin⟩ := o.ball_radial_minimum x hH hρ
  let b := dist o (y.withHeight H hH)
  let k := ⌊b / δ⌋₊
  have hb : 0 ≤ b / δ := div_nonneg dist_nonneg hδ.le
  have hlo : (k : ℝ) * δ ≤ b := (le_div_iff₀ hδ).mp (Nat.floor_le hb)
  have hhi : b < (k + 1) * δ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (b / δ))
  have hbound : ∀ z : M.Point J root, dist x z ≤ ρ →
      (k : ℝ) * δ ≤ dist o (z.withHeight H hH) ∧
        dist o (z.withHeight H hH) < (k + 2) * δ := by
    intro z hz
    have hminz := hmin z hz
    have hspread := o.ball_radial_spread x z y hH hhalf hz hy
    have hu := (abs_le.mp hspread).2
    constructor
    · exact hlo.trans hminz
    · dsimp [b] at hhi
      linarith
  have hsub : x.ballColumns ρ ⊆ o.superlevel H hH (k * δ) := by
    rintro _ ⟨z, rfl, hz⟩
    exact (o.mem_superlevel_iff z H hH (k * δ)).mpr (hbound z hz).1
  obtain ⟨C, hC⟩ := ColumnOrder.exists_component_containing
    (x.ballColumns_nonempty hρ) (x.ballColumns_preconnected hJ ρ) hsub
  exact ⟨k, y, C, hy, hhi, fun z hz => ⟨hC (x.mem_ballColumns z hz), hbound z hz⟩⟩


/-- At depth zero the single radial node contains every reachable column,
including the chosen basepoint column. -/
lemma mem_zero_component (o x : M.Point J root) {H : ℝ} (hH : H ∈ J)
    (C : ((M.activeGraph J).induce (o.superlevel H hH 0)).ConnectedComponent) :
    x.column ∈ ColumnOrder.componentColumns C := by
  classical
  obtain ⟨i, hi⟩ := C.nonempty_supp
  obtain ⟨hr, _⟩ := i.property
  obtain ⟨p⟩ := hr.symm.trans x.reachable
  apply ColumnOrder.componentColumns_of_walk C p ⟨i, hi, rfl⟩
  intro v hv
  exact ⟨hr.trans (p.takeUntil v hv).reachable, dist_nonneg⟩

/-- Two fixed geometric portals, with all bounds required by the actual
interpolation hierarchy. Repeated portals encode the one-portal case. -/
structure PortalData (o : M.Point J root) (H : ℝ) (hH : H ∈ J) (a t : ℝ)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) where
  left : M.Point J root
  right : M.Point J root
  left_height : left.height = H
  right_height : right.height = H
  left_mem : left.column ∈ ColumnOrder.componentColumns C
  right_mem : right.column ∈ ColumnOrder.componentColumns C
  left_radial : t ≤ dist o left ∧ dist o left < t + a
  right_radial : t ≤ dist o right ∧ dist o right < t + a
  cover : ∀ x : M.Point J root, x.column ∈ ColumnOrder.componentColumns C →
    min (dist x left) (dist x right) ≤ dist o x - t + 201 * a
  entrance_cover : ∀ x : M.Point J root,
    x.withHeight H hH ∈ o.entrances H hH t C →
      min (dist x left) (dist x right) ≤ 200 * a

/-- The portal data are constructed from the proved geometry, including the
root convention; they are not assumptions on the interpolation input. -/
lemma portalData_nonempty (hJ : IsClosed J) (o : M.Point J root)
    {H a t : ℝ} (hH : H ∈ J) (ho : o.height = H) (ha : 0 < a)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (ht : t = 0 ∨ a / 2 < t)
    (C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent) :
    Nonempty (o.PortalData H hH a t C) := by
  rcases ht with rfl | ht
  · refine ⟨⟨o, o, ho, ho, o.mem_zero_component o hH C,
      o.mem_zero_component o hH C, ?_, ?_, ?_, ?_⟩⟩
    · simpa only [dist_self, zero_add] using And.intro (le_refl (0 : ℝ)) ha
    · simpa only [dist_self, zero_add] using And.intro (le_refl (0 : ℝ)) ha
    · intro x _
      simp only [min_self, sub_zero, dist_comm x o]
      linarith
    · rintro x ⟨_, _, y, _, _, hy⟩
      exact (not_lt_of_ge dist_nonneg hy).elim
  · obtain ⟨p, hp, q, hq, hpr, hqr, hc⟩ := o.component_two_portals hJ hH ha hhalf C
      (o.entrances_nonempty hJ hH ht hhalf C)
    refine ⟨⟨p, q, hp.1, hq.1, hp.2.1, hq.2.1, hpr, hqr, ?_, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, hd⟩ := o.exit_superlevel hJ x hH ht hhalf C hx
      rcases hc z hz with hz | hz
      · exact (min_le_left _ _).trans (by linarith [dist_triangle x z p])
      · exact (min_le_right _ _).trans (by linarith [dist_triangle x z q])
    · intro x hx
      exact min_le_iff.mpr (hc x hx)

namespace PortalData

variable {o : M.Point J root} {H a t : ℝ} {hH : H ∈ J}
    {C : ((M.activeGraph J).induce (o.superlevel H hH t)).ConnectedComponent}

/-- Layer points and points only slightly beyond its top are close to a
fixed portal. The radial allowance is kept explicit for child portals. -/
lemma near_of_radial (K : o.PortalData H hH a t C)
    {δ e : ℝ} (x : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hr : dist o x ≤ t + δ + e) :
    min (dist x K.left) (dist x K.right) ≤ δ + e + 201 * a := by
  linarith [K.cover x hx]

lemma near_layer (K : o.PortalData H hH a t C)
    (hhalf : ∀ T ∈ J, |H - T| ≤ a / 2) (ha : 0 ≤ a)
    {δ : ℝ} (x : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hr : dist o (x.withHeight H hH) < t + δ) :
    min (dist x K.left) (dist x K.right) ≤ δ + 220 * a := by
  have hv : dist (x.withHeight H hH) x ≤ a / 2 := by
    rw [dist_comm, x.dist_withHeight, abs_sub_comm]
    exact hhalf x.height x.inBand
  have htri := dist_triangle o (x.withHeight H hH) x
  linarith [K.cover x hx]

/-- A near-exit point is in the equality collar of these same portals;
there is no resampling or reselecting a different portal pair. -/
lemma near_exit (K : o.PortalData H hH a t C) (hJ : IsClosed J)
    (x y : M.Point J root) (hx : x.column ∈ ColumnOrder.componentColumns C)
    (hy : y.column ∉ ColumnOrder.componentColumns C) :
    min (dist x K.left) (dist x K.right) ≤ dist x y + 200 * a := by
  obtain ⟨z, hz, hd⟩ := o.exit_superlevel_to hJ x y hH C hx hy
  rcases min_le_iff.mp (K.entrance_cover z hz) with h | h
  · exact (min_le_left _ _).trans (by linarith [dist_triangle x z K.left])
  · exact (min_le_right _ _).trans (by linarith [dist_triangle x z K.right])

end PortalData

end Point

end Model
end Columns
end PlanarL1

end

end OAI
