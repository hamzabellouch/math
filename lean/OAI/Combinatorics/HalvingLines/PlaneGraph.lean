import OAI.Combinatorics.HalvingLines.RankCoordinates

namespace OAI

open Filter Topology

namespace PlanarHalving
namespace PlaneGraph

noncomputable def height (p q : Point) (x : ℝ) : ℝ :=
  p.2 + (x - p.1) * PlanarHalving.slope p q

@[simp] lemma height_left (p q : Point) : height p q p.1 = p.2 := by simp [height]
@[simp] lemma height_right (p q : Point) (hx : p.1 ≠ q.1) : height p q q.1 = q.2 := by
  unfold height PlanarHalving.slope
  have h : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
  field_simp
  ring

lemma height_point_openSegment (p q : Point) {x : ℝ} (hl : p.1 < x) (hr : x < q.1) :
    (x, height p q x) ∈ openSegment ℝ p q := by
  rw [openSegment_eq_image]
  have hd : 0 < q.1 - p.1 := sub_pos.mpr (hl.trans hr)
  refine ⟨(x - p.1) / (q.1 - p.1), ⟨div_pos (sub_pos.mpr hl) hd, ?_⟩, ?_⟩
  · apply (div_lt_one hd).mpr
    linarith
  · ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, height, PlanarHalving.slope]
    all_goals field_simp; ring

lemma height_continuous (p q : Point) : Continuous (height p q) := by
  unfold height
  fun_prop

lemma height_order {p q r s : Point}
    (hd : Disjoint (openSegment ℝ p q) (openSegment ℝ r s))
    {x y : ℝ} (hxy : x < y) (hp : p.1 ≤ x) (hr : r.1 ≤ x)
    (hq : y ≤ q.1) (hs : y ≤ s.1)
    (hstart : height p q x < height r s x) :
    height p q y ≤ height r s y := by
  by_contra h
  have hend : height r s y < height p q y := lt_of_not_ge h
  let f : ℝ → ℝ := fun z => height p q z - height r s z
  have hc : Continuous f := (height_continuous p q).sub (height_continuous r s)
  have hfx : f x < 0 := sub_neg.mpr hstart
  have hfy : 0 < f y := sub_pos.mpr hend
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc hxy.le hc.continuousOn ⟨hfx.le, hfy.le⟩
  have hxz : x < z := lt_of_le_of_ne hz.1 (by intro heq; subst z; exact ne_of_lt hfx he)
  have hzy : z < y := lt_of_le_of_ne hz.2 (by intro heq; subst z; exact ne_of_gt hfy he)
  have h₁ := height_point_openSegment p q (hp.trans_lt hxz) (hzy.trans_le hq)
  have h₂ := height_point_openSegment r s (hr.trans_lt hxz) (hzy.trans_le hs)
  have hv : height p q z = height r s z := sub_eq_zero.mp he
  rw [← hv] at h₂
  exact Set.disjoint_left.mp hd h₁ h₂

def Position {V : Type*} (P : V → Point) : Prop :=
  Function.Injective P ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    orient (P i) (P j) (P l) ≠ 0

variable {V : Type*} [Fintype V] {P : V → Point}

structure Drawing (P : V → Point) where
  vertices : Finset V
  edges : Finset (V × V)
  right : ∀ e ∈ edges, (P e.1).1 < (P e.2).1
  ends : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices

def Drawing.NonCrossing (D : Drawing P) : Prop :=
  ∀ e ∈ D.edges, ∀ f ∈ D.edges, e ≠ f →
    Disjoint (openSegment ℝ (P e.1) (P e.2)) (openSegment ℝ (P f.1) (P f.2))

omit [Fintype V] in
lemma slope_eq_implies_eq (hP : Position P) {v u w : V}
    (hu : (P v).1 < (P u).1) (hw : (P v).1 < (P w).1)
    (hs : PlanarHalving.slope (P v) (P u) = PlanarHalving.slope (P v) (P w)) : u = w := by
  by_contra hn
  have hvu : v ≠ u := by intro h; subst u; exact (lt_irrefl _ hu)
  have hvw : v ≠ w := by intro h; subst w; exact (lt_irrefl _ hw)
  have hyu := height_right (P v) (P u) hu.ne
  have hyw := height_right (P v) (P w) hw.ne
  rw [height, hs] at hyu
  rw [height] at hyw
  apply hP.2 v u w hvu hn hvw
  unfold orient
  have hu' : (P u).2 - (P v).2 = ((P u).1 - (P v).1) * PlanarHalving.slope (P v) (P w) := by linarith
  have hw' : (P w).2 - (P v).2 = ((P w).1 - (P v).1) * PlanarHalving.slope (P v) (P w) := by linarith
  rw [hu', hw']
  ring

def IsGap (D : Drawing P) (g : V × V × V) : Prop :=
  (g.1, g.2.1) ∈ D.edges ∧ (g.1, g.2.2) ∈ D.edges ∧
  PlanarHalving.slope (P g.1) (P g.2.1) < PlanarHalving.slope (P g.1) (P g.2.2) ∧
  ∀ w, (g.1, w) ∈ D.edges →
    PlanarHalving.slope (P g.1) (P g.2.1) < PlanarHalving.slope (P g.1) (P w) →
    PlanarHalving.slope (P g.1) (P g.2.2) ≤ PlanarHalving.slope (P g.1) (P w)

noncomputable def Drawing.gaps (D : Drawing P) : Finset (V × V × V) :=
  by classical exact Finset.univ.filter (IsGap D)

lemma height_lt_height_iff (p u v : Point) {x : ℝ} (hx : p.1 < x) :
    height p u x < height p v x ↔ PlanarHalving.slope p u < PlanarHalving.slope p v := by
  simp only [height, add_lt_add_iff_left, mul_lt_mul_iff_right₀ (sub_pos.mpr hx)]

lemma height_le_height_iff (p u v : Point) {x : ℝ} (hx : p.1 < x) :
    height p u x ≤ height p v x ↔ PlanarHalving.slope p u ≤ PlanarHalving.slope p v := by
  simp only [height, add_le_add_iff_left, mul_le_mul_iff_right₀ (sub_pos.mpr hx)]

def InWedge (P : V → Point) (g : V × V × V) (q : V) : Prop :=
  (P g.1).1 < (P q).1 ∧ (P q).1 ≤ (P g.2.1).1 ∧ (P q).1 ≤ (P g.2.2).1 ∧
  height (P g.1) (P g.2.1) (P q).1 ≤ (P q).2 ∧
  (P q).2 ≤ height (P g.1) (P g.2.2) (P q).1

def FirstVertex (P : V → Point) (s : Finset V) (g : V × V × V) (q : V) : Prop :=
  InWedge P g q ∧ ∀ r ∈ s, InWedge P g r → (P q).1 ≤ (P r).1

omit [Fintype V] in
lemma IsGap.width_pos {D : Drawing P} {g : V × V × V} (hg : IsGap D g)
    {x : ℝ} (hx : (P g.1).1 < x) : height (P g.1) (P g.2.1) x < height (P g.1) (P g.2.2) x :=
  (height_lt_height_iff _ _ _ hx).mpr hg.2.2.1

omit [Fintype V] in
lemma IsGap.exists_inWedge {D : Drawing P} {g : V × V × V} (hg : IsGap D g) :
    ∃ q ∈ D.vertices, InWedge P g q := by
  have hl := D.right _ hg.1
  have hu := D.right _ hg.2.1
  by_cases h : (P g.2.1).1 ≤ (P g.2.2).1
  · refine ⟨g.2.1, (D.ends _ hg.1).2, hl, le_rfl, h, ?_, ?_⟩
    · rw [height_right _ _ hl.ne]
    · simpa only [height_right _ _ hl.ne] using (hg.width_pos hl).le
  · refine ⟨g.2.2, (D.ends _ hg.2.1).2, hu, (not_le.mp h).le, le_rfl, ?_, ?_⟩
    · simpa only [height_right _ _ hu.ne] using (hg.width_pos hu).le
    · rw [height_right _ _ hu.ne]

omit [Fintype V] in
lemma IsGap.exists_firstVertex {D : Drawing P} {g : V × V × V} (hg : IsGap D g) :
    ∃ q : ↥D.vertices, FirstVertex P D.vertices g q := by
  classical
  let W := D.vertices.filter (InWedge P g)
  have he : W.Nonempty := by
    obtain ⟨q, hqv, hq⟩ := hg.exists_inWedge
    exact ⟨q, Finset.mem_filter.mpr ⟨hqv, hq⟩⟩
  obtain ⟨q, hq, hmin⟩ := W.exists_min_image (fun r => (P r).1) he
  refine ⟨⟨q, (Finset.mem_filter.mp hq).1⟩, (Finset.mem_filter.mp hq).2, ?_⟩
  intro r hrv hr
  exact hmin r (Finset.mem_filter.mpr ⟨hrv, hr⟩)

omit [Fintype V] in
lemma IsGap.separated_of_same_source (hP : Position P) {D : Drawing P}
    {g h : V × V × V} (hg : IsGap D g) (hh : IsGap D h)
    (hsrc : g.1 = h.1) (hne : g ≠ h) {x : ℝ} (hx : (P g.1).1 < x) :
    height (P g.1) (P g.2.2) x ≤ height (P h.1) (P h.2.1) x ∨
    height (P h.1) (P h.2.2) x ≤ height (P g.1) (P g.2.1) x := by
  have hhl : (h.1, h.2.1) ∈ D.edges := hh.1
  have hhu : (h.1, h.2.2) ∈ D.edges := hh.2.1
  have hgl : (g.1, g.2.1) ∈ D.edges := hg.1
  have hgu : (g.1, g.2.2) ∈ D.edges := hg.2.1
  rcases lt_trichotomy (PlanarHalving.slope (P g.1) (P g.2.1))
      (PlanarHalving.slope (P h.1) (P h.2.1)) with hl | he | hl
  · left
    rw [← hsrc] at hhl hl ⊢
    exact (height_le_height_iff _ _ _ hx).mpr (hg.2.2.2 _ hhl hl)
  · have hlower : g.2.1 = h.2.1 := by
      rw [← hsrc] at hhl he
      exact slope_eq_implies_eq hP (D.right _ hgl) (D.right _ hhl) he
    have hupper : g.2.2 = h.2.2 := by
      have hab := hh.2.2.1
      have hba := hg.2.2.1
      rw [← hsrc] at hab hhu
      rw [← hlower] at hab
      have hb := hg.2.2.2 _ hhu hab
      rw [hsrc] at hba hgu
      rw [hlower] at hba
      have ha := hh.2.2.2 _ hgu hba
      rw [← hsrc] at ha
      exact slope_eq_implies_eq hP (v := g.1)
        (D.right (g.1, g.2.2) hg.2.1) (D.right (g.1, h.2.2) hhu) (le_antisymm hb ha)
    exact (hne (Prod.ext hsrc (Prod.ext hlower hupper))).elim
  · right
    rw [hsrc] at hgl hl hx ⊢
    exact (height_le_height_iff _ _ _ hx).mpr (hh.2.2.2 _ hgl hl)

omit [Fintype V] in
lemma firstVertex_separated_of_source_lt {D : Drawing P} (hD : D.NonCrossing)
    {g h : V × V × V} (hg : IsGap D g) (hh : IsGap D h)
    {q : V} (hqg : FirstVertex P D.vertices g q) (hqh : FirstVertex P D.vertices h q)
    (hsrc : (P g.1).1 < (P h.1).1) :
    height (P g.1) (P g.2.2) (P q).1 ≤ height (P h.1) (P h.2.1) (P q).1 ∨
    height (P h.1) (P h.2.2) (P q).1 ≤ height (P g.1) (P g.2.1) (P q).1 := by
  have hnot : ¬ (height (P g.1) (P g.2.1) (P h.1).1 ≤ (P h.1).2 ∧
      (P h.1).2 ≤ height (P g.1) (P g.2.2) (P h.1).1) := by
    intro hi
    have hw : InWedge P g h.1 := ⟨hsrc, hqh.1.1.le.trans hqg.1.2.1,
      hqh.1.1.le.trans hqg.1.2.2.1, hi⟩
    exact (not_le_of_gt hqh.1.1) (hqg.2 _ (D.ends _ hh.1).1 hw)
  have hneq : g.1 ≠ h.1 := by intro h; rw [h] at hsrc; exact lt_irrefl _ hsrc
  rcases not_and_or.mp hnot with hlo | hup
  · right
    apply height_order (hD _ hh.2.1 _ hg.1 (by intro h; exact hneq (Prod.mk.inj h).1.symm))
      hqh.1.1 le_rfl hsrc.le hqh.1.2.2.1 hqg.1.2.1
    simpa only [height_left] using lt_of_not_ge hlo
  · left
    apply height_order (hD _ hg.2.1 _ hh.1 (by intro h; exact hneq (Prod.mk.inj h).1))
      hqh.1.1 hsrc.le le_rfl hqg.1.2.2.1 hqh.1.2.1
    simpa only [height_left] using lt_of_not_ge hup

omit [Fintype V] in
lemma FirstVertex.separated (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) {D : Drawing P} (hD : D.NonCrossing)
    {g h : V × V × V} (hg : IsGap D g) (hh : IsGap D h)
    {q : V} (hqg : FirstVertex P D.vertices g q) (hqh : FirstVertex P D.vertices h q) (hne : g ≠ h) :
    height (P g.1) (P g.2.2) (P q).1 ≤ height (P h.1) (P h.2.1) (P q).1 ∨
    height (P h.1) (P h.2.2) (P q).1 ≤ height (P g.1) (P g.2.1) (P q).1 := by
  rcases lt_trichotomy (P g.1).1 (P h.1).1 with hl | he | hl
  · exact firstVertex_separated_of_source_lt hD hg hh hqg hqh hl
  · exact hg.separated_of_same_source hP hh (hx he) hne hqg.1.1
  · exact (firstVertex_separated_of_source_lt hD hh hg hqh hqg hl).symm

noncomputable def Drawing.first (D : Drawing P) (g : ↥D.gaps) : ↥D.vertices :=
  by classical exact Classical.choose ((Finset.mem_filter.mp g.property).2.exists_firstVertex)

lemma Drawing.first_spec (D : Drawing P) (g : ↥D.gaps) : FirstVertex P D.vertices g.val (D.first g) :=
  by classical exact Classical.choose_spec ((Finset.mem_filter.mp g.property).2.exists_firstVertex)

noncomputable def Drawing.gapCharge (D : Drawing P) (g : ↥D.gaps) : ↥D.vertices × Bool :=
  by classical exact (D.first g, decide
    (height (P g.val.1) (P g.val.2.1) (P (D.first g)).1 < (P (D.first g)).2))

lemma Drawing.gapCharge_injective (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) (hD : D.NonCrossing) :
    Function.Injective D.gapCharge := by
  classical
  intro g h he
  apply Subtype.ext
  by_contra hne
  have hq : D.first g = D.first h := congrArg Prod.fst he
  have hb := congrArg Prod.snd he
  change decide (height (P g.val.1) (P g.val.2.1) (P (D.first g)).1 < (P (D.first g)).2) =
    decide (height (P h.val.1) (P h.val.2.1) (P (D.first h)).1 < (P (D.first h)).2) at hb
  rw [← hq] at hb
  have hg : IsGap D g.val := (Finset.mem_filter.mp g.property).2
  have hh : IsGap D h.val := (Finset.mem_filter.mp h.property).2
  have hfg := D.first_spec g
  have hfh := D.first_spec h
  rw [← hq] at hfh
  have hgwidth := hg.width_pos hfg.1.1
  have hhwidth := hh.width_pos hfh.1.1
  rcases FirstVertex.separated hP hx hD hg hh hfg hfh hne with hsep | hsep
  · have htrue : height (P g.val.1) (P g.val.2.1) (P (D.first g)).1 < (P (D.first g)).2 :=
      hgwidth.trans_le (hsep.trans hfh.1.2.2.2.1)
    have hfalse : ¬ height (P h.val.1) (P h.val.2.1) (P (D.first g)).1 < (P (D.first g)).2 := by
      linarith only [hsep, hfg.1.2.2.2.2]
    simp [htrue, hfalse] at hb
  · have htrue : height (P h.val.1) (P h.val.2.1) (P (D.first g)).1 < (P (D.first g)).2 :=
      hhwidth.trans_le (hsep.trans hfg.1.2.2.2.1)
    have hfalse : ¬ height (P g.val.1) (P g.val.2.1) (P (D.first g)).1 < (P (D.first g)).2 := by
      linarith only [hsep, hfh.1.2.2.2.2]
    simp [htrue, hfalse] at hb

lemma Drawing.card_gaps_le (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) (hD : D.NonCrossing) :
    D.gaps.card ≤ 2 * D.vertices.card := by
  have h := Fintype.card_le_of_injective D.gapCharge (D.gapCharge_injective hP hx hD)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool,
    Nat.mul_comm] using h

lemma Drawing.exists_next_gap (D : Drawing P) {v u : V} (he : (v,u) ∈ D.edges)
    (hh : ∃ w, (v,w) ∈ D.edges ∧ PlanarHalving.slope (P v) (P u) < PlanarHalving.slope (P v) (P w)) :
    ∃ w, IsGap D (v,u,w) := by
  classical
  let W := Finset.univ.filter (fun w => (v,w) ∈ D.edges ∧
    PlanarHalving.slope (P v) (P u) < PlanarHalving.slope (P v) (P w))
  have hw : W.Nonempty := by obtain ⟨w, hw⟩ := hh; exact ⟨w, by simpa [W] using hw⟩
  obtain ⟨w, hw, hmin⟩ := W.exists_min_image (fun w => PlanarHalving.slope (P v) (P w)) hw
  have hp := (Finset.mem_filter.mp hw).2
  refine ⟨w, he, hp.1, hp.2, ?_⟩
  intro r hr hs
  exact hmin r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr, hs⟩)

noncomputable def Drawing.edgeCharge (D : Drawing P) (e : ↥D.edges) : ↥D.vertices ⊕ ↥D.gaps := by
  classical
  exact if h : ∃ w, IsGap D (e.val.1, e.val.2, w) then
    Sum.inr ⟨(e.val.1, e.val.2, Classical.choose h), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Classical.choose_spec h⟩⟩
  else Sum.inl ⟨e.val.1, (D.ends _ e.property).1⟩

lemma Drawing.edgeCharge_injective (hP : Position P) (D : Drawing P) :
    Function.Injective D.edgeCharge := by
  classical
  intro e f he
  dsimp only [Drawing.edgeCharge] at he
  split_ifs at he with hg hh
  · have heq := congrArg Subtype.val (Sum.inr.inj he)
    apply Subtype.ext
    exact Prod.ext (Prod.mk.inj heq).1 (Prod.mk.inj (Prod.mk.inj heq).2).1
  · rename_i hh
    have hsrc : e.val.1 = f.val.1 := congrArg Subtype.val (Sum.inl.inj he)
    have hemax : ¬ ∃ w, (e.val.1, w) ∈ D.edges ∧
        PlanarHalving.slope (P e.val.1) (P e.val.2) < PlanarHalving.slope (P e.val.1) (P w) :=
      fun h => hg (D.exists_next_gap e.property h)
    have hfmax : ¬ ∃ w, (f.val.1, w) ∈ D.edges ∧
        PlanarHalving.slope (P f.val.1) (P f.val.2) < PlanarHalving.slope (P f.val.1) (P w) :=
      fun h => hh (D.exists_next_gap f.property h)
    have hef : PlanarHalving.slope (P e.val.1) (P e.val.2) ≤
        PlanarHalving.slope (P f.val.1) (P f.val.2) := by
      by_contra h
      apply hfmax
      refine ⟨e.val.2, ?_, ?_⟩
      · simpa only [← hsrc, Prod.mk.eta] using e.property
      · simpa only [← hsrc] using lt_of_not_ge h
    have hfe : PlanarHalving.slope (P f.val.1) (P f.val.2) ≤
        PlanarHalving.slope (P e.val.1) (P e.val.2) := by
      by_contra h
      apply hemax
      refine ⟨f.val.2, ?_, ?_⟩
      · simpa only [hsrc, Prod.mk.eta] using f.property
      · simpa only [hsrc] using lt_of_not_ge h
    have hright := D.right f.val f.property
    have heq := le_antisymm hef hfe
    rw [← hsrc] at hright heq
    have htarget := slope_eq_implies_eq hP (D.right e.val e.property) hright heq
    exact Subtype.ext (Prod.ext hsrc htarget)

theorem Drawing.planar_bound (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) (hD : D.NonCrossing) :
    D.edges.card ≤ 3 * D.vertices.card := by
  have hc := Fintype.card_le_of_injective D.edgeCharge (D.edgeCharge_injective hP)
  have hcard : D.edges.card ≤ D.vertices.card + D.gaps.card := by
    simpa only [Fintype.card_coe, Fintype.card_sum] using hc
  have hg := D.card_gaps_le hP hx hD
  omega

omit [Fintype V] in
lemma slope_eq_implies_eq_ne (hP : Position P) {v u w : V}
    (hu : (P v).1 ≠ (P u).1) (hw : (P v).1 ≠ (P w).1)
    (hs : PlanarHalving.slope (P v) (P u) = PlanarHalving.slope (P v) (P w)) : u = w := by
  by_contra hn
  have hvu : v ≠ u := fun h => hu (congrArg (fun i => (P i).1) h)
  have hvw : v ≠ w := fun h => hw (congrArg (fun i => (P i).1) h)
  have hyu := height_right (P v) (P u) hu
  have hyw := height_right (P v) (P w) hw
  rw [height, hs] at hyu
  rw [height] at hyw
  apply hP.2 v u w hvu hn hvw
  unfold orient
  have hu' : (P u).2 - (P v).2 = ((P u).1 - (P v).1) * PlanarHalving.slope (P v) (P w) := by linarith
  have hw' : (P w).2 - (P v).2 = ((P w).1 - (P v).1) * PlanarHalving.slope (P v) (P w) := by linarith
  rw [hu', hw']
  ring

lemma height_of_mem_openSegment {p q z : Point} (hx : p.1 ≠ q.1)
    (hz : z ∈ openSegment ℝ p q) : z.1 ≠ p.1 ∧ z.2 = height p q z.1 := by
  rw [openSegment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hd : q.1 - p.1 ≠ 0 := sub_ne_zero.mpr hx.symm
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · have hmul : t * (q.1 - p.1) ≠ 0 := mul_ne_zero ht.1.ne' hd
    intro he
    apply hmul
    linarith
  · unfold height PlanarHalving.slope
    field_simp
    ring

lemma openSegment_horizontal_bounds {p q z : Point} (hx : p.1 < q.1)
    (hz : z ∈ openSegment ℝ p q) : p.1 < z.1 ∧ z.1 < q.1 := by
  rw [openSegment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  constructor <;> nlinarith [mul_pos ht.1 (sub_pos.mpr hx),
    mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hx)]

omit [Fintype V] in
lemma incident_disjoint (hP : Position P) (hx : Function.Injective (fun v => (P v).1))
    {v u w : V} (hvu : v ≠ u) (hvw : v ≠ w) (huw : u ≠ w) :
    Disjoint (openSegment ℝ (P v) (P u)) (openSegment ℝ (P v) (P w)) := by
  apply Set.disjoint_left.mpr
  intro z hzu hzw
  have hu := height_of_mem_openSegment (fun h => hvu (hx h)) hzu
  have hw := height_of_mem_openSegment (fun h => hvw (hx h)) hzw
  have he : PlanarHalving.slope (P v) (P u) = PlanarHalving.slope (P v) (P w) := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hu.1)
    dsimp only [height] at hu hw
    linarith only [hu.2, hw.2]
  exact huw (slope_eq_implies_eq_ne hP (fun h => hvu (hx h)) (fun h => hvw (hx h)) he)

def Crosses (P : V → Point) (e f : V × V) : Prop :=
  ¬ Disjoint (openSegment ℝ (P e.1) (P e.2)) (openSegment ℝ (P f.1) (P f.2))

omit [Fintype V] in
lemma Drawing.crossing_endpoints (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P)
    {e f : V × V} (he : e ∈ D.edges) (hf : f ∈ D.edges) (hne : e ≠ f)
    (hc : Crosses P e f) :
    e.1 ≠ e.2 ∧ f.1 ≠ f.2 ∧ e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
  have hev : e.1 ≠ e.2 := by intro h; have := D.right _ he; rw [h] at this; exact lt_irrefl _ this
  have hfv : f.1 ≠ f.2 := by intro h; have := D.right _ hf; rw [h] at this; exact lt_irrefl _ this
  have h11 : e.1 ≠ f.1 := by
    intro h
    apply hc
    rw [h]
    exact incident_disjoint hP hx (by simpa only [← h] using hev) hfv
      (fun h' => hne (Prod.ext h h'))
  have h22 : e.2 ≠ f.2 := by
    intro h
    apply hc
    rw [openSegment_symm ℝ (P e.1), openSegment_symm ℝ (P f.1), h]
    exact incident_disjoint hP hx (by simpa only [← h] using hev.symm) hfv.symm
      (fun h' => hne (Prod.ext h' h))
  obtain ⟨z, hze, hzf⟩ := Set.not_disjoint_iff.mp hc
  have hxe := openSegment_horizontal_bounds (D.right _ he) hze
  have hxf := openSegment_horizontal_bounds (D.right _ hf) hzf
  refine ⟨hev, hfv, h11, ?_, ?_, h22⟩
  · intro h
    rw [h] at hxe
    exact lt_irrefl _ (hxe.1.trans hxf.2)
  · intro h
    rw [h] at hxe
    exact lt_irrefl _ (hxf.1.trans hxe.2)

noncomputable def edgeIndex : (V × V) ≃ Fin (Fintype.card (V × V)) := Fintype.equivFin _

noncomputable def Drawing.crossings (D : Drawing P) : Finset ((V × V) × (V × V)) := by
  classical
  exact (D.edges ×ˢ D.edges).filter (fun ef => edgeIndex ef.1 < edgeIndex ef.2 ∧ Crosses P ef.1 ef.2)

noncomputable def Drawing.uncross (D : Drawing P) : Drawing P := by
  classical
  exact ⟨D.vertices, D.edges \ D.crossings.image Prod.fst,
    fun e he => D.right e (Finset.mem_sdiff.mp he).1,
    fun e he => D.ends e (Finset.mem_sdiff.mp he).1⟩

lemma Drawing.uncross_nonCrossing (D : Drawing P) : D.uncross.NonCrossing := by
  classical
  intro e he f hf hne
  by_contra hc
  have he' := Finset.mem_sdiff.mp he
  have hf' := Finset.mem_sdiff.mp hf
  have hi : edgeIndex e ≠ edgeIndex f := fun h => hne (edgeIndex.injective h)
  rcases hi.lt_or_gt with hlt | hlt
  · apply he'.2
    exact Finset.mem_image.mpr ⟨(e,f), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨he'.1, hf'.1⟩, hlt, hc⟩, rfl⟩
  · apply hf'.2
    exact Finset.mem_image.mpr ⟨(f,e), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hf'.1, he'.1⟩, hlt, fun h => hc h.symm⟩, rfl⟩

theorem Drawing.linear_crossing_bound (hP : Position P)
    (hx : Function.Injective (fun v => (P v).1)) (D : Drawing P) :
    D.edges.card ≤ 3 * D.vertices.card + D.crossings.card := by
  classical
  have hp := D.uncross.planar_bound hP hx D.uncross_nonCrossing
  change (D.edges \ D.crossings.image Prod.fst).card ≤ 3 * D.vertices.card at hp
  have hi : (D.edges ∩ D.crossings.image Prod.fst).card ≤ D.crossings.card :=
    (Finset.card_le_card Finset.inter_subset_right).trans (Finset.card_image_le)
  have he := Finset.card_sdiff_add_card_inter D.edges (D.crossings.image Prod.fst)
  omega

end PlaneGraph
end PlanarHalving

end OAI
