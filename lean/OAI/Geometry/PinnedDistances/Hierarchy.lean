import OAI.Geometry.PinnedDistances.ProductFormula

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators

/- Deterministic giant-removal identity. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace WeakPinned.Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]

structure Depth (P : Type u2) where
  value : P → P → ℝ
  symm : ∀ x y, value x y = value y x
  ultra : ∀ x y z, x ≠ y → y ≠ z → x ≠ z →
    min (value x y) (value y z) ≤ value x z

namespace Depth

variable (d : Depth P)

def share (r : ℝ) (x y : P) : Prop := x = y ∨ r ≤ d.value x y
instance (r : ℝ) (x y : P) : Decidable (d.share r x y) := Classical.propDecidable _

omit [Fintype P] [DecidableEq P] in
lemma share_refl (r : ℝ) (x : P) : d.share r x x := Or.inl rfl
omit [Fintype P] [DecidableEq P] in
lemma share_symm {r : ℝ} {x y : P} (h : d.share r x y) : d.share r y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [d.symm y x] using h)
omit [Fintype P] in
lemma share_trans {r : ℝ} {x y z : P} (hxy : d.share r x y) (hyz : d.share r y z) :
    d.share r x z := by
  by_cases h₁ : x = y
  · subst y; exact hyz
  by_cases h₂ : y = z
  · subst z; exact hxy
  by_cases h₃ : x = z
  · exact Or.inl h₃
  exact Or.inr ((le_min (hxy.resolve_left h₁) (hyz.resolve_left h₂)).trans
    (d.ultra x y z h₁ h₂ h₃))
omit [Fintype P] [DecidableEq P] in
lemma share_mono {r t : ℝ} (htr : t ≤ r) {x y : P} (h : d.share r x y) :
    d.share t x y := h.imp_right (htr.trans ·)

def cell (r : ℝ) (x : P) : Finset P := Finset.univ.filter (d.share r x)
omit [DecidableEq P] in
@[simp] lemma mem_cell (r : ℝ) (x y : P) : y ∈ d.cell r x ↔ d.share r x y := by
  simp [cell]
omit [DecidableEq P] in
@[simp] lemma self_mem_cell (r : ℝ) (x : P) : x ∈ d.cell r x := by
  simp [share_refl]
omit [DecidableEq P] in
lemma cell_nonempty (r : ℝ) (x : P) : (d.cell r x).Nonempty := ⟨x, d.self_mem_cell r x⟩

lemma cell_eq_of_share {r : ℝ} {x y : P} (h : d.share r x y) : d.cell r x = d.cell r y := by
  ext z
  simp only [mem_cell]
  exact ⟨fun hz => d.share_trans (d.share_symm h) hz, fun hz => d.share_trans h hz⟩

omit [DecidableEq P] in
lemma cell_mono {r t : ℝ} (htr : t ≤ r) (x : P) : d.cell r x ⊆ d.cell t x := by
  intro z hz
  exact (d.mem_cell t x z).mpr (d.share_mono htr ((d.mem_cell r x z).mp hz))

def cells (r : ℝ) : Finset (Finset P) := Finset.univ.image (d.cell r)
@[simp] lemma mem_cells (r : ℝ) (C : Finset P) : C ∈ d.cells r ↔ ∃ x, d.cell r x = C := by
  simp [cells]
lemma cell_mem_cells (r : ℝ) (x : P) : d.cell r x ∈ d.cells r := by simp

lemma cell_of_mem {r : ℝ} {C : Finset P} (hC : C ∈ d.cells r) {x : P} (hx : x ∈ C) :
    C = d.cell r x := by
  obtain ⟨z, rfl⟩ := (d.mem_cells r C).mp hC
  exact d.cell_eq_of_share ((d.mem_cell r z x).mp hx)

lemma cells_disjoint {r : ℝ} {C D : Finset P} (hC : C ∈ d.cells r)
    (hD : D ∈ d.cells r) (hne : C ≠ D) : Disjoint C D := by
  apply Finset.disjoint_left.mpr
  intro x hx hd
  exact hne ((d.cell_of_mem hC hx).trans (d.cell_of_mem hD hd).symm)

lemma cells_pair_sum (r : ℝ) (x y : P) :
    (∑ C ∈ d.cells r, (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      if d.share r x y then 1 else 0 := by
  have h : ∀ C ∈ d.cells r, (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0) =
      if C = d.cell r x then (if d.share r x y then 1 else 0) else 0 := by
    intro C hC
    by_cases hx : x ∈ C
    · rw [d.cell_of_mem hC hx]
      simp [d.share_refl]
    · have hne : C ≠ d.cell r x := by intro he; apply hx; simpa [he] using d.self_mem_cell r x
      simp [hx, hne]
  rw [Finset.sum_congr rfl h]
  simp [d.cell_mem_cells r x]

def giants (r : ℝ) : Finset (Finset P) :=
  (d.cells r).filter (fun C => Fintype.card P < 2*C.card)

@[simp] lemma mem_giants (r : ℝ) (C : Finset P) : C ∈ d.giants r ↔
    C ∈ d.cells r ∧ Fintype.card P < 2*C.card := by simp [giants]

lemma giants_unique {r : ℝ} {C D : Finset P} (hC : C ∈ d.giants r)
    (hD : D ∈ d.giants r) : C = D := by
  rw [d.mem_giants] at hC hD
  by_contra hne
  have hd := d.cells_disjoint hC.1 hD.1 hne
  have hc := Finset.card_le_univ (C ∪ D)
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

lemma giants_card_le_one (r : ℝ) : (d.giants r).card ≤ 1 :=
  Finset.card_le_one.mpr (fun _C hC _D hD => d.giants_unique hC hD)

def giant (r : ℝ) : Finset P := (d.giants r).biUnion id

lemma giant_eq {r : ℝ} {C : Finset P} (hC : C ∈ d.giants r) : d.giant r = C := by
  have he : d.giants r = {C} := Finset.ext fun D => by
    simp only [Finset.mem_singleton]
    exact ⟨fun hd => d.giants_unique hd hC, fun hd => hd ▸ hC⟩
  simp [giant, he]

def transformed (r : ℝ) : Multiset (Finset P) :=
  ((d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card)).val +
  ((d.giants r).val.map (fun C => Cᶜ))

def sumCells (f : Finset P → ℝ) (r : ℝ) : ℝ := ((d.transformed r).map f).sum

def pairOverlap (r : ℝ) (x y : P) : ℝ :=
  d.sumCells (fun C => if x ∈ C ∧ y ∈ C then 1 else 0) r

def giantIndicator (r : ℝ) : ℝ := if (d.giants r).Nonempty then 1 else 0

def outsideIndicator (r : ℝ) (x : P) : ℝ :=
  if (d.giants r).Nonempty ∧ x ∉ d.giant r then 1 else 0

lemma sumCells_formula (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r = (∑ C ∈ d.cells r, f C) +
      ∑ C ∈ d.giants r, (f Cᶜ - f C) := by
  classical
  simp only [sumCells, transformed, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Finset.sum, Function.comp_def]
  change (∑ C ∈ (d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card), f C) +
    (∑ C ∈ d.giants r, f Cᶜ) = (∑ C ∈ d.cells r, f C) +
      ∑ C ∈ d.giants r, (f Cᶜ - f C)
  rw [Finset.sum_sub_distrib]
  have hh := Finset.sum_filter_add_sum_filter_not (d.cells r)
    (fun C => Fintype.card P < 2*C.card) f
  change (∑ C ∈ d.giants r, f C) + _ = _ at hh
  linarith

lemma pairOverlap_formula (r : ℝ) (x y : P) :
    d.pairOverlap r x y = (if d.share r x y then 1 else 0) -
      d.giantIndicator r + d.outsideIndicator r x + d.outsideIndicator r y := by
  unfold pairOverlap
  rw [d.sumCells_formula, d.cells_pair_sum]
  unfold giantIndicator outsideIndicator
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    have he : d.giants r = {G} := Finset.ext fun C => by
      simp only [Finset.mem_singleton]
      exact ⟨fun hc => d.giants_unique hc hG, fun hc => hc ▸ hG⟩
    rw [d.giant_eq hG]
    have hg : (d.giants r).Nonempty := ⟨G,hG⟩
    simp only [he, Finset.sum_singleton, Finset.mem_compl]
    by_cases hx : x ∈ G <;> by_cases hy : y ∈ G <;> simp [hx,hy]
    ring
  · have he : d.giants r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hg
    simp [he]

lemma giants_nonempty_iff (r : ℝ) : (d.giants r).Nonempty ↔
    ∃ x : P, ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hC,hc⟩ := (d.mem_giants r C).mp hC
    obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hC
    exact ⟨x,d.cell r x,hc,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨x,C,hc,hC⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hC y hy)
    refine ⟨d.cell r x, (d.mem_giants r _).mpr ⟨d.cell_mem_cells r x, ?_⟩⟩
    have := Finset.card_le_card hsub
    omega

lemma giants_mono {r t : ℝ} (htr : t ≤ r) (hr : (d.giants r).Nonempty) :
    (d.giants t).Nonempty := by
  rw [d.giants_nonempty_iff] at hr ⊢
  obtain ⟨x,C,hc,hC⟩ := hr
  exact ⟨x,C,hc,fun y hy => d.share_mono htr (hC y hy)⟩

lemma isClosed_giants : IsClosed {r : ℝ | (d.giants r).Nonempty} := by
  simp_rw [d.giants_nonempty_iff, Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro x
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x = y
    · simp [share, hxy]
    · simp only [share, hxy, false_or]
      exact isClosed_le continuous_id continuous_const

def radius : ℝ := ∑ x, ∑ y, |d.value x y|

omit [DecidableEq P] in
lemma radius_nonneg : 0 ≤ d.radius := by unfold radius; positivity

omit [DecidableEq P] in
lemma abs_value_le_radius (x y : P) : |d.value x y| ≤ d.radius := by
  have hx : (∑ y, |d.value x y|) ≤ d.radius :=
    Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun w _ => abs_nonneg (d.value z w)))
      (Finset.mem_univ x)
  exact (Finset.single_le_sum (fun z _ => abs_nonneg (d.value x z)) (Finset.mem_univ y)).trans hx

omit [DecidableEq P] in
lemma cell_of_low {r : ℝ} (hr : r ≤ -d.radius) (x : P) : d.cell r x = Finset.univ := by
  ext y
  simp only [mem_cell, Finset.mem_univ, iff_true]
  exact Or.inr (hr.trans (abs_le.mp (d.abs_value_le_radius x y)).1)

omit [DecidableEq P] in
lemma cell_of_high {r : ℝ} (hr : d.radius < r) (x : P) : d.cell r x = {x} := by
  ext y
  simp only [mem_cell, share, Finset.mem_singleton]
  have hh : ¬r ≤ d.value x y := not_le.mpr ((abs_le.mp (d.abs_value_le_radius x y)).2.trans_lt hr)
  simp [hh, eq_comm]

lemma giants_of_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius) :
    (d.giants r).Nonempty := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := ‹Nonempty P›
  refine ⟨Finset.univ, (d.mem_giants r _).mpr ⟨?_, ?_⟩⟩
  · exact (d.mem_cells r _).mpr ⟨x, d.cell_of_low hr x⟩
  · simp only [Finset.card_univ]
    omega

lemma giants_le_radius (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : (d.giants r).Nonempty) :
    r ≤ d.radius := by
  by_contra! h
  obtain ⟨C,hC⟩ := hr
  obtain ⟨hC,hc⟩ := (d.mem_giants r C).mp hC
  obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hC
  rw [d.cell_of_high h x, Finset.card_singleton] at hc
  omega

/-- The last level containing a giant. -/
def M : ℝ := sSup {r : ℝ | (d.giants r).Nonempty}

lemma giants_cutoff (hn : 2 ≤ Fintype.card P) (r : ℝ) :
    (d.giants r).Nonempty ↔ r ≤ d.M := by
  have hne : Set.Nonempty {t : ℝ | (d.giants t).Nonempty} := ⟨-d.radius,d.giants_of_low hn le_rfl⟩
  have hbd : BddAbove {t : ℝ | (d.giants t).Nonempty} := ⟨d.radius,fun t ht => d.giants_le_radius hn ht⟩
  exact ⟨fun hr => le_csSup hbd hr, fun hr =>
    d.giants_mono hr (d.isClosed_giants.csSup_mem hne hbd)⟩

lemma M_bounds (hn : 2 ≤ Fintype.card P) : -d.radius ≤ d.M ∧ d.M ≤ d.radius := by
  constructor
  · exact (d.giants_cutoff hn _).mp (d.giants_of_low hn le_rfl)
  · exact d.giants_le_radius hn ((d.giants_cutoff hn _).mpr le_rfl)

omit [DecidableEq P] in
lemma measurable_cell (x : P) : Measurable (fun r : ℝ => d.cell r x) := by
  apply measurable_finset_iff.mpr
  intro y
  simp only [mem_cell, share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))

lemma measurable_cells : Measurable d.cells := by
  have hm : Measurable (fun r : ℝ => fun x : P => d.cell r x) :=
    measurable_pi_iff.mpr (d.measurable_cell)
  exact (measurable_of_finite (fun f : P → Finset P => Finset.univ.image f)).comp hm

lemma measurable_giants : Measurable d.giants :=
  (measurable_of_finite (fun s : Finset (Finset P) =>
    s.filter (fun C : Finset P => Fintype.card P < 2*C.card))).comp d.measurable_cells

lemma measurable_giant : Measurable d.giant :=
  (measurable_of_finite (fun s : Finset (Finset P) => s.biUnion id)).comp d.measurable_giants

lemma measurable_giantIndicator : Measurable d.giantIndicator :=
  (measurable_of_finite (fun s : Finset (Finset P) => if s.Nonempty then (1 : ℝ) else 0)).comp
    d.measurable_giants

lemma measurable_outsideIndicator (x : P) : Measurable (fun r => d.outsideIndicator r x) := by
  have hm : Measurable (fun r : ℝ => (d.giants r, d.giant r)) :=
    d.measurable_giants.prodMk d.measurable_giant
  exact (measurable_of_finite
    (fun st : Finset (Finset P) × Finset P => if st.1.Nonempty ∧ x ∉ st.2 then (1 : ℝ) else 0)).comp hm

lemma measurable_pairOverlap (x y : P) : Measurable (fun r => d.pairOverlap r x y) := by
  have hm : Measurable (fun r : ℝ => if d.share r x y then (1 : ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))
  have ht : Measurable (fun r =>
      (if d.share r x y then (1 : ℝ) else 0) - d.giantIndicator r +
        d.outsideIndicator r x + d.outsideIndicator r y) :=
    ((hm.sub d.measurable_giantIndicator).add (d.measurable_outsideIndicator x)).add
      (d.measurable_outsideIndicator y)
  simpa only [pairOverlap_formula] using ht

lemma outsideIndicator_bounds (r : ℝ) (x : P) :
    0 ≤ d.outsideIndicator r x ∧ d.outsideIndicator r x ≤ 1 := by
  unfold outsideIndicator
  split_ifs <;> norm_num

lemma pairOverlap_bounds (r : ℝ) (x y : P) :
    0 ≤ d.pairOverlap r x y ∧ d.pairOverlap r x y ≤ 2 := by
  have lo : 0 ≤ d.pairOverlap r x y := by
    unfold pairOverlap sumCells
    apply Multiset.sum_nonneg
    intro t ht
    obtain ⟨C,hC,rfl⟩ := Multiset.mem_map.mp ht
    split_ifs <;> norm_num
  refine ⟨lo, ?_⟩
  rw [pairOverlap_formula]
  have hx := (d.outsideIndicator_bounds r x).2
  have hy := (d.outsideIndicator_bounds r y).2
  by_cases hg : (d.giants r).Nonempty
  · simp only [giantIndicator, hg, reduceIte]
    split_ifs <;> linarith
  · simp [giantIndicator, outsideIndicator, hg]
    split_ifs <;> norm_num

lemma outsideIndicator_zero_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius)
    (x : P) : d.outsideIndicator r x = 0 := by
  have hg : Finset.univ ∈ d.giants r := (d.mem_giants r _).mpr ⟨
    (d.mem_cells r _).mpr ⟨x,d.cell_of_low hr x⟩, by simp only [Finset.card_univ]; omega⟩
  simp [outsideIndicator, d.giant_eq hg]

lemma outsideIndicator_zero_high (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : d.radius < r)
    (x : P) : d.outsideIndicator r x = 0 := by
  have hg : ¬(d.giants r).Nonempty := fun hg => not_le.mpr hr (d.giants_le_radius hn hg)
  simp [outsideIndicator, hg]

lemma pairOverlap_zero_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius)
    (x y : P) : d.pairOverlap r x y = 0 := by
  have hxy : d.share r x y := Or.inr (hr.trans (abs_le.mp (d.abs_value_le_radius x y)).1)
  simp [pairOverlap_formula, giantIndicator, d.giants_of_low hn hr,
    d.outsideIndicator_zero_low hn hr, hxy]

lemma pairOverlap_zero_high (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : d.radius < r)
    (x y : P) (hxy : x ≠ y) : d.pairOverlap r x y = 0 := by
  have hg : ¬(d.giants r).Nonempty := fun hg => not_le.mpr hr (d.giants_le_radius hn hg)
  have hs : ¬d.share r x y := by
    simp only [share, hxy, false_or]
    exact not_le.mpr ((abs_le.mp (d.abs_value_le_radius x y)).2.trans_lt hr)
  simp [pairOverlap_formula, giantIndicator, hg, hs, d.outsideIndicator_zero_high hn hr]

/- The diagonal is deliberately absent from overlapLength's domain: the
   transformed singleton tails have infinite diagonal overlap. -/
def potential (x : P) : ℝ := ∫ r : ℝ, d.outsideIndicator r x

def overlapLength (x y : P) (_ : x ≠ y) : ℝ := ∫ r : ℝ, d.pairOverlap r x y

lemma integrable_supported_Icc {f : ℝ → ℝ} {a b C : ℝ}
    (hm : Measurable f) (hb : ∀ r, ‖f r‖ ≤ C)
    (hz : ∀ r ∉ Set.Icc a b, f r = 0) : Integrable f := by
  have hi : IntegrableOn f (Set.Icc a b) :=
    IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb)
  have he : (Set.Icc a b).indicator f = f := by
    apply Set.indicator_eq_self.mpr
    intro r hr
    by_contra hn
    exact hr (hz r hn)
  simpa only [he] using hi.integrable_indicator measurableSet_Icc

lemma outsideIndicator_zero_compl (hn : 2 ≤ Fintype.card P) (x : P) :
    ∀ r ∉ Set.Icc (-d.radius) d.radius, d.outsideIndicator r x = 0 := by
  intro r hr
  by_cases hlo : r ≤ -d.radius
  · exact d.outsideIndicator_zero_low hn hlo x
  · exact d.outsideIndicator_zero_high hn
      (lt_of_not_ge (fun hhi => hr ⟨le_of_not_ge hlo, hhi⟩)) x

lemma pairOverlap_zero_compl (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    ∀ r ∉ Set.Icc (-d.radius) d.radius, d.pairOverlap r x y = 0 := by
  intro r hr
  by_cases hlo : r ≤ -d.radius
  · exact d.pairOverlap_zero_low hn hlo x y
  · exact d.pairOverlap_zero_high hn
      (lt_of_not_ge (fun hhi => hr ⟨le_of_not_ge hlo, hhi⟩)) x y hxy

lemma integrable_outsideIndicator (hn : 2 ≤ Fintype.card P) (x : P) :
    Integrable (fun r => d.outsideIndicator r x) := by
  apply integrable_supported_Icc (d.measurable_outsideIndicator x) (C := 1)
  · intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (d.outsideIndicator_bounds r x).1]
    exact (d.outsideIndicator_bounds r x).2
  · exact d.outsideIndicator_zero_compl hn x

lemma integrable_pairOverlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    Integrable (fun r => d.pairOverlap r x y) := by
  apply integrable_supported_Icc (d.measurable_pairOverlap x y) (C := 2)
  · intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (d.pairOverlap_bounds r x y).1]
    exact (d.pairOverlap_bounds r x y).2
  · exact d.pairOverlap_zero_compl hn x y hxy

lemma integral_cutoff {R a : ℝ} (hR : 0 ≤ R) (ha : a ∈ Set.Icc (-R) R) :
    (∫ r : ℝ in Set.Icc (-R) R, if r ≤ a then (1 : ℝ) else 0) = a + R := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  change (∫ r : ℝ in (-R)..R, {r : ℝ | r ≤ a}.indicator (fun _ => (1 : ℝ)) r) = a + R
  rw [intervalIntegral.integral_indicator ha, intervalIntegral.integral_const]
  simp

lemma depth_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    d.value x y = d.M + d.overlapLength x y hxy - d.potential x - d.potential y := by
  let I := Set.Icc (-d.radius) d.radius
  have hoc : IntegrableOn (fun r : ℝ => if r ≤ d.value x y then (1 : ℝ) else 0) I := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r => by split_ifs <;> norm_num)
  have hgc : IntegrableOn (fun r : ℝ => if r ≤ d.M then (1 : ℝ) else 0) I := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r => by split_ifs <;> norm_num)
  have hs : IntegrableOn (fun r : ℝ => (if r ≤ d.value x y then (1 : ℝ) else 0) -
      (if r ≤ d.M then (1 : ℝ) else 0)) I := hoc.sub hgc
  have hx := (d.integrable_outsideIndicator hn x).integrableOn (s := I)
  have hy := (d.integrable_outsideIndicator hn y).integrableOn (s := I)
  have ha : IntegrableOn (fun r : ℝ => (if r ≤ d.value x y then (1 : ℝ) else 0) -
      (if r ≤ d.M then (1 : ℝ) else 0) + d.outsideIndicator r x) I := hs.add hx
  have he : (∫ r in I, d.pairOverlap r x y) =
      (∫ r in I, if r ≤ d.value x y then (1 : ℝ) else 0) -
      (∫ r in I, if r ≤ d.M then (1 : ℝ) else 0) +
      (∫ r in I, d.outsideIndicator r x) + (∫ r in I, d.outsideIndicator r y) := by
    calc
      _ = ∫ r in I, ((if r ≤ d.value x y then (1 : ℝ) else 0) -
          (if r ≤ d.M then 1 else 0) + d.outsideIndicator r x + d.outsideIndicator r y) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro r _
        simp only [pairOverlap_formula, share, hxy, false_or, giantIndicator,
          d.giants_cutoff hn]
      _ = _ := by rw [integral_add ha hy, integral_add hs hx, integral_sub hoc hgc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.pairOverlap_zero_compl hn x y hxy)] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.outsideIndicator_zero_compl hn x),
    setIntegral_eq_integral_of_forall_compl_eq_zero (d.outsideIndicator_zero_compl hn y)] at he
  change d.overlapLength x y hxy = _ at he
  dsimp only [I] at he
  rw [integral_cutoff d.radius_nonneg (abs_le.mp (d.abs_value_le_radius x y)),
    integral_cutoff d.radius_nonneg (d.M_bounds hn)] at he
  change d.overlapLength x y hxy = _ - _ + d.potential x + d.potential y at he
  linarith

lemma potential_nonneg (x : P) : 0 ≤ d.potential x :=
  integral_nonneg (fun r => (d.outsideIndicator_bounds r x).1)

lemma overlapLength_nonneg (x y : P) (hxy : x ≠ y) : 0 ≤ d.overlapLength x y hxy :=
  integral_nonneg (fun r => (d.pairOverlap_bounds r x y).1)

lemma integral_bound_supported {f : ℝ → ℝ} {R C : ℝ} (hR : 0 ≤ R)
    (hi : Integrable f) (hb : ∀ r, f r ≤ C)
    (hz : ∀ r ∉ Set.Icc (-R) R, f r = 0) : (∫ r, f r) ≤ 2*R*C := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hh := integral_mono (hi.integrableOn (s := Set.Icc (-R) R))
    (integrableOn_const (s := Set.Icc (-R) R) (μ := volume)
      (C := C) (measure_Icc_lt_top.ne)) (fun r => hb r)
  rw [setIntegral_const] at hh
  simp only [Measure.real, Real.volume_Icc, sub_neg_eq_add,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R+R), smul_eq_mul] at hh
  nlinarith

lemma potential_le (hn : 2 ≤ Fintype.card P) (x : P) : d.potential x ≤ 2*d.radius := by
  have hh := integral_bound_supported d.radius_nonneg (d.integrable_outsideIndicator hn x)
    (fun r => (d.outsideIndicator_bounds r x).2) (d.outsideIndicator_zero_compl hn x)
  change d.potential x ≤ _ at hh
  simpa only [mul_one] using hh

lemma overlapLength_le (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    d.overlapLength x y hxy ≤ 4*d.radius := by
  have hh := integral_bound_supported d.radius_nonneg (d.integrable_pairOverlap hn x y hxy)
    (fun r => (d.pairOverlap_bounds r x y).2) (d.pairOverlap_zero_compl hn x y hxy)
  change d.overlapLength x y hxy ≤ _ at hh
  linarith

lemma zero_values (hn : 2 ≤ Fintype.card P) (hzero : ∀ x y, d.value x y = 0) :
    d.M = 0 ∧ (∀ x, d.potential x = 0) ∧
      (∀ x y (hxy : x ≠ y), d.overlapLength x y hxy = 0) := by
  have hr : d.radius = 0 := by simp [radius, hzero]
  refine ⟨?_, ?_, ?_⟩
  · have := d.M_bounds hn
    rw [hr] at this
    linarith [this.1, this.2]
  · intro x
    have := d.potential_le hn x
    rw [hr] at this
    linarith [d.potential_nonneg x]
  · intro x y hxy
    have := d.overlapLength_le hn x y hxy
    rw [hr] at this
    linarith [d.overlapLength_nonneg x y hxy]

/- Joint measurability and averaging over a family of realized hierarchies. -/
section Param
variable {Ω : Type u3} [MeasurableSpace Ω] (D : Ω → Depth P)
  (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
  (R : Ω → ℝ) (hR : Measurable R)
include hD hR

omit [DecidableEq P] in
lemma measurable_cell_param (x : P) : Measurable (fun ω => (D ω).cell (R ω) x) := by
  apply measurable_finset_iff.mpr
  intro y
  simp only [mem_cell, share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))

lemma measurable_cells_param : Measurable (fun ω => (D ω).cells (R ω)) := by
  have hm : Measurable (fun ω => fun x : P => (D ω).cell (R ω) x) :=
    measurable_pi_iff.mpr (measurable_cell_param D hD R hR)
  exact (measurable_of_finite (fun f : P → Finset P => Finset.univ.image f)).comp hm

lemma measurable_giants_param : Measurable (fun ω => (D ω).giants (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) =>
    s.filter (fun C : Finset P => Fintype.card P < 2*C.card))).comp
      (measurable_cells_param D hD R hR)

lemma measurable_giant_param : Measurable (fun ω => (D ω).giant (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) => s.biUnion id)).comp
    (measurable_giants_param D hD R hR)

lemma measurable_giantIndicator_param : Measurable (fun ω => (D ω).giantIndicator (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) => if s.Nonempty then (1 : ℝ) else 0)).comp
    (measurable_giants_param D hD R hR)

lemma measurable_outsideIndicator_param (x : P) : Measurable (fun ω => (D ω).outsideIndicator (R ω) x) := by
  have hm := (measurable_giants_param D hD R hR).prodMk (measurable_giant_param D hD R hR)
  exact (measurable_of_finite
    (fun st : Finset (Finset P) × Finset P => if st.1.Nonempty ∧ x ∉ st.2 then (1 : ℝ) else 0)).comp hm

lemma measurable_pairOverlap_param (x y : P) : Measurable (fun ω => (D ω).pairOverlap (R ω) x y) := by
  have hm : Measurable (fun ω => if (D ω).share (R ω) x y then (1:ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))
  have hh : Measurable (fun ω => (if (D ω).share (R ω) x y then (1:ℝ) else 0) -
      (D ω).giantIndicator (R ω) + (D ω).outsideIndicator (R ω) x + (D ω).outsideIndicator (R ω) y) :=
    ((hm.sub (measurable_giantIndicator_param D hD R hR)).add
    (measurable_outsideIndicator_param D hD R hR x)).add
    (measurable_outsideIndicator_param D hD R hR y)
  simpa only [pairOverlap_formula, Pi.add_apply, Pi.sub_apply] using hh

omit hR
lemma measurable_potential_param (x : P) : Measurable (fun ω => (D ω).potential x) := by
  have hm : Measurable (fun p : Ω × ℝ => (D p.1).outsideIndicator p.2 x) :=
    measurable_outsideIndicator_param (P := P) (Ω := Ω × ℝ) (fun p : Ω × ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd x
  simpa only [potential] using hm.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_overlapLength_param (x y : P) (hxy : x ≠ y) :
    Measurable (fun ω => (D ω).overlapLength x y hxy) := by
  have hm : Measurable (fun p : Ω × ℝ => (D p.1).pairOverlap p.2 x y) :=
    measurable_pairOverlap_param (P := P) (Ω := Ω × ℝ) (fun p : Ω × ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd x y
  simpa only [overlapLength] using hm.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_M_param (hn : 2 ≤ Fintype.card P) : Measurable (fun ω => (D ω).M) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ : Finset P).card by simpa using (show 1 < Fintype.card P by omega))
  have hh := (((hD x y).sub (measurable_overlapLength_param D hD x y hxy)).add
    (measurable_potential_param D hD x)).add (measurable_potential_param D hD y)
  have he : (fun ω => (D ω).value x y - (D ω).overlapLength x y hxy +
      (D ω).potential x + (D ω).potential y) = (fun ω => (D ω).M) := by
    funext ω
    have := (D ω).depth_identity hn x y hxy
    linarith
  change Measurable (fun ω => (D ω).value x y - (D ω).overlapLength x y hxy +
      (D ω).potential x + (D ω).potential y) at hh
  rwa [he] at hh

variable {μ : Measure Ω} (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
include hi

omit [DecidableEq P] in
omit hD in
lemma integrable_radius_param : Integrable (fun ω => (D ω).radius) μ := by
  unfold radius
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (hi x y).abs))

lemma integrable_potential_param (hn : 2 ≤ Fintype.card P) (x : P) :
    Integrable (fun ω => (D ω).potential x) μ := by
  apply Integrable.mono' ((integrable_radius_param D hi).const_mul 2)
    (measurable_potential_param D hD x).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((D ω).potential_nonneg x)]
  exact (D ω).potential_le hn x

lemma integrable_overlapLength_param (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    Integrable (fun ω => (D ω).overlapLength x y hxy) μ := by
  apply Integrable.mono' ((integrable_radius_param D hi).const_mul 4)
    (measurable_overlapLength_param D hD x y hxy).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((D ω).overlapLength_nonneg x y hxy)]
  exact (D ω).overlapLength_le hn x y hxy

lemma integrable_M_param (hn : 2 ≤ Fintype.card P) : Integrable (fun ω => (D ω).M) μ := by
  apply Integrable.mono' (integrable_radius_param D hi) (measurable_M_param D hD hn).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((D ω).M_bounds hn)

lemma integral_depth_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∫ ω, (D ω).value x y ∂μ) =
      (∫ ω, (D ω).M ∂μ) + (∫ ω, (D ω).overlapLength x y hxy ∂μ) -
      (∫ ω, (D ω).potential x ∂μ) - (∫ ω, (D ω).potential y ∂μ) := by
  have hiM := integrable_M_param D hD hi hn
  have hiL := integrable_overlapLength_param D hD hi hn x y hxy
  have hix := integrable_potential_param D hD hi hn x
  have hiy := integrable_potential_param D hD hi hn y
  calc
    _ = ∫ ω, (D ω).M + (D ω).overlapLength x y hxy - (D ω).potential x - (D ω).potential y ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => (D ω).depth_identity hn x y hxy)
    _ = _ := by
      have h₁ : Integrable (fun ω => (D ω).M + (D ω).overlapLength x y hxy) μ := hiM.add hiL
      have h₂ : Integrable (fun ω => (D ω).M + (D ω).overlapLength x y hxy - (D ω).potential x) μ := h₁.sub hix
      rw [integral_sub h₂ hiy, integral_sub h₁ hix, integral_add hiM hiL]
end Param

end Depth
end WeakPinned.Hierarchy

end
end
end

end OAI
