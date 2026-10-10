import OAI.Computability.Superstring.DistributeCode

namespace OAI

namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

def representative (K : Code α) (i : ℕ) : ℕ :=
  first K.1.length (fun j => compatible K i j)

@[fun_prop] theorem poly_representative :
    Poly (fun q : Code α × ℕ => representative q.1 q.2) := by
  unfold representative first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ) × ℕ => compatible q.1.1 q.1.2 q.2)
    (by fun_prop) (by fun_prop))

def groups (K : Code α) : List ℕ :=
  (List.range K.1.length).filter (fun i => equal (representative K i) i)

@[fun_prop] theorem poly_groups : Poly (fun K : Code α => groups K) := by
  unfold groups
  exact BitCode.Poly.filterFn
    (p := fun q : Code α × ℕ => equal (representative q.1 q.2) q.2)
    (by fun_prop) (by fun_prop)

omit [Coded α] in
theorem representative_spec {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i : Fin K.1.length) :
    representative K i.val < K.1.length ∧
      compatible K i.val (representative K i.val) = true ∧
      ∀ j : Fin K.1.length, C.SameText i j → representative K i.val ≤ j.val := by
  obtain hh := first_spec (n := K.1.length) (P := fun j => compatible K i.val j)
    ⟨i.val,i.isLt,(compatible_eq h i i).mpr (C.textSetoid.refl i)⟩
  exact ⟨hh.1,hh.2.1,fun j hj => hh.2.2 j.val j.isLt ((compatible_eq h i j).mpr hj)⟩

omit [Coded α] in
def repFin {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) : Fin K.1.length :=
  ⟨representative K i.val,(representative_spec h i).1⟩

omit [Coded α] in
theorem same_repFin {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i : Fin K.1.length) :
    C.SameText i (repFin h i) :=
  (compatible_eq h i (repFin h i)).mp (representative_spec h i).2.1

omit [Coded α] in
theorem representative_eq_iff {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i j : Fin K.1.length) :
    representative K i.val = representative K j.val ↔ C.SameText i j := by
  constructor
  · intro he
    have he' : repFin h i = repFin h j := Fin.ext he
    have hj := same_repFin h j
    rw [← he'] at hj
    exact C.textSetoid.trans (same_repFin h i) (C.textSetoid.symm hj)
  · intro hs
    apply le_antisymm
    · exact (representative_spec h i).2.2 (repFin h j)
        (C.textSetoid.trans hs (same_repFin h j))
    · exact (representative_spec h j).2.2 (repFin h i)
        (C.textSetoid.trans (C.textSetoid.symm hs) (same_repFin h i))

omit [Coded α] in
theorem representative_idem {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (i : Fin K.1.length) :
    representative K (representative K i.val) = representative K i.val :=
  ((representative_eq_iff h i (repFin h i)).mpr (same_repFin h i)).symm

abbrev Group (K : Code α) := {i : Fin K.1.length // representative K i.val = i.val}

omit [Coded α] in
def groupOf {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) : Group K :=
  ⟨repFin h i,representative_idem h i⟩

omit [Coded α] in
theorem groupOf_eq_iff {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (i : Fin K.1.length) (g : Group K) :
    groupOf h i = g ↔ C.SameText i g.val := by
  constructor
  · intro he
    have hh := same_repFin h i
    have hh' := congrArg Subtype.val he
    rwa [← hh']
  · intro hs
    apply Subtype.ext
    apply Fin.ext
    exact ((representative_eq_iff h i g.val).mpr hs).trans g.property

omit [Coded α] in
theorem compatible_groupOf {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C)
    (i : Fin K.1.length) (g : Group K) :
    (∃ d : ℤ, ∀ x, C.text i x = C.text g.val (x+d)) ↔ groupOf h i = g := by
  rw [groupOf_eq_iff h]
  constructor
  · rintro ⟨d,hd⟩
    refine ⟨-d,fun x => ?_⟩
    simpa only [add_assoc, neg_add_cancel, add_zero] using hd (x + -d)
  · intro hi
    obtain ⟨d,hd⟩ := C.textSetoid.symm hi
    exact ⟨d,fun x => (hd x).symm⟩

noncomputable def collection {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V) :
    LayerCollection V (Group K) where
  text := fun g => C.text g.val
  period := fun g => period K g.val.val
  size := fun g => Fintype.card (C.Aligned (C.text g.val))
  positive := fun g => (period_spec h g.val).1.positive
  periodic := fun g => (period_spec h g.val).1.periodic
  nonempty := fun g => Fintype.card_pos_iff.mpr ⟨⟨g.val,rfl⟩⟩
  layer := fun g j => C.layer closed (period_spec h g.val).1.periodic j
  ordered := fun g i j hij x => C.layers_ordered (C.text g.val) i j hij x
  different := by
    intro g d hgd c hh
    have hs : C.SameText g.val d.val := by
      refine ⟨-c,fun x => ?_⟩
      simpa only [add_assoc, neg_add_cancel, add_zero] using congrFun hh (x + -c)
    apply hgd
    apply Subtype.ext
    apply Fin.ext
    have he := (representative_eq_iff h g.val d.val).mpr hs
    simpa only [g.property, d.property] using he

noncomputable def phaseEquiv {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Group K) :
    (Fin (period K g.val.val) × Fin (Fintype.card (C.Aligned (C.text g.val)))) ≃
      {i : Fin K.1.length // groupOf h i = g} :=
  (Equiv.prodCongr (Equiv.refl _) (C.enumerate (C.text g.val))).trans
    ((C.phaseEquiv (period_spec h g.val).1).trans
      (Equiv.subtypeEquivRight (fun i => compatible_groupOf h i g)))

noncomputable def allPhaseEquiv {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) :
    (Σ g : Group K, Fin (period K g.val.val) ×
      Fin (Fintype.card (C.Aligned (C.text g.val)))) ≃ Fin K.1.length :=
  (Equiv.sigmaCongrRight (phaseEquiv h)).trans (Equiv.sigmaFiberEquiv (groupOf h))

omit [Coded α] in
theorem collection_budget {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V) :
    ∑ g : Group K, (collection h closed).period g * (collection h closed).size g =
      K.1.length := by
  classical
  have hh := Fintype.card_congr (allPhaseEquiv h)
  simpa only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, collection] using hh

omit [Coded α] in
theorem allPhaseEquiv_value {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Group K)
    (r : Fin (period K g.val.val)) (j : Fin (Fintype.card (C.Aligned (C.text g.val)))) :
    allPhaseEquiv h ⟨g,r,j⟩ = (C.next ^ (r.val : ℤ)) (C.enumerate (C.text g.val) j).val := rfl

omit [Coded α] in
theorem phase_prefix_count {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (g : Group K)
    (r : Fin (period K g.val.val)) (s : List α) :
    (Finset.univ.filter (fun j => s <+: textWord (C.text g.val) r.val
      (C.sortedExit (C.text g.val) j r.val))).card =
      (Finset.univ.filter (fun j => s <+: C.word (allPhaseEquiv h ⟨g,r,j⟩))).card := by
  classical
  change (Finset.univ.filter (fun j => s <+: textWord (C.text g.val) r.val
    (OrderStats.order (C.exits (C.text g.val) r.val) j))).card = _
  rw [OrderStats.card_filter_order (C.exits (C.text g.val) r.val)
    (fun e => s <+: textWord (C.text g.val) r.val e)]
  congr 1
  apply Finset.filter_congr
  intro j _
  have he := C.translated_word (C.enumerate (C.text g.val) j).val (r.val : ℤ)
  rw [(C.enumerate (C.text g.val) j).property] at he
  rw [allPhaseEquiv_value, he]
  rfl

omit [Coded α] in
theorem collection_histogram {K : Code α} {V : Set (List α)}
    {C : Threading V (Fin K.1.length)} (h : Represents K C) (closed : SubstringClosed V)
    (s : List α) :
    Fintype.card (Family.Occurrence (collection h closed).layerAt s) =
      (Finset.univ.filter (fun i => s <+: C.word i)).card := by
  classical
  rw [Fintype.card_eq_nat_card, Nat.card_sigma]
  simp only [Fintype.sum_sigma]
  simp only [← Fintype.card_eq_nat_card, Layer.Occurrence, Fintype.card_subtype,
    Finset.card_filter]
  rw [← (allPhaseEquiv h).sum_comp (fun i => if s <+: C.word i then 1 else 0)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro g _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have hp := phase_prefix_count h g r s
  simp only [Finset.card_filter] at hp
  simp only [Layer.records_iff_prefix, collection, LayerCollection.layerAt,
    Threading.layer]
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1

end Superstring.ThreadArray


namespace Superstring.Hierarchical.LayerCollection
open Counts
variable {α G : Type} [Fintype G] {V : Set (List α)} (C : LayerCollection V G)

omit [Fintype G] in
theorem eq_of_alignment (g h : G) (r t : ℤ)
    (halign : ∀ x, C.text h (x+r) = C.text g (x+t)) : h = g := by
  by_contra hne
  apply C.different h g hne (t-r)
  funext x
  convert halign (x-r) using 1 <;> congr 1 <;> omega

abbrev AlignedOccurrence (g : G) (t : ℤ) (s : List α) :=
  {o : Family.Occurrence C.layerAt s // ∀ x : ℤ, C.text o.1.1 (x+o.2.val.val) = C.text g (x+t)}

noncomputable instance (g : G) (t : ℤ) (s : List α) : Fintype (C.AlignedOccurrence g t s) := by
  classical
  exact inferInstanceAs (Fintype {o : Family.Occurrence C.layerAt s //
    ∀ x : ℤ, C.text o.1.1 (x+o.2.val.val) = C.text g (x+t)})

noncomputable def qualifyingLayer (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (t : ℤ) (s : List α) (o : C.AlignedOccurrence g t s) :
    {j : Fin (C.size g) // t + s.length ≤ (C.layer g j).last t} := by
  rcases o with ⟨⟨⟨h,j⟩,r⟩,ha⟩
  have hh := C.eq_of_alignment g h r.val.val t ha
  subst h
  exact ⟨j, ((C.layer g j).records_at_alignment (prim g) r.property ha).2⟩

omit [Fintype G] in
theorem qualifyingLayer_injective (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (t : ℤ) (s : List α) : Function.Injective (C.qualifyingLayer prim g t s) := by
  rintro ⟨⟨⟨h,j⟩,r⟩,hr⟩ ⟨⟨⟨h',j'⟩,r'⟩,hr'⟩ he
  have hh := C.eq_of_alignment g h r.val.val t hr
  have hh' := C.eq_of_alignment g h' r'.val.val t hr'
  subst h; subst h'
  have hj : j = j' := congrArg Subtype.val he
  subst j'
  have hphase : r.val = r'.val := by
    apply Fin.ext
    have hh := (prim g).alignment_unique
      (by omega : 0 ≤ (r.val.val : ℤ)) (by exact_mod_cast r.val.isLt)
      (by omega : 0 ≤ (r'.val.val : ℤ)) (by exact_mod_cast r'.val.isLt)
      (fun x => (hr x).trans (hr' x).symm)
    omega
  have hre : r = r' := Subtype.ext hphase
  subst r'
  rfl

theorem aligned_card_le_qualifying (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (t : ℤ) (s : List α) :
    Nat.card (C.AlignedOccurrence g t s) ≤
      Nat.card {j : Fin (C.size g) // t + s.length ≤ (C.layer g j).last t} := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective (C.qualifyingLayer prim g t s)
      (C.qualifyingLayer_injective prim g t s)

variable [DecidableEq α] [Inhabited α]

 theorem blocking_count (D : Data α)
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    (A : ℤ → α) (s : List α) :
    blocking D.vertices A s (fun r => Fintype.card (Family.Occurrence C.layerAt r)) =
      blocking D.vertices A s D.count := by
  apply blocking_congr
  intro r _hr hlen
  apply hist r
  intro he
  simp only [he, List.length_nil] at hlen
  omega

theorem period_forces_matching (D : Data α) (hD : D.WellFormed)
    (hvtx : V = (D.vertices : Set (List α)))
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    {A : ℤ → α} {w v : List α} {p k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hper : Function.Periodic A (p : ℤ))
    (hw : w ∈ D.vertices) (hwne : w ≠ []) (hv : v ∈ D.vertices)
    (hmv : Matches A v) (hmw : Matches A w)
    (hlen : w.length + k * p = v.length)
    (ov : Family.Occurrence (C.layerAt) v)
    (halign : ∀ x : ℤ, C.text ov.1.1 (x + ov.2.val.val) = A x)
    (hfew : Nat.card {o : Family.Occurrence (C.layerAt) w //
      ∀ x : ℤ, C.text o.1.1 (x + o.2.val.val) = A x} ≤ k) :
    ∃ o : Family.Occurrence (C.layerAt) w,
      (¬ ∀ x : ℤ, C.text o.1.1 (x + o.2.val.val) = A x) ∧
      ∃ a b : ℤ, a ≤ o.2.val.val ∧ (o.2.val.val : ℤ) + w.length ≤ b ∧
        (C.layerAt o.1).first a ≤ b ∧
        b ≤ (C.layerAt o.1).last a ∧
        AgreeOn (C.text o.1.1) (fun x => A (x - o.2.val.val)) a b := by
  have hvne : v ≠ [] := by
    intro he
    have hwpos := List.length_pos_iff.mpr hwne
    simp only [he, List.length_nil] at hlen
    omega
  have pos := fun i : C.Id =>
    (C.positive i.1)
  have per := fun i : C.Id =>
    (C.periodic i.1)
  have ht := Family.blocking_lt_of_aligned (C.layerAt)
    pos per D.vertices ov halign
  rw [C.blocking_count D hist, hist v hvne] at ht
  have hexcess := D.period_rule hp hk hper hw hwne hv hmv hmw hlen ht
  apply Family.matching_different (C.layerAt)
    pos per D.vertices hvtx (by simpa only [hvtx] using hD.closed) hmw k _ hfew
  rw [C.blocking_count D hist, hist w hwne]
  omega


theorem hard_case_record (D : Data α) (hD : D.WellFormed)
    (hvtx : V = (D.vertices : Set (List α)))
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    (prim : ∀ g, Primitive (C.text g) (C.period g))
    (g : G) (j : Fin (C.size g)) (t : ℤ) (k : ℕ) (hk : 0 < k)
    (hhard : t + (k * C.period g : ℕ) < (C.layer g j).first t)
    (hfew : (Processing.qualifying (fun l => (C.layer g l).last t)
      ((C.layer g j).first t) (C.period g) k).card ≤ k) :
    ∃ i : C.Id, ∃ R : (C.layerAt i).Record (C.text g),
      R.start ≤ t ∧ (C.layer g j).first t - (k * C.period g : ℕ) ≤ R.stop ∧
      C.text g ≠ (fun x => C.text i.1 (x+R.offset)) ∧
      R.stop - R.start < C.period g + C.period i.1 ∧
      (i.1 = g → R.stop - R.start < C.period g) := by
  classical
  let A := C.text g
  let p := C.period g
  let L := C.layerAt ⟨g, j⟩
  let H := L.first t
  let v := textWord A t H
  let w := textWord A t (H - (k * p : ℕ))
  have hp : 0 < p := (prim g).positive
  have per : Function.Periodic A (p : ℤ) := (prim g).periodic
  change t + (k * p : ℕ) < H at hhard
  have hv : v ∈ D.vertices := by
    have hh := L.first_actual t
    exact (Set.ext_iff.mp hvtx v).mp hh
  have hw : w ∈ D.vertices := hD.closed hv (textWord_infix A le_rfl
    (by omega : t ≤ H - (k * p : ℕ)) (by omega))
  have hwlen : t + (w.length : ℤ) = H - (k * p : ℕ) := by
    dsimp only [w]
    rw [length_textWord]
    omega
  have hvlen : t + (v.length : ℤ) = H := by
    dsimp only [v]
    rw [length_textWord]
    omega
  have hwne : w ≠ [] := by
    intro he
    simp only [he, List.length_nil, Nat.cast_zero, add_zero] at hwlen
    omega
  have hlen : w.length + k * p = v.length := by omega
  have hvrec : L.Records v t := ⟨TextOccurs.word A t H, by
    rw [hvlen]
    exact L.first_le_last t⟩
  let ov : Family.Occurrence (C.layerAt) v :=
    ⟨⟨g, j⟩, L.normalize hp per hvrec⟩
  have halign : ∀ x, C.text ov.1.1 (x + ov.2.val.val) = A (x + t) :=
    L.normalize_alignment hp per hvrec
  have hmv : Matches (fun x => A (x + t)) v := by
    intro i
    simpa only [add_comm] using (TextOccurs.word A t H i)
  have hmw : Matches (fun x => A (x + t)) w := by
    intro i
    simpa only [add_comm] using (TextOccurs.word A t (H - (k * p : ℕ)) i)
  have hper : Function.Periodic (fun x => A (x + t)) (p : ℤ) := by
    intro x
    simpa only [add_right_comm] using per (x + t)
  have hcard : Nat.card {l : Fin (C.size g) //
      t + w.length ≤ (C.layer g l).last t} ≤ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    change (Processing.qualifying (fun l => (C.layer g l).last t) H p k).card ≤ k at hfew
    simpa only [hwlen, Processing.qualifying] using hfew
  have hAligned : Nat.card (C.AlignedOccurrence g t w) ≤ k :=
    (C.aligned_card_le_qualifying prim g t w).trans hcard
  obtain ⟨o, hdiff, a, b, har, hrb, hfa, hbl, hagree⟩ :=
    C.period_forces_matching D hD hvtx hist hp hk hper hw hwne hv hmv hmw hlen ov halign hAligned
  let c : ℤ := o.2.val.val - t
  let R : (C.layerAt o.1).Record A := {
    offset := c
    start := a - c
    stop := b - c
    first_le := by simpa only [sub_add_cancel] using hfa
    le_last := by simpa only [sub_add_cancel] using hbl
    agree := by
      intro x hax hxb
      have hh := hagree (x + c) (by omega) (by omega)
      change C.text o.1.1 (x + c) = A (x + c - o.2.val.val + t) at hh
      have he : x + c - (o.2.val.val : ℤ) + t = x := by dsimp only [c]; omega
      rw [he] at hh
      exact hh.symm }
  have hd : A ≠ fun x => C.text o.1.1 (x + R.offset) := by
    intro he
    apply hdiff
    intro x
    have hh := congrFun he (x + t)
    change A (x + t) = C.text o.1.1 (x + t + c) at hh
    have hc : x + t + c = x + (o.2.val.val : ℤ) := by dsimp only [c]; omega
    rw [hc] at hh
    exact hh.symm
  refine ⟨o.1, R, ?_, ?_, hd,
    R.length_lt hp (prim o.1.1).positive per
      (prim o.1.1).periodic hd, ?_⟩
  · change a - c ≤ t
    dsimp only [c]
    omega
  · change H - (k * p : ℕ) ≤ b - c
    dsimp only [c]
    omega
  · intro he
    apply R.same_period_length_lt hp per _ hd
    simpa only [he] using (prim o.1.1).periodic


theorem recordSupply_of_histogram (D : Data α) (hD : D.WellFormed)
    (hvtx : V = (D.vertices : Set (List α)))
    (hist : ∀ s, s ≠ [] → Fintype.card (Family.Occurrence C.layerAt s) = D.count s)
    (prim : ∀ g, Primitive (C.text g) (C.period g)) : C.RecordSupply := by
  intro g j t k hk hh hs
  obtain ⟨d,R,ha,hb,hd,_⟩ := C.hard_case_record D hD hvtx hist prim g j t k hk hh hs
  exact ⟨d,R,ha,hb,hd⟩

end Superstring.Hierarchical.LayerCollection


namespace Superstring.Hierarchical.Layer.Record
variable {α : Type} {V : Set (List α)} {A B : ℤ → α} {q : ℕ} {D : Layer V B q}

/-- Only the period residue of a recipient offset is stored. -/
def normalize (R : D.Record A) (per : Function.Periodic B (q : ℤ)) : D.Record A where
  offset := R.offset % q
  start := R.start
  stop := R.stop
  first_le := by
    have he : R.start + R.offset = R.start + R.offset % q + (R.offset / q) * q := by have := Int.emod_add_ediv_mul R.offset (q : ℤ); omega
    have hh := R.first_le
    rw [he,D.first_shift_int] at hh
    have := Int.emod_add_ediv_mul R.offset (q : ℤ)
    omega
  le_last := by
    have he : R.start + R.offset = R.start + R.offset % q + (R.offset / q) * q := by have := Int.emod_add_ediv_mul R.offset (q : ℤ); omega
    have hh := R.le_last
    change R.stop + R.offset ≤ D.z (R.start + R.offset) at hh
    rw [he,D.shift_int] at hh
    change R.stop + R.offset % q ≤ D.z (R.start + R.offset % q)
    have := Int.emod_add_ediv_mul R.offset (q : ℤ)
    omega
  agree := by
    intro x hx hy
    have he : B (x + R.offset % q) = B (x + R.offset) := by
      have ht := per.int_mul (R.offset / q) (x + R.offset % q)
      simp only [Int.cast_id] at ht
      convert ht.symm using 1
      congr 1
      have := Int.emod_add_ediv_mul R.offset (q : ℤ)
      omega
    exact (R.agree x hx hy).trans he.symm

theorem normalize_text (R : D.Record A) (per : Function.Periodic B (q : ℤ)) :
    (fun x => B (x + (R.normalize per).offset)) = fun x => B (x + R.offset) := by
  funext x
  have ht := per.int_mul (R.offset / q) (x + R.offset % q)
  simp only [Int.cast_id] at ht
  change B (x + R.offset % q) = B (x + R.offset)
  convert ht.symm using 1
  congr 1
  have := Int.emod_add_ediv_mul R.offset (q : ℤ)
  omega

theorem bounds (R : D.Record A) {t : ℤ} {M : ℕ} (ha : R.start ≤ t) (hb : t < R.stop)
    (len : ∀ w ∈ V, w.length ≤ M) :
    t - M ≤ R.start ∧ R.stop ≤ t + M := by
  have hm := len _ R.word_mem
  rw [length_textWord] at hm
  have hs := R.start_le_stop
  omega
end Superstring.Hierarchical.Layer.Record

namespace Superstring.RecordCode
open BitCode Hierarchical LayerArray
variable {α : Type} [Inhabited α] [DecidableEq α]

abbrev Code := ℤ × ℤ × ℤ
def offset (R : Code) : ℤ := R.1
def start (R : Code) : ℤ := R.2.1
def stop (R : Code) : ℤ := R.2.2

def check (U T : List α) (Z : List ℕ) (R : Code) : Bool :=
  decide (GeoCode.exit Z (start R + offset R - 1) ≤ stop R + offset R) &&
  decide (stop R + offset R ≤ GeoCode.exit Z (start R + offset R)) &&
  decide (start R ≤ stop R) &&
  equal (PeriodWord.window U (start R) (stop R))
    (PeriodWord.window T (start R + offset R) (stop R + offset R))

 theorem check_record {V : Set (List α)} {A B : ℤ → α} {q : ℕ}
    {S T : List α} {Z : List ℕ} {L : Layer V B q}
    (hS : PeriodWord.text S = A) (hL : Represents T Z L) (R : L.Record A) :
    check S T Z (R.offset,R.start,R.stop) = true := by
  simp only [check,offset,start,stop,PeriodWord.window_eq,hS,hL.text_eq,hL.exit_eq]
  have hh := R.word_eq
  simp only [Bool.and_eq_true,BitCode.equal,decide_eq_true_eq]
  exact ⟨⟨⟨R.first_le,R.le_last⟩,decide_eq_true R.start_le_stop⟩,hh⟩

variable [Coded α]
@[fun_prop] theorem poly_check : Poly (fun q : (List α × List α × List ℕ) × Code =>
    check q.1.1 q.1.2.1 q.1.2.2 q.2) := by
  unfold check start stop offset
  fun_prop
end Superstring.RecordCode

namespace Superstring.RecordCode
open BitCode Hierarchical LayerArray
variable {α : Type} [Inhabited α] [DecidableEq α]

omit [Inhabited α] [DecidableEq α] in
theorem agree_of_word_eq {A B : ℤ → α} {a b : ℤ}
    (he : textWord A a b = textWord B a b) : AgreeOn A B a b := by
  intro x hx hb
  have hi : (x-a).toNat < (b-a).toNat := by omega
  have ha : a + ((x-a).toNat : ℤ) = x := by omega
  have ht := congrArg (fun w : List α => w[(x-a).toNat]?) he
  simp only [textWord,List.getElem?_ofFn,hi,↓reduceDIte,Option.some.injEq] at ht
  simpa only [ha] using ht

def checkedRecord {V : Set (List α)} {A B : ℤ → α} {q : ℕ}
    {S T : List α} {Z : List ℕ} {L : Layer V B q}
    (hS : PeriodWord.text S = A) (hL : Represents T Z L) (R : Code)
    (h : check S T Z R = true) : L.Record A := by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq,BitCode.equal,PeriodWord.window_eq,
    hS,hL.text_eq,hL.exit_eq] at h
  exact ⟨offset R,start R,stop R,h.1.1.1,h.1.1.2,
    agree_of_word_eq (h.2.trans (textWord_reindex B (offset R) (start R) (stop R)).symm)⟩

def pool (q M : ℕ) (t : ℤ) : List Code :=
  ((List.range q).product ((List.range (M+1)).product (List.range M))).map
    (fun r => ((r.1 : ℤ),t-M+r.2.1,t+1+r.2.2))

theorem mem_pool {q M : ℕ} {t : ℤ} {R : Code}
    (ho : 0 ≤ offset R) (hoq : offset R < q)
    (ha : t-M ≤ start R) (hat : start R ≤ t)
    (hb : t < stop R) (hbt : stop R ≤ t+M) : R ∈ pool q M t := by
  apply List.mem_map.mpr
  refine ⟨((offset R).toNat,((start R-t+M).toNat,(stop R-t-1).toNat)),?_,?_⟩
  · exact List.mem_product.mpr ⟨List.mem_range.mpr (by omega),
      List.mem_product.mpr ⟨List.mem_range.mpr (by omega),List.mem_range.mpr (by omega)⟩⟩
  · rcases R with ⟨o,a,b⟩
    simp only [offset,start,stop] at *
    apply Prod.ext
    · simp only [Int.toNat_of_nonneg ho]
    · apply Prod.ext
      · change t - M + ((a-t+M).toNat : ℤ) = a
        omega
      · change t + 1 + ((b-t-1).toNat : ℤ) = b
        omega

omit [Inhabited α] [DecidableEq α] in
theorem normalized_mem_pool {V : Set (List α)} {A B : ℤ → α} {q : ℕ}
    {L : Layer V B q} (hq : 0 < q) (per : Function.Periodic B (q : ℤ))
    (R : L.Record A) {t : ℤ} {M : ℕ} (ha : R.start ≤ t) (hb : t < R.stop)
    (len : ∀ w ∈ V, w.length ≤ M) :
    ((R.normalize per).offset,R.start,R.stop) ∈ pool q M t := by
  obtain ⟨hlo,hhi⟩ := R.bounds ha hb len
  exact mem_pool (Int.emod_nonneg _ (by omega)) (Int.emod_lt_of_pos _ (by omega))
    hlo ha hb hhi

variable [Coded α]
@[fun_prop] theorem poly_pool : Poly (fun q : ℕ × ℕ × ℤ => pool q.1 q.2.1 q.2.2) := by
  unfold pool
  exact BitCode.Poly.mapFn
    (f := fun q : (ℕ × ℕ × ℤ) × (ℕ × ℕ × ℕ) =>
      ((q.2.1 : ℤ),q.1.2.2-q.1.2.1+q.2.2.1,q.1.2.2+1+q.2.2.2))
    (by fun_prop) (by fun_prop)
end Superstring.RecordCode

end OAI
