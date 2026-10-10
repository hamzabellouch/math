import OAI.Computability.Superstring.Counting

namespace OAI

namespace Superstring

namespace Hierarchical.Threading

variable {α ι : Type} [Fintype ι] {V : Set (List α)}

/-- Stable IDs for every sorted primitive layer of the exact base threading. -/
abbrev LayerId (C : Threading V ι) :=
  Σ g : C.Groups, Fin (Fintype.card (C.Aligned (C.groupText g)))

noncomputable def layerAt (C : Threading V ι) (closed : SubstringClosed V)
    (i : C.LayerId) : Layer V (C.groupText i.1) (C.groupPeriod i.1) :=
  C.layer closed (C.primitive_group i.1).periodic i.2

/-- Reordering a phase and a stable layer ID does not alter the recorded words. -/
noncomputable def occurrenceEquiv (C : Threading V ι) (closed : SubstringClosed V)
    (s : List α) : Family.Occurrence (C.layerAt closed) s ≃ C.Recorded s where
  toFun o := ⟨⟨o.1.1, o.2.val, o.1.2⟩,
    ((C.layerAt closed o.1).records_iff_prefix s o.2.val.val).mp o.2.property⟩
  invFun o := ⟨⟨o.val.1, o.val.2.2⟩, ⟨o.val.2.1,
    ((C.layerAt closed ⟨o.val.1, o.val.2.2⟩).records_iff_prefix s o.val.2.1.val).mpr
      o.property⟩⟩
  left_inv := by rintro ⟨⟨g, j⟩, ⟨r, hr⟩⟩; rfl
  right_inv := by rintro ⟨⟨g, r, j⟩, hr⟩; rfl

end Hierarchical.Threading

namespace Hierarchical.Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Moving a recorded occurrence to any identical full-text alignment preserves
its exact exit-end test. Primitivity, not just periodicity, is essential here. -/
theorem records_at_alignment (D : Layer V A p) (hp : Primitive A p)
    {s : List α} {r t : ℤ} (hr : D.Records s r)
    (halign : ∀ x, A (x + r) = A (x + t)) : D.Records s t := by
  have hper : Function.Periodic A (t - r) := by
    intro x
    have hh := (halign (x - r)).symm
    convert hh using 1 <;> congr 1 <;> omega
  obtain ⟨m, hm⟩ := (hp.period_iff_dvd (t - r)).mp hper
  have he : r + m * p = t := by rw [mul_comm]; omega
  exact he ▸ D.records_shift hp.periodic hr m

end Hierarchical.Layer

namespace Hierarchical.Threading

variable {α ι : Type} [Fintype ι] {V : Set (List α)}

omit [Fintype ι] in
/-- Identical aligned infinite texts necessarily belong to the same primitive
text group; no finite-word coincidence is substituted for this condition. -/
theorem group_eq_of_alignment (C : Threading V ι) (g h : C.Groups) (r t : ℤ)
    (halign : ∀ x, C.groupText h (x + r) = C.groupText g (x + t)) : h = g := by
  have he : C.group (Quotient.out h) = C.group (Quotient.out g) := by
    apply Quotient.sound
    refine ⟨r - t, ?_⟩
    intro x
    have hh := halign (x - t)
    convert hh using 1 <;> congr 1 <;> omega
  exact (Quotient.out_eq h).symm.trans (he.trans (Quotient.out_eq g))

abbrev AlignedOccurrence (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) :=
  {o : Family.Occurrence (C.layerAt closed) s //
    ∀ x : ℤ, C.groupText o.1.1 (x + o.2.val.val) = C.groupText g (x + t)}

noncomputable instance (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) : Fintype (C.AlignedOccurrence closed g t s) := by
  classical
  exact inferInstanceAs (Fintype {o : Family.Occurrence (C.layerAt closed) s //
    ∀ x : ℤ, C.groupText o.1.1 (x + o.2.val.val) = C.groupText g (x + t)})

/-- Forgetting the unique aligned residue retains a qualifying sorted layer. -/
noncomputable def qualifyingLayer (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) (o : C.AlignedOccurrence closed g t s) :
    {j : Fin (Fintype.card (C.Aligned (C.groupText g))) //
      t + s.length ≤ C.sortedExit (C.groupText g) j t} := by
  rcases o with ⟨⟨⟨h, j⟩, r⟩, halign⟩
  have hg := C.group_eq_of_alignment g h r.val.val t halign
  subst h
  exact ⟨j, ((C.layerAt closed ⟨g, j⟩).records_at_alignment (C.primitive_group g)
    r.property halign).2⟩

theorem qualifyingLayer_injective (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) :
    Function.Injective (C.qualifyingLayer closed g t s) := by
  rintro ⟨⟨⟨h, j⟩, r⟩, hr⟩ ⟨⟨⟨h', j'⟩, r'⟩, hr'⟩ he
  have hh := C.group_eq_of_alignment g h r.val.val t hr
  have hh' := C.group_eq_of_alignment g h' r'.val.val t hr'
  subst h
  subst h'
  have hj : j = j' := congrArg Subtype.val he
  subst j'
  have hphase : r.val = r'.val := by
    apply Fin.ext
    have hh := (C.primitive_group g).alignment_unique
      (by omega : 0 ≤ (r.val.val : ℤ)) (by exact_mod_cast r.val.isLt)
      (by omega : 0 ≤ (r'.val.val : ℤ)) (by exact_mod_cast r'.val.isLt)
      (fun x => (hr x).trans (hr' x).symm)
    omega
  have hre : r = r' := Subtype.ext hphase
  subst r'
  rfl


theorem aligned_card_le_qualifying (C : Threading V ι) (closed : SubstringClosed V)
    (g : C.Groups) (t : ℤ) (s : List α) :
    Nat.card (C.AlignedOccurrence closed g t s) ≤
      Nat.card {j : Fin (Fintype.card (C.Aligned (C.groupText g))) //
        t + s.length ≤ C.sortedExit (C.groupText g) j t} := by
  classical
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective (C.qualifyingLayer closed g t s)
      (C.qualifyingLayer_injective closed g t s)

end Hierarchical.Threading

namespace Hierarchical.Processing

/-- The occurrence count tested when choosing a layer. -/
def qualifying {m : ℕ} (z : Fin m → ℤ) (H : ℤ) (p k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => H - (k * p : ℕ) ≤ z j)

theorem qualifying_bound {m : ℕ} (z : Fin m → ℤ) (hz : Monotone z)
    (H : ℤ) (p k : ℕ) (j : Fin m) (hj : z j < H - (k * p : ℕ)) :
    (qualifying z H p k).card ≤ m - 1 - j.val := by
  have hsub : qualifying z H p k ⊆ Finset.Ioi j := by
    intro i hi
    simp only [qualifying, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply Finset.mem_Ioi.mpr
    by_contra h
    have hh := hz (le_of_not_gt h)
    omega
  exact (Finset.card_le_card hsub).trans_eq (Fin.card_Ioi j)

/-- The first failed test exists by the number of still available upper layers;
the sharp-band bound comes from the previous, successful, integer test. -/
theorem choose_k {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (z : Fin m → ℤ) (hz : Monotone z) (H : ℤ) (p : ℕ)
    (hH : H ≤ z ⟨m - 1, by omega⟩)
    (hstop : (qualifying z H p n).card ≤ n) :
    ∃ (k : ℕ) (hk : 0 < k) (hkn : k ≤ n),
      (qualifying z H p k).card ≤ k ∧
      H - ((k - 1) * p : ℕ) ≤ z ⟨m - k, by omega⟩ := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ (qualifying z H p k).card ≤ k := ⟨n, hn, hstop⟩
  let k := Nat.find hex
  have hspec : 0 < k ∧ (qualifying z H p k).card ≤ k := Nat.find_spec hex
  have hkn : k ≤ n := Nat.find_min' hex ⟨hn, hstop⟩
  refine ⟨k, hspec.1, hkn, hspec.2, ?_⟩
  by_cases hk1 : k = 1
  · simp only [hk1, Nat.sub_self, Nat.zero_mul, Nat.cast_zero, sub_zero]
    exact hH
  · have hprev : k - 1 < (qualifying z H p (k - 1)).card := by
      have hh := Nat.find_min hex (show k - 1 < k by omega)
      have hkprev : 0 < k - 1 := by omega
      exact lt_of_not_ge (fun he => hh ⟨hkprev, he⟩)
    by_contra hsharp
    have hh := qualifying_bound z hz H p (k - 1) ⟨m - k, by omega⟩
      (lt_of_not_ge hsharp)
    change (qualifying z H p (k - 1)).card ≤ m - 1 - (m - k) at hh
    omega


theorem wide_band {α : Type} {V : Set (List α)} {A : ℤ → α} {p k : ℕ}
    (H L : Layer V A p) (hp : 0 < p) (hk : 0 < k) (t : ℤ)
    (hsharp : H.first t - L.last t ≤ ((k - 1) * p : ℕ)) :
    ∀ x : ℤ, H.first x - L.last x ≤ (k * p : ℕ) := by
  intro x
  let r := (t - x) % (p : ℤ)
  let q := (t - x) / (p : ℤ)
  let y := t - r
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrp : r < p := Int.emod_lt_of_pos _ (by omega)
  have hyt : y ≤ t := by dsimp only [y]; omega
  have hty : t ≤ y + p := by dsimp only [y]; omega
  have he : x + q * p = y := by
    have hdiv := Int.emod_add_ediv_mul (t - x) (p : ℤ)
    dsimp only [r, q, y]
    omega
  have hH := H.first_mono hyt
  have hL := L.last_mono hty
  have hLshift : L.last (y + p) = L.last y + p := L.shift y
  rw [hLshift] at hL
  have hHx := H.first_shift_int q x
  have hLx := L.shift_int q x
  rw [he] at hHx hLx
  change L.last y = L.last x + q * p at hLx
  have hprod : ((k - 1) * p : ℕ) + p = k * p := by
    calc
      (k - 1) * p + p = (k - 1) * p + 1 * p := by rw [one_mul]
      _ = (k - 1 + 1) * p := (Nat.add_mul _ _ _).symm
      _ = k * p := by rw [Nat.sub_add_cancel hk]
  have hprod' : (((k - 1) * p : ℕ) : ℤ) + p = (k * p : ℕ) := by exact_mod_cast hprod
  omega

end Hierarchical.Processing

namespace Hierarchical.Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

theorem normalize_alignment (D : Layer V A p) (hp : 0 < p)
    (per : Function.Periodic A (p : ℤ)) {s : List α} {t : ℤ}
    (h : D.Records s t) :
    ∀ x, A (x + (D.normalize hp per h).val.val) = A (x + t) := by
  intro x
  rw [D.normalize_val hp per h]
  have hh := per.int_mul (t / (p : ℤ)) (x + t % (p : ℤ))
  have he := Int.emod_add_ediv_mul t (p : ℤ)
  simp only [Int.cast_id] at hh
  have he' : x + t % (p : ℤ) + t / (p : ℤ) * p = x + t := by omega
  rw [he'] at hh
  exact hh.symm

end Hierarchical.Layer

namespace Counts.Data

open Hierarchical
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem family_occurrence_count (D : Data α) (hD : D.WellFormed) {s : List α}
    (hs : s ≠ []) :
    Fintype.card (Family.Occurrence ((D.threading hD).layerAt hD.closed) s) =
      D.count s := by
  rw [Fintype.card_congr ((D.threading hD).occurrenceEquiv hD.closed s)]
  exact D.recorded_count hD hs

/-- Empty recorded words do not disturb this identity: every positive blocking
coefficient has a strictly longer, hence nonempty, bracketing word. -/
theorem blocking_layer_count (D : Data α) (hD : D.WellFormed)
    (A : ℤ → α) (s : List α) :
    blocking D.vertices A s
      (fun r => Fintype.card (Family.Occurrence ((D.threading hD).layerAt hD.closed) r)) =
      blocking D.vertices A s D.count := by
  apply blocking_congr
  intro r _hr hlen
  apply D.family_occurrence_count hD
  intro he
  simp only [he, List.length_nil] at hlen
  omega

/-- The exact period rule plus the exact base-layer histogram forces a genuine
matching record with a different aligned bi-infinite text. -/
theorem period_forces_matching (D : Data α) (hD : D.WellFormed)
    {A : ℤ → α} {w v : List α} {p k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hper : Function.Periodic A (p : ℤ))
    (hw : w ∈ D.vertices) (hwne : w ≠ []) (hv : v ∈ D.vertices)
    (hmv : Matches A v) (hmw : Matches A w)
    (hlen : w.length + k * p = v.length)
    (ov : Family.Occurrence ((D.threading hD).layerAt hD.closed) v)
    (halign : ∀ x : ℤ, (D.threading hD).groupText ov.1.1 (x + ov.2.val.val) = A x)
    (hfew : Nat.card {o : Family.Occurrence ((D.threading hD).layerAt hD.closed) w //
      ∀ x : ℤ, (D.threading hD).groupText o.1.1 (x + o.2.val.val) = A x} ≤ k) :
    ∃ o : Family.Occurrence ((D.threading hD).layerAt hD.closed) w,
      (¬ ∀ x : ℤ, (D.threading hD).groupText o.1.1 (x + o.2.val.val) = A x) ∧
      ∃ a b : ℤ, a ≤ o.2.val.val ∧ (o.2.val.val : ℤ) + w.length ≤ b ∧
        ((D.threading hD).layerAt hD.closed o.1).first a ≤ b ∧
        b ≤ ((D.threading hD).layerAt hD.closed o.1).last a ∧
        AgreeOn ((D.threading hD).groupText o.1.1) (fun x => A (x - o.2.val.val)) a b := by
  have hvne : v ≠ [] := by
    intro he
    have hwpos := List.length_pos_iff.mpr hwne
    simp only [he, List.length_nil] at hlen
    omega
  have pos := fun i : (D.threading hD).LayerId =>
    ((D.threading hD).primitive_group i.1).positive
  have per := fun i : (D.threading hD).LayerId =>
    ((D.threading hD).primitive_group i.1).periodic
  have ht := Family.blocking_lt_of_aligned ((D.threading hD).layerAt hD.closed)
    pos per D.vertices ov halign
  rw [D.blocking_layer_count hD, D.family_occurrence_count hD hvne] at ht
  have hexcess := D.period_rule hp hk hper hw hwne hv hmv hmw hlen ht
  apply Family.matching_different ((D.threading hD).layerAt hD.closed)
    pos per D.vertices rfl hD.closed hmw k _ hfew
  rw [D.blocking_layer_count hD, D.family_occurrence_count hD hwne]
  omega

end Counts.Data

namespace Hierarchical

variable {α : Type}

/-- Reindexing a text changes coordinates, never the represented graph word. -/
theorem textWord_reindex (A : ℤ → α) (c a b : ℤ) :
    textWord (fun x => A (x + c)) a b = textWord A (a + c) (b + c) := by
  apply List.ext_getElem
  · simp only [length_textWord]
    congr 1
    omega
  · intro i hi hj
    simp only [textWord, List.getElem_ofFn]
    congr 1
    omega

namespace Layer

variable {V : Set (List α)} {A B : ℤ → α} {p q : ℕ}


structure Record (D : Layer V B q) (A : ℤ → α) where
  offset : ℤ
  start : ℤ
  stop : ℤ
  first_le : D.first (start + offset) ≤ stop + offset
  le_last : stop + offset ≤ D.last (start + offset)
  agree : AgreeOn A (fun x => B (x + offset)) start stop

namespace Record

variable {D : Layer V B q} (R : D.Record A)

theorem start_le_stop : R.start ≤ R.stop := by
  have hh := D.start_le_first (R.start + R.offset)
  have hh' := R.first_le
  omega

theorem word_eq : textWord A R.start R.stop =
    textWord B (R.start + R.offset) (R.stop + R.offset) :=
  (textWord_eq_of_agree R.agree).trans (textWord_reindex B R.offset R.start R.stop)

theorem word_mem : textWord A R.start R.stop ∈ V :=
  R.word_eq ▸ D.actual (R.start + R.offset) (R.stop + R.offset) R.first_le R.le_last

theorem touched {s t : List α} (P : Path V s t)
    (hv : P.Visits (textWord A R.start R.stop)) : D.TouchedBy P := by
  refine ⟨R.start + R.offset, R.stop + R.offset, R.first_le, R.le_last, ?_⟩
  rwa [R.word_eq] at hv

theorem length_lt (hp : 0 < p) (hq : 0 < q)
    (hA : Function.Periodic A (p : ℤ)) (hB : Function.Periodic B (q : ℤ))
    (hdiff : A ≠ fun x => B (x + R.offset)) : R.stop - R.start < p + q := by
  apply agreement_bound A (fun x => B (x + R.offset)) p q hp hq hA _ hdiff
    R.start R.stop R.agree
  intro x
  simpa only [add_right_comm] using hB (x + R.offset)

theorem same_period_length_lt (hp : 0 < p)
    (hA : Function.Periodic A (p : ℤ)) (hB : Function.Periodic B (p : ℤ))
    (hdiff : A ≠ fun x => B (x + R.offset)) : R.stop - R.start < p := by
  apply same_period_agreement_bound A (fun x => B (x + R.offset)) p hp hA _ hdiff
    R.start R.stop R.agree
  intro x
  simpa only [add_right_comm] using hB (x + R.offset)

end Record
end Layer
end Hierarchical

namespace Counts.Data

open Hierarchical
variable {α : Type} [DecidableEq α] [Inhabited α]


theorem hard_case_record (D : Data α) (hD : D.WellFormed)
    (g : (D.threading hD).Groups)
    (j : Fin (Fintype.card ((D.threading hD).Aligned ((D.threading hD).groupText g))))
    (t : ℤ) (k : ℕ) (hk : 0 < k)
    (hhard : t + (k * (D.threading hD).groupPeriod g : ℕ) <
      ((D.threading hD).layerAt hD.closed ⟨g, j⟩).first t)
    (hfew : (Processing.qualifying
      (fun l => (D.threading hD).sortedExit ((D.threading hD).groupText g) l t)
      (((D.threading hD).layerAt hD.closed ⟨g, j⟩).first t)
      ((D.threading hD).groupPeriod g) k).card ≤ k) :
    ∃ i : (D.threading hD).LayerId,
      ∃ R : ((D.threading hD).layerAt hD.closed i).Record ((D.threading hD).groupText g),
        R.start ≤ t ∧
        ((D.threading hD).layerAt hD.closed ⟨g, j⟩).first t -
          (k * (D.threading hD).groupPeriod g : ℕ) ≤ R.stop ∧
        ((D.threading hD).groupText g ≠
          fun x => (D.threading hD).groupText i.1 (x + R.offset)) ∧
        R.stop - R.start < (D.threading hD).groupPeriod g + (D.threading hD).groupPeriod i.1 ∧
        (i.1 = g → R.stop - R.start < (D.threading hD).groupPeriod g) := by
  classical
  let C := D.threading hD
  let A := C.groupText g
  let p := C.groupPeriod g
  let L := C.layerAt hD.closed ⟨g, j⟩
  let H := L.first t
  let v := textWord A t H
  let w := textWord A t (H - (k * p : ℕ))
  have hp : 0 < p := (C.primitive_group g).positive
  have per : Function.Periodic A (p : ℤ) := (C.primitive_group g).periodic
  change t + (k * p : ℕ) < H at hhard
  have hv : v ∈ D.vertices := L.first_actual t
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
  let ov : Family.Occurrence (C.layerAt hD.closed) v :=
    ⟨⟨g, j⟩, L.normalize hp per hvrec⟩
  have halign : ∀ x, C.groupText ov.1.1 (x + ov.2.val.val) = A (x + t) :=
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
  have hcard : Nat.card {l : Fin (Fintype.card (C.Aligned A)) //
      t + w.length ≤ C.sortedExit A l t} ≤ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simpa only [hwlen, Processing.qualifying] using hfew
  have hAligned : Nat.card (C.AlignedOccurrence hD.closed g t w) ≤ k :=
    (C.aligned_card_le_qualifying hD.closed g t w).trans hcard
  obtain ⟨o, hdiff, a, b, har, hrb, hfa, hbl, hagree⟩ :=
    D.period_forces_matching hD hp hk hper hw hwne hv hmv hmw hlen ov halign hAligned
  let c : ℤ := o.2.val.val - t
  let R : (C.layerAt hD.closed o.1).Record A := {
    offset := c
    start := a - c
    stop := b - c
    first_le := by simpa only [sub_add_cancel] using hfa
    le_last := by simpa only [sub_add_cancel] using hbl
    agree := by
      intro x hax hxb
      have hh := hagree (x + c) (by omega) (by omega)
      change C.groupText o.1.1 (x + c) = A (x + c - o.2.val.val + t) at hh
      have he : x + c - (o.2.val.val : ℤ) + t = x := by dsimp only [c]; omega
      rw [he] at hh
      exact hh.symm }
  have hd : A ≠ fun x => C.groupText o.1.1 (x + R.offset) := by
    intro he
    apply hdiff
    intro x
    have hh := congrFun he (x + t)
    change A (x + t) = C.groupText o.1.1 (x + t + c) at hh
    have hc : x + t + c = x + (o.2.val.val : ℤ) := by dsimp only [c]; omega
    rw [hc] at hh
    exact hh.symm
  refine ⟨o.1, R, ?_, ?_, hd,
    R.length_lt hp (C.primitive_group o.1.1).positive per
      (C.primitive_group o.1.1).periodic hd, ?_⟩
  · change a - c ≤ t
    dsimp only [c]
    omega
  · change H - (k * p : ℕ) ≤ b - c
    dsimp only [c]
    omega
  · intro he
    apply R.same_period_length_lt hp per _ hd
    simpa only [he] using (C.primitive_group o.1.1).periodic

end Counts.Data

end Superstring

end OAI
