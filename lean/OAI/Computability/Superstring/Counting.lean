import OAI.Computability.Superstring.Groups

namespace OAI

namespace Superstring

namespace Hierarchical.TextOccurs

variable {α : Type} {B : ℤ → α} {s : List α} {t l u : ℤ}

theorem occurs_word (hs : TextOccurs B s t) (hlt : l ≤ t)
    (htu : t + s.length ≤ u) : Counts.Occurs (textWord B l u) s (t - l).toNat := by
  have hlen : (textWord B l u).length = (u - l).toNat := length_textWord B l u
  refine ⟨by omega, ?_⟩
  intro i
  have hi : (t - l).toNat + i.val < (textWord B l u).length := by
    have := i.isLt
    omega
  rw [(word B l u).get hi, hs i]
  congr 2
  omega

theorem agrees_template (hs : TextOccurs B s t) {A : ℤ → α}
    (hA : Counts.Matches A s) : AgreeOn B (fun x => A (x - t)) t (t + s.length) := by
  intro x htx hxe
  let k := (x - t).toNat
  have hk : k < s.length := by dsimp [k]; omega
  have he : t + (k : ℤ) = x := by dsimp [k]; omega
  have hh := (hs ⟨k, hk⟩).symm.trans (hA ⟨k, hk⟩)
  simp only [Option.some.injEq] at hh
  rw [he] at hh
  exact hh.trans (congrArg A (by omega))

end Hierarchical.TextOccurs

namespace Counts.Block

open Hierarchical

variable {α : Type} {A B : ℤ → α} {s r r' : List α} {j j' : ℕ} {x x' : ℤ}

theorem text_left (h : Block A s r j) (hr : TextOccurs B r x) : B x ≠ A (-(j : ℤ)) := by
  have hi : 0 < r.length := h.length_pos
  have hh := h.2.2.2.2.1
  rw [hr.get hi, Nat.cast_zero, add_zero] at hh
  exact fun he => hh (congrArg some he)

theorem text_right (h : Block A s r j) (hr : TextOccurs B r x) :
    B (x + r.length - 1) ≠ A (x + r.length - 1 - (x + j)) := by
  have hi : r.length - 1 < r.length := by have := h.length_pos; omega
  have hh := h.2.2.2.2.2
  rw [hr.get hi] at hh
  intro he
  apply hh
  congr 1
  convert he using 1 <;> congr 1 <;> omega

theorem text_inside (h : Block A s r j) (hr : TextOccurs B r x) (z : ℤ)
    (hzl : x < z) (hzr : z < x + r.length - 1) :
    B z = A (z - (x + j)) := by
  let k := (z - x).toNat
  have hk : k < r.length := by dsimp only [k]; omega
  have hk0 : 0 < k := by dsimp only [k]; omega
  have hkl : k + 1 < r.length := by dsimp only [k]; omega
  have hh := h.2.2.2.1 ⟨k, hk⟩ hk0 hkl
  rw [hr.get hk, Option.some.injEq] at hh
  convert hh using 1 <;> congr 1 <;> dsimp only [k] <;> omega

/-- Nearest-mismatch uniqueness on a bi-infinite lift; endpoints may be negative. -/
theorem text_boundaries_unique (h : Block A s r j) (h' : Block A s r' j')
    (hr : TextOccurs B r x) (hr' : TextOccurs B r' x') (he : x + j = x' + j') :
    x = x' ∧ r.length = r'.length := by
  have h₁ := h.1
  have h₂ := h.2.1
  have h₁' := h'.1
  have h₂' := h'.2.1
  have hstart : x = x' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := h'.text_left hr'
      have hh := h.text_inside hr x' hlt (by omega)
      apply hm
      convert hh using 1
      congr 1
      omega
    · have hm := h.text_left hr
      have hh := h'.text_inside hr' x hgt (by omega)
      apply hm
      convert hh using 1
      congr 1
      omega
  refine ⟨hstart, ?_⟩
  subst x'
  have hj : j = j' := by omega
  subst j'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.text_right hr (h'.text_inside hr' (x + r.length - 1) (by omega) (by omega))
  · exact h'.text_right hr' (h.text_inside hr (x + r'.length - 1) (by omega) (by omega))


theorem of_bounds {t l u : ℤ} (hs : TextOccurs B s t) (hlt : l < t)
    (htu : t + s.length ≤ u) (hl : B l ≠ A (l - t)) (hu : B u ≠ A (u - t))
    (hm : ∀ z : ℤ, l < z → z < u → B z = A (z - t)) :
    Block A s (textWord B l (u + 1)) (t - l).toNat := by
  have hlen : ((textWord B l (u + 1)).length : ℤ) = u + 1 - l := by
    rw [length_textWord]
    omega
  have hj : (((t - l).toNat : ℕ) : ℤ) = t - l := by omega
  refine ⟨by omega, by omega, hs.occurs_word (by omega) (by omega), ?_, ?_, ?_⟩
  · intro i hi hil
    rw [(TextOccurs.word B l (u + 1)).get i.isLt]
    congr 1
    have hh := hm (l + i.val) (by omega) (by omega)
    convert hh using 1
    congr 1
    omega
  · have hi : 0 < (textWord B l (u + 1)).length := by omega
    rw [(TextOccurs.word B l (u + 1)).get hi, Nat.cast_zero, add_zero]
    intro he
    apply hl
    injection he with he
    convert he using 1
    congr 1
    omega
  · have hi : (textWord B l (u + 1)).length - 1 < (textWord B l (u + 1)).length := by omega
    rw [(TextOccurs.word B l (u + 1)).get hi]
    intro he
    apply hu
    injection he with he
    convert he using 1 <;> congr 1 <;> omega

end Counts.Block

namespace Hierarchical.Layer

variable {α : Type} {V : Set (List α)} {B : ℤ → α} {p : ℕ}

/-- The first up crossing of an occurrence end is an actual containing window. -/
theorem first_containing (D : Layer V B p) (hp : 0 < p) {s : List α} {t : ℤ}
    (hr : D.Records s t) : ∃ a : ℤ,
      a ≤ t ∧ D.first a ≤ t + s.length ∧ t + s.length ≤ D.last a := by
  let k : ℕ := (D.z t - (t + s.length)).toNat + 1
  let K : ℕ := k * p
  have hk : D.z t - (t + s.length) < k := by dsimp only [k]; omega
  have hK : (k : ℤ) ≤ K := by dsimp only [K]; exact_mod_cast Nat.le_mul_of_pos_right k hp
  have he := D.shift_mul k (t - K)
  have hearg : t - (K : ℤ) + (k * p : ℕ) = t := by dsimp only [K]; omega
  rw [hearg] at he
  change D.z t = D.z (t - K) + (K : ℤ) at he
  have hfirst : D.first (t - K) ≤ t + s.length := by
    have hm : D.first (t - K) ≤ D.z (t - K) := D.first_le_last (t - K)
    omega
  have hlast : t + s.length ≤ D.last (t - K + K) := by
    simpa only [sub_add_cancel, last] using hr.2
  obtain ⟨a, _ha, hat, hfa, hla⟩ := D.meets_height (t - K) (t + s.length) K hfirst hlast
  exact ⟨a, by omega, hfa, hla⟩


theorem matching_or_block (D : Layer V B p) (closed : SubstringClosed V) (hp : 0 < p)
    {A : ℤ → α} {s : List α} {t : ℤ} (hr : D.Records s t) (hA : Counts.Matches A s) :
    (∃ a b : ℤ, a ≤ t ∧ t + s.length ≤ b ∧ D.first a ≤ b ∧ b ≤ D.last a ∧
      AgreeOn B (fun x => A (x - t)) a b) ∨
    ∃ r ∈ V, ∃ (y : ℤ) (j : ℕ), D.Records r y ∧ Counts.Block A s r j ∧ y + j = t := by
  classical
  obtain ⟨a, hat, hfa, hla⟩ := D.first_containing hp hr
  have hagree := hr.1.agrees_template hA
  let leftBad := (Finset.Ico a t).filter (fun x => B x ≠ A (x - t))
  by_cases hleft : leftBad.Nonempty
  · let l := leftBad.max' hleft
    have hlmem : l ∈ leftBad := Finset.max'_mem _ _
    have hal : a ≤ l := (Finset.mem_Ico.mp (Finset.mem_filter.mp hlmem).1).1
    have hlt : l < t := (Finset.mem_Ico.mp (Finset.mem_filter.mp hlmem).1).2
    have hlbad : B l ≠ A (l - t) := (Finset.mem_filter.mp hlmem).2
    have hleftgood (x : ℤ) (hlx : l < x) (hxt : x < t) : B x = A (x - t) := by
      by_contra hx
      have hxmem : x ∈ leftBad := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega, hxt⟩, hx⟩
      have hh : x ≤ l := Finset.le_max' _ _ hxmem
      omega
    have hend : t + s.length ≤ D.z l := hla.trans (D.mono hal)
    let rightBad := (Finset.Ico (t + s.length) (D.z l)).filter (fun x => B x ≠ A (x - t))
    by_cases hright : rightBad.Nonempty
    · let u := rightBad.min' hright
      have humem : u ∈ rightBad := Finset.min'_mem _ _
      have heu : t + s.length ≤ u := (Finset.mem_Ico.mp (Finset.mem_filter.mp humem).1).1
      have huz : u < D.z l := (Finset.mem_Ico.mp (Finset.mem_filter.mp humem).1).2
      have hubad : B u ≠ A (u - t) := (Finset.mem_filter.mp humem).2
      have hinside (x : ℤ) (hlx : l < x) (hxu : x < u) : B x = A (x - t) := by
        by_cases hxt : x < t
        · exact hleftgood x hlx hxt
        · by_cases hxe : x < t + s.length
          · exact hagree x (by omega) hxe
          · by_contra hx
            have hxmem : x ∈ rightBad := Finset.mem_filter.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hx⟩
            have hh : u ≤ x := Finset.min'_le _ _ hxmem
            omega
      let r := textWord B l (u + 1)
      have hrl : D.Records r l := by
        refine ⟨TextOccurs.word B l (u + 1), ?_⟩
        change l + ((textWord B l (u + 1)).length : ℤ) ≤ D.z l
        rw [length_textWord]
        omega
      have hrV : r ∈ V := closed (D.last_actual l)
        ((D.records_iff_prefix r l).mp hrl).isInfix
      refine Or.inr ⟨r, hrV, l, (t - l).toNat, hrl,
        Counts.Block.of_bounds hr.1 hlt heu hlbad hubad hinside, ?_⟩
      omega
    · refine Or.inl ⟨l + 1, D.z l, by omega, hend, ?_, ?_, ?_⟩
      · simp only [first, add_sub_cancel_right, le_refl]
      · exact D.mono (by omega)
      · intro x hlx hxe
        by_cases hxt : x < t
        · exact hleftgood x (by omega) hxt
        · by_cases hxend : x < t + s.length
          · exact hagree x (by omega) hxend
          · by_contra hx
            apply hright
            exact ⟨x, Finset.mem_filter.mpr
              ⟨Finset.mem_Ico.mpr ⟨by omega, hxe⟩, hx⟩⟩
  · refine Or.inl ⟨a, t + s.length, hat, le_rfl, hfa, hla, ?_⟩
    intro x hax hxe
    by_cases hxt : x < t
    · by_contra hx
      apply hleft
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hax, hxt⟩, hx⟩⟩
    · exact hagree x (by omega) hxe

/-- A recorded complete bracketing word and one of its eligible inner placements. -/
abbrev BlockWitness (D : Layer V B p) (F : Finset (List α)) (A : ℤ → α) (s : List α) :=
  Σ r : F, D.Occurrence r.val × Counts.BlockPosition A s r.val

def blockedOccurrence (D : Layer V B p) (hp : 0 < p) (per : Function.Periodic B (p : ℤ))
    (F : Finset (List α)) (A : ℤ → α) (s : List α) (w : D.BlockWitness F A s) :
    D.Occurrence s :=
  D.normalize hp per (D.records_suboccurrence w.2.1.property w.2.2.property.2.2.1)

/-- Injectivity holds modulo one primitive turn, even when a block spans many turns. -/
theorem blockedOccurrence_injective (D : Layer V B p) (hp : 0 < p)
    (per : Function.Periodic B (p : ℤ)) (F : Finset (List α)) (A : ℤ → α) (s : List α) :
    Function.Injective (D.blockedOccurrence hp per F A s) := by
  rintro ⟨⟨r, hr⟩, ⟨x, hx⟩, ⟨j, hj⟩⟩ ⟨⟨r', hr'⟩, ⟨x', hx'⟩, ⟨j', hj'⟩⟩ he
  have hemod := congrArg (fun o : D.Occurrence s => (o.val.val : ℤ)) he
  simp only [blockedOccurrence, normalize_val] at hemod
  let q : ℤ := ((x.val : ℤ) + j.val) / p
  let q' : ℤ := ((x'.val : ℤ) + j'.val) / p
  have hT := hx.1.shift (show Function.Periodic B (-q * p) by
    simpa only [Int.cast_id] using per.int_mul (-q))
  have hT' := hx'.1.shift (show Function.Periodic B (-q' * p) by
    simpa only [Int.cast_id] using per.int_mul (-q'))
  have heq : ((x.val : ℤ) + -q * p) + j.val =
      ((x'.val : ℤ) + -q' * p) + j'.val := by
    have h₁ := Int.emod_add_ediv_mul ((x.val : ℤ) + j.val) (p : ℤ)
    have h₂ := Int.emod_add_ediv_mul ((x'.val : ℤ) + j'.val) (p : ℤ)
    change ((x.val : ℤ) + j.val) % (p : ℤ) = ((x'.val : ℤ) + j'.val) % (p : ℤ) at hemod
    dsimp only [q, q']
    simp only [neg_mul]
    omega
  obtain ⟨hstart, hlen⟩ := hj.text_boundaries_unique hj' hT hT' heq
  have hpz : (0 : ℤ) < p := by omega
  have hq : q = q' := by
    have hxb := x.isLt
    have hxb' := x'.isLt
    have hx0 : (0 : ℤ) ≤ x.val := by omega
    have hx0' : (0 : ℤ) ≤ x'.val := by omega
    simp only [neg_mul] at hstart
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh : q + 1 ≤ q' := by omega
      have hmul := mul_le_mul_of_nonneg_right hh (le_of_lt hpz)
      nlinarith
    · have hh : q' + 1 ≤ q := by omega
      have hmul := mul_le_mul_of_nonneg_right hh (le_of_lt hpz)
      nlinarith
  have hxx : x = x' := by
    apply Fin.ext
    rw [hq] at hstart
    omega
  have hjj : j.val = j'.val := by omega
  have hrr : r = r' := by
    rw [hstart] at hT
    exact hT.unique hT' hlen
  subst r'
  subst x'
  have hjs : j = j' := Fin.ext hjj
  subst j'
  rfl

/-- The exact block count for one periodic layer. -/
theorem card_blockWitness [DecidableEq α] (D : Layer V B p) (F : Finset (List α))
    (A : ℤ → α) (s : List α) :
    Fintype.card (D.BlockWitness F A s) =
      Counts.blocking F A s (fun r => Fintype.card (D.Occurrence r)) := by
  rw [Counts.blocking, Finset.sum_subtype F (fun _ => Iff.rfl)]
  simp only [Fintype.card_sigma, Fintype.card_prod, Counts.coefficient]
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.mul_comm _ _

/-- Normalization is compatible with moving to an inner occurrence. -/
theorem normalize_add (D : Layer V B p) (hp : 0 < p) (per : Function.Periodic B (p : ℤ))
    {r s : List α} {y : ℤ} (hy : D.Records r y) {j : ℕ} (hj : Counts.Occurs r s j) :
    D.normalize hp per (D.records_suboccurrence (D.normalize hp per hy).property hj) =
      D.normalize hp per (D.records_suboccurrence hy hj) := by
  apply Subtype.ext
  apply Fin.ext
  have he : (((D.normalize hp per hy).val.val : ℤ) + (j : ℤ)) % p =
      (y + (j : ℤ)) % p := by
    rw [D.normalize_val]
    simp only [Int.add_emod, Int.emod_emod]
  have h₁ := D.normalize_val hp per
    (D.records_suboccurrence (D.normalize hp per hy).property hj)
  have h₂ := D.normalize_val hp per (D.records_suboccurrence hy hj)
  omega

/-- Unblocked occurrences have actual matching windows; no matching-window
certificate is assumed in selecting an occurrence later in the algorithm. -/
theorem matching_of_not_blocked (D : Layer V B p) (F : Finset (List α))
    (hV : V = (F : Set (List α))) (closed : SubstringClosed V) (hp : 0 < p)
    (per : Function.Periodic B (p : ℤ)) {A : ℤ → α} {s : List α}
    (hA : Counts.Matches A s) (o : D.Occurrence s)
    (ho : ¬ ∃ w : D.BlockWitness F A s, D.blockedOccurrence hp per F A s w = o) :
    ∃ a b : ℤ, a ≤ o.val.val ∧ (o.val.val : ℤ) + s.length ≤ b ∧
      D.first a ≤ b ∧ b ≤ D.last a ∧ AgreeOn B (fun x => A (x - o.val.val)) a b := by
  rcases D.matching_or_block closed hp o.property hA with hm | ⟨r, hr, y, j, hy, hj, he⟩
  · exact hm
  · apply (ho ?_).elim
    have hrF : r ∈ F := by rw [hV] at hr; exact hr
    let w : D.BlockWitness F A s :=
      ⟨⟨r, hrF⟩, D.normalize hp per hy, ⟨⟨j, by change j < r.length + 1; have := hj.2.1; omega⟩, hj⟩⟩
    refine ⟨w, ?_⟩
    change D.normalize hp per
      (D.records_suboccurrence (D.normalize hp per hy).property hj.2.2.1) = o
    rw [D.normalize_add hp per hy hj.2.2.1]
    apply Subtype.ext
    apply Fin.ext
    have hh := D.normalize_val hp per (D.records_suboccurrence hy hj.2.2.1)
    have hm : (y + (j : ℤ)) % p = o.val.val := by
      rw [he, Int.emod_eq_of_lt (by omega) (by exact_mod_cast o.val.isLt)]
    exact_mod_cast hh.trans hm

/-- An occurrence whose full-text alignment equals the template is never blocked. -/
theorem aligned_not_blocked (D : Layer V B p) (hp : 0 < p)
    (per : Function.Periodic B (p : ℤ)) (F : Finset (List α)) {A : ℤ → α} {s : List α}
    (o : D.Occurrence s) (halign : ∀ x : ℤ, B (x + o.val.val) = A x) :
    ¬ ∃ w : D.BlockWitness F A s, D.blockedOccurrence hp per F A s w = o := by
  rintro ⟨⟨r, occ, pos⟩, he⟩
  have hm := congrArg (fun o : D.Occurrence s => (o.val.val : ℤ)) he
  simp only [blockedOccurrence, normalize_val] at hm
  have hleft := pos.property.text_left occ.property.1
  apply hleft
  have hed := Int.emod_add_ediv_mul ((occ.val.val : ℤ) + pos.val.val) (p : ℤ)
  have hper := per.int_mul (((occ.val.val : ℤ) + pos.val.val) / p)
    (-(pos.val.val : ℤ) + o.val.val)
  simp only [Int.cast_id] at hper
  have hecoord : -(pos.val.val : ℤ) + o.val.val +
      (((occ.val.val : ℤ) + pos.val.val) / p) * p = occ.val.val := by omega
  rw [hecoord] at hper
  exact hper.trans (halign (-(pos.val.val : ℤ)))

end Hierarchical.Layer

namespace Hierarchical.Family

variable {α ι : Type} [Fintype ι] {V : Set (List α)}
  {A : ι → ℤ → α} {p : ι → ℕ} (D : ∀ i, Layer V (A i) (p i))

/-- All recorded occurrences, retaining the actual original layer as their owner. -/
abbrev Occurrence (s : List α) := Σ i, (D i).Occurrence s

/-- Bracketing witnesses over the whole fixed family of layers. -/
abbrev BlockWitness (F : Finset (List α)) (B : ℤ → α) (s : List α) :=
  Σ i, (D i).BlockWitness F B s

def blockedOccurrence (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) (B : ℤ → α) (s : List α) :
    BlockWitness D F B s → Occurrence D s :=
  Sigma.map id (fun i => (D i).blockedOccurrence (hp i) (per i) F B s)

omit [Fintype ι] in
theorem blockedOccurrence_injective (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) (B : ℤ → α) (s : List α) :
    Function.Injective (blockedOccurrence D hp per F B s) :=
  Function.injective_id.sigma_map
    (fun i => (D i).blockedOccurrence_injective (hp i) (per i) F B s)


theorem card_blockWitness [DecidableEq α] (F : Finset (List α))
    (B : ℤ → α) (s : List α) :
    Fintype.card (BlockWitness D F B s) =
      Counts.blocking F B s (fun r => Fintype.card (Occurrence D r)) := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [Layer.card_blockWitness]
  unfold Counts.blocking
  rw [Finset.sum_comm]
  simp only [Fintype.card_sigma, Finset.mul_sum]

/-- An actual finite pigeonhole argument used by the period-rule forcing step. -/
theorem outside_image_and_pred {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → Y) (P : Y → Prop) [Fintype {y // P y}] (k : ℕ)
    (hX : Fintype.card X + k < Fintype.card Y)
    (hP : Fintype.card {y // P y} ≤ k) :
    ∃ y, (¬ ∃ x, f x = y) ∧ ¬ P y := by
  classical
  by_contra hn
  have cover : ∀ y, (∃ x, f x = y) ∨ P y := by
    intro y
    by_cases h : ∃ x, f x = y
    · exact Or.inl h
    · exact Or.inr (not_not.mp (fun hy => hn ⟨y, h, hy⟩))
  let g : X ⊕ {y // P y} → Y := Sum.elim f Subtype.val
  have hg : Function.Surjective g := by
    intro y
    rcases cover y with ⟨x, hx⟩ | hy
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩
  have hc := Fintype.card_le_of_surjective g hg
  simp only [Fintype.card_sum] at hc
  omega

omit [Fintype ι] in
/-- An aligned recorded occurrence is outside the global blocking image. -/
theorem aligned_not_blocked (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) {B : ℤ → α} {s : List α} (o : Occurrence D s)
    (halign : ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) :
    ¬ ∃ w : BlockWitness D F B s, blockedOccurrence D hp per F B s w = o := by
  rcases o with ⟨i, o⟩
  rintro ⟨⟨j, w⟩, he⟩
  have hij : j = i := congrArg Sigma.fst he
  subst j
  have he' : (D i).blockedOccurrence (hp i) (per i) F B s w = o :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact (D i).aligned_not_blocked (hp i) (per i) F o halign ⟨w, he'⟩


theorem blocking_lt_of_aligned [DecidableEq α] (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) {B : ℤ → α} {s : List α} (o : Occurrence D s)
    (halign : ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) :
    Counts.blocking F B s (fun r => Fintype.card (Occurrence D r)) <
      Fintype.card (Occurrence D s) := by
  rw [← card_blockWitness D F B s]
  apply Fintype.card_lt_of_injective_not_surjective
    (blockedOccurrence D hp per F B s)
    (blockedOccurrence_injective D hp per F B s)
  intro hsurj
  exact aligned_not_blocked D hp per F o halign (hsurj o)

/-- The excess forced by a period rule produces a matching actual window on a
DIFFERENT aligned text. The exceptional set must have the proved size bound k. -/
theorem matching_different [DecidableEq α] (hp : ∀ i, 0 < p i)
    (per : ∀ i, Function.Periodic (A i) (p i : ℤ))
    (F : Finset (List α)) (hV : V = (F : Set (List α)))
    (closed : SubstringClosed V) {B : ℤ → α} {s : List α}
    (hB : Counts.Matches B s) (k : ℕ)
    (hexcess : Counts.blocking F B s (fun r => Fintype.card (Occurrence D r)) + k <
      Fintype.card (Occurrence D s))
    (hfew : Nat.card {o : Occurrence D s //
      ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x} ≤ k) :
    ∃ o : Occurrence D s, (¬ ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) ∧
      ∃ a b : ℤ, a ≤ o.2.val.val ∧ (o.2.val.val : ℤ) + s.length ≤ b ∧
        (D o.1).first a ≤ b ∧ b ≤ (D o.1).last a ∧
        AgreeOn (A o.1) (fun x => B (x - o.2.val.val)) a b := by
  classical
  rw [← card_blockWitness D F B s] at hexcess
  obtain ⟨o, ho, hdiff⟩ := outside_image_and_pred
    (blockedOccurrence D hp per F B s)
    (fun o => ∀ x : ℤ, A o.1 (x + o.2.val.val) = B x) k hexcess (by simpa only [Nat.card_eq_fintype_card] using hfew)
  refine ⟨o, hdiff, (D o.1).matching_of_not_blocked F hV closed (hp o.1) (per o.1)
    hB o.2 ?_⟩
  rintro ⟨w, hw⟩
  apply ho
  exact ⟨⟨o.1, w⟩, by cases o; exact congrArg (Sigma.mk _) hw⟩

end Hierarchical.Family

end Superstring

end OAI
