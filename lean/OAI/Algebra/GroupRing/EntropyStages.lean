import Mathlib
import OAI.Algebra.GroupRing.BlockGrid

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.EntropyStages
structure Pairing (O : Type*) where
  partner : O → O
  involutive : Function.Involutive partner
end TorsionFreeZeroDivisors.EntropyStages

namespace TorsionFreeZeroDivisors.OccurrenceMatching
open scoped Classical
open EntropyStages
variable {Ω B E : Type*}

structure Data where
  /-- Uniform bound for discarded letters in every selected comparison. -/
  error : ℕ
  positions : B → Finset Ω
  disjoint : ∀ {o p}, o ≠ p → Disjoint (positions o) (positions p)
  pairing : Pairing Ω
  side : Ω → Option E
  flip : E → E
  flip_inv : Function.Involutive flip
  flip_ne : ∀ e, flip e ≠ e
  side_partner : ∀ x e, side x = some e → side (pairing.partner x) = some (flip e)

namespace Data
variable (D : Data (Ω := Ω) (B := B) (E := E))

/-- The positions of one comparison side in a pair of occurrence blocks. -/
def slice (e : E) (o p : B) : Finset Ω :=
  (D.positions o).filter (fun x => D.side x = some e ∧ D.pairing.partner x ∈ D.positions p)

theorem slice_mem {e : E} {o p : B} {x : Ω} :
    x ∈ D.slice e o p ↔ x ∈ D.positions o ∧ D.side x = some e ∧ D.pairing.partner x ∈ D.positions p := by
  simp only [slice,Finset.mem_filter]

def reverseSlice (e : E) (o p : B) : D.slice e o p ≃ D.slice (D.flip e) p o where
  toFun x := ⟨D.pairing.partner x.val,by
    obtain ⟨hx,he,hp⟩ := D.slice_mem.mp x.property
    exact D.slice_mem.mpr ⟨hp,D.side_partner x.val e he,by rwa [D.pairing.involutive]⟩⟩
  invFun x := ⟨D.pairing.partner x.val,by
    obtain ⟨hx,he,hp⟩ := D.slice_mem.mp x.property
    exact D.slice_mem.mpr ⟨hp,by simpa only [D.flip_inv e] using D.side_partner x.val (D.flip e) he,
      by rwa [D.pairing.involutive]⟩⟩
  left_inv x := Subtype.ext (D.pairing.involutive x.val)
  right_inv x := Subtype.ext (D.pairing.involutive x.val)

theorem slice_card (e : E) (o p : B) : (D.slice e o p).card = (D.slice (D.flip e) p o).card := by
  simpa using Fintype.card_congr (D.reverseSlice e o p)

def Joined (o p : B) : Prop :=
  ∃ e, (D.positions o).card < 2*(D.slice e o p).card ∧
    (D.positions p).card < 2*(D.slice e o p).card ∧
    (D.positions o).card ≤ (D.slice e o p).card+D.error ∧
    (D.positions p).card ≤ (D.slice e o p).card+D.error

theorem joined_symm {o p : B} (h : D.Joined o p) : D.Joined p o := by
  obtain ⟨e,ho,hp,heo,hep⟩ := h
  rw [D.slice_card e o p] at ho hp heo hep
  exact ⟨D.flip e,hp,ho,hep,heo⟩

theorem joined_ne {o p : B} (h : D.Joined o p) : o ≠ p := by
  intro he
  subst p
  obtain ⟨e,ho,_⟩ := h
  have hd : Disjoint (D.slice e o o) (D.slice (D.flip e) o o) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (D.slice_mem.mp hx).2.1
    have hy' := (D.slice_mem.mp hy).2.1
    exact D.flip_ne e (Option.some.inj (hy'.symm.trans hx'))
  have hu : D.slice e o o ∪ D.slice (D.flip e) o o ⊆ D.positions o :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd,← D.slice_card e o o] at hc
  omega

theorem joined_unique {o p q : B} (hp : D.Joined o p) (hq : D.Joined o q) : p = q := by
  by_contra hne
  obtain ⟨e,ho,_⟩ := hp
  obtain ⟨f,ho',_⟩ := hq
  have hd : Disjoint (D.slice e o p) (D.slice f o q) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp (D.disjoint hne) (D.slice_mem.mp hx).2.2 (D.slice_mem.mp hy).2.2
  have hu : D.slice e o p ∪ D.slice f o q ⊆ D.positions o :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hc := Finset.card_le_card hu
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

def partner (o : B) : B := if h : ∃ p, D.Joined o p then h.choose else o

theorem partner_spec {o p : B} (h : D.Joined o p) : D.partner o = p := by
  unfold partner
  rw [dite_eq_left ⟨p,h⟩]
  exact D.joined_unique (Exists.choose_spec _) h

theorem partner_involutive : Function.Involutive D.partner := by
  intro o
  by_cases h : ∃ p, D.Joined o p
  · obtain ⟨p,hp⟩ := h
    rw [D.partner_spec hp,D.partner_spec (D.joined_symm hp)]
  · simp only [partner,dite_eq_right h]

def matching : Pairing B := ⟨D.partner,D.partner_involutive⟩

theorem matched_iff (o : B) : (D.matching.partner o ≠ o) ↔ ∃ p, D.Joined o p := by
  change D.partner o ≠ o ↔ _
  constructor
  · intro h
    by_contra hn
    exact h (by simp [partner,hn])
  · rintro ⟨p,hp⟩
    rw [D.partner_spec hp]
    exact (D.joined_ne hp).symm

theorem unmatched_iff (o : B) : D.matching.partner o = o ↔ ∀ p, ¬D.Joined o p := by
  simpa using not_congr (D.matched_iff o)

/-- Explicit error criterion usable with the half-integer alignment lemma. -/
theorem joined_of_small_deficit {o p : B} {e : E}
    (hbig_o : 2*D.error < (D.positions o).card) (hbig_p : 2*D.error < (D.positions p).card)
    (hdef_o : (D.positions o).card-(D.slice e o p).card ≤ D.error)
    (hdef_p : (D.positions p).card-(D.slice e o p).card ≤ D.error) : D.Joined o p := by
  exact ⟨e,by omega,by omega,by omega,by omega⟩

open scoped BigOperators
variable [Fintype Ω] [Fintype B]

def unmatchedBlocks : Finset B := Finset.univ.filter (fun o => D.matching.partner o = o)
def unpairedPositions : Finset Ω := Finset.univ.filter (fun x => D.pairing.partner x = x)

/-- The source unmatched-block charge, with every rounding/cut error explicit.
Only the stated local geometric coverage of nonexceptional blocks is needed. -/
theorem unmatched_mass (s : ℝ) (hs : 0 ≤ s) (exceptional : Finset B)
    (hsize : ∀ o, s-1 ≤ ((D.positions o).card : ℝ))
    (hcover : ∀ o, D.matching.partner o = o → o ∉ exceptional →
      D.positions o ⊆ D.unpairedPositions) :
    s*(D.unmatchedBlocks.card : ℝ) ≤ (D.unpairedPositions.card : ℝ) +
      s*exceptional.card + Fintype.card B := by
  let good := D.unmatchedBlocks \ exceptional
  have hsubset : good.biUnion D.positions ⊆ D.unpairedPositions := by
    intro x hx
    obtain ⟨o,ho,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨ho,hn⟩ := Finset.mem_sdiff.mp ho
    exact hcover o (Finset.mem_filter.mp ho).2 hn hx
  have hsum : (∑ o ∈ good, (D.positions o).card) ≤ D.unpairedPositions.card := by
    rw [← Finset.card_biUnion (fun o _ p _ hne => D.disjoint hne)]
    exact Finset.card_le_card hsubset
  have hsumr : (∑ o ∈ good, ((D.positions o).card : ℝ)) ≤ D.unpairedPositions.card := by
    exact_mod_cast hsum
  have hlower : s*(good.card : ℝ) ≤ D.unpairedPositions.card + good.card := by
    have hh := Finset.sum_le_sum (s := good) (fun o _ => hsize o)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    nlinarith
  have hcount : D.unmatchedBlocks.card ≤ good.card+exceptional.card := by
    have hh := Finset.card_sdiff_add_card_inter D.unmatchedBlocks exceptional
    have hi := Finset.card_le_card (Finset.inter_subset_right : D.unmatchedBlocks ∩ exceptional ⊆ exceptional)
    dsimp [good]
    omega
  have hcount' : (D.unmatchedBlocks.card : ℝ) ≤ good.card+exceptional.card := by exact_mod_cast hcount
  have hb : (good.card : ℝ) ≤ Fintype.card B := by exact_mod_cast Finset.card_le_univ good
  have hh := mul_le_mul_of_nonneg_left hcount' hs
  nlinarith

end Data
end TorsionFreeZeroDivisors.OccurrenceMatching

/-! The actual common-grid block matching of an affine comparison system.
Positions are the literal half-integer edge indices within each traversal. -/
namespace TorsionFreeZeroDivisors.ComparedBlocks
open scoped Classical BigOperators
open BlockAlignment EntropyStages
variable {T E : Type*}

abbrev Position (len : T → ℕ) := (t : T) × (positions 0 (len t))
abbrev Block (s : ℝ) (len : T → ℕ) := (t : T) × Fin (blockCount s (len t))

variable (s : ℝ) (hs : 0 < s) (len : T → ℕ)

def includeBlock (b : Block s len) : block s b.2.val ↪ Position len where
  toFun q := ⟨b.1,⟨q.val,full_subset s hs (len b.1) b.2 q.property⟩⟩
  inj' := by
    intro q r h
    exact Subtype.ext (congrArg (fun x : Position len => x.2.val) h)

def blockPositions (b : Block s len) : Finset (Position len) :=
  (block s b.2.val).attach.map (includeBlock s hs len b)

theorem mem_blockPositions {b : Block s len} {x : Position len} :
    x ∈ blockPositions s hs len b ↔ x.1 = b.1 ∧ x.2.val ∈ block s b.2.val := by
  constructor
  · intro hx
    obtain ⟨y,_,he⟩ := Finset.mem_map.mp hx
    cases he
    exact ⟨rfl,y.property⟩
  · rintro ⟨he,hq⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨x.2.val,hq⟩,Finset.mem_attach _ _,?_⟩
    cases b; cases x; dsimp at he; subst he; rfl

theorem blockPositions_card (b : Block s len) :
    (blockPositions s hs len b).card = (block s b.2.val).card := by
  simp only [blockPositions,Finset.card_map,Finset.card_attach]

theorem blockPositions_disjoint {b c : Block s len} (hne : b ≠ c) :
    Disjoint (blockPositions s hs len b) (blockPositions s hs len c) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨he,hx⟩ := (mem_blockPositions s hs len).mp hx
  obtain ⟨he',hy⟩ := (mem_blockPositions s hs len).mp hy
  have hb : b.1 = c.1 := he.symm.trans he'
  have hk : (b.2.val : ℤ) = c.2.val := by
    by_contra h
    exact Finset.disjoint_left.mp (block_disjoint s hs h) hx hy
  cases b; cases c; dsimp at hb hk; subst hb
  exact hne (by congr 1; apply Fin.ext; exact_mod_cast hk)

include hs in
/-- Exact full-grid-index converse, rather than clipping a target partner. -/
theorem fullIndex {t : T} {k : ℤ} (hk : 0 ≤ k)
    (hfull : ((k : ℝ)+1)*s ≤ len t) :
    ∃ j : Fin (blockCount s (len t)), (j.val : ℤ) = k := by
  have hcast : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  have hle : k.toNat+1 ≤ blockCount s (len t) := by
    apply Nat.le_floor
    rw [Nat.cast_add,Nat.cast_one,hcast]
    exact (le_div_iff₀ hs).mpr hfull
  exact ⟨⟨k.toNat,by omega⟩,Int.toNat_of_nonneg hk⟩

/-- Data of the original disjoint signed interval comparisons on traversals.
The involution and side predicates retain occurrence indices throughout. -/
structure Comparisons where
  pairing : Pairing (Position len)
  side : Position len → Option E
  flip : E → E
  flip_inv : Function.Involutive flip
  flip_ne : ∀ e, flip e ≠ e
  side_partner : ∀ x e, side x = some e → side (pairing.partner x) = some (flip e)
  none_iff : ∀ x, side x = none ↔ pairing.partner x = x
  source : E → T
  lo : E → ℝ
  hi : E → ℝ
  reverse : E → Bool
  offset : E → ℤ
  side_iff : ∀ x e, side x = some e ↔ x.1 = source e ∧ x.2.val ∈ positions (lo e) (hi e)
  partner_source : ∀ x e, side x = some e → (pairing.partner x).1 = source (flip e)
  partner_coordinate : ∀ x e, side x = some e →
    (pairing.partner x).2.val = affine (reverse e) (offset e) x.2.val
  target_range : ∀ e, if reverse e then
      0 ≤ (offset e : ℝ)-hi e ∧ (offset e : ℝ)-lo e ≤ len (source (flip e))
    else 0 ≤ lo e+(offset e : ℝ) ∧ hi e+(offset e : ℝ) ≤ len (source (flip e))

namespace Comparisons
variable (C : Comparisons (E := E) len) (err : ℕ)

def matchingData : OccurrenceMatching.Data (Ω := Position len) (B := Block s len) (E := E) where
  error := err
  positions := blockPositions s hs len
  disjoint := blockPositions_disjoint s hs len
  pairing := C.pairing
  side := C.side
  flip := C.flip
  flip_inv := C.flip_inv
  flip_ne := C.flip_ne
  side_partner := C.side_partner

/-- The literal integer slice before making any near-full grid approximation. -/
def integerSlice (e : E) (b p : Block s len) : Finset ℤ :=
  (block s b.2.val ∩ positions (C.lo e) (C.hi e)).filter
    (fun q => affine (C.reverse e) (C.offset e) q ∈ block s p.2.val)

theorem slice_sources {e : E} {b p : Block s len}
    (hne : ((C.matchingData s hs len err).slice e b p).Nonempty) :
    b.1 = C.source e ∧ p.1 = C.source (C.flip e) := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hb,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
  have hb' := ((mem_blockPositions s hs len).mp hb).1
  have hp' := ((mem_blockPositions s hs len).mp hp).1
  exact ⟨hb'.symm.trans ((C.side_iff x e).mp he).1,
    hp'.symm.trans (C.partner_source x e he)⟩

theorem slice_integer_card {e : E} {b p : Block s len}
    (hsource : b.1 = C.source e) (htarget : p.1 = C.source (C.flip e)) :
    ((C.matchingData s hs len err).slice e b p).card =
      (C.integerSlice s len e b p).card := by
  apply Finset.card_bij (fun x _ => x.2.val)
  · intro x hx
    obtain ⟨hb,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr
      ⟨((mem_blockPositions s hs len).mp hb).2,((C.side_iff x e).mp he).2⟩,?_⟩
    have hh := ((mem_blockPositions s hs len).mp hp).2
    change (C.pairing.partner x).2.val ∈ block s p.2.val at hh
    rwa [C.partner_coordinate x e he] at hh
  · intro x hx y hy he
    have hx' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hx).1).1
    have hy' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hy).1).1
    have hxy := hx'.trans hy'.symm
    cases x; cases y; dsimp at hxy he; subst hxy
    congr 1
    exact Subtype.ext he
  · intro q hq
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hb,he⟩ := Finset.mem_inter.mp hq
    let x : Position len := ⟨b.1,⟨q,full_subset s hs (len b.1) b.2 hb⟩⟩
    have hx : C.side x = some e := (C.side_iff x e).mpr ⟨hsource,he⟩
    refine ⟨x,(OccurrenceMatching.Data.slice_mem _).mpr ⟨?_,hx,?_⟩,rfl⟩
    · exact (mem_blockPositions s hs len).mpr ⟨rfl,hb⟩
    · apply (mem_blockPositions s hs len).mpr
      refine ⟨(C.partner_source x e hx).trans htarget.symm,?_⟩
      change (C.pairing.partner x).2.val ∈ block s p.2.val
      rwa [C.partner_coordinate x e hx]

/-- The original side comparison covers this entire source block. -/
theorem side_of_margin {b : Block s len} {e : E} (hsource : b.1 = C.source e)
    (hlo : C.lo e ≤ (b.2.val : ℝ)*s-s)
    (hhi : ((b.2.val : ℝ)+1)*s+s ≤ C.hi e)
    {x : Position len} (hx : x ∈ blockPositions s hs len b) : C.side x = some e := by
  obtain ⟨he,hx⟩ := (mem_blockPositions s hs len).mp hx
  obtain ⟨hx0,hx1⟩ := mem_positions.mp hx
  apply (C.side_iff x e).mpr
  refine ⟨he.trans hsource,mem_positions.mpr ?_⟩
  simp only [Int.cast_natCast] at hx0 hx1
  constructor <;> linarith

/-- The full slice is exactly the algebraic source overlap. -/
theorem slice_card_eq {b p : Block s len} {e : E} {ν : ℤ}
    (hsource : b.1 = C.source e) (htarget : p.1 = C.source (C.flip e))
    (hindex : (p.2.val : ℤ) = partnerIndex (C.reverse e) ν b.2.val)
    (hlo : C.lo e ≤ (b.2.val : ℝ)*s-s)
    (hhi : ((b.2.val : ℝ)+1)*s+s ≤ C.hi e) :
    ((C.matchingData s hs len err).slice e b p).card =
      (overlap s (C.reverse e) (C.offset e) b.2.val ν).card := by
  apply Finset.card_bij (fun x _ => x.2.val)
  · intro x hx
    obtain ⟨hx,he,hp⟩ := (OccurrenceMatching.Data.slice_mem _).mp hx
    have hc := C.partner_coordinate x e he
    have hm := ((mem_blockPositions s hs len).mp hp).2
    change (C.pairing.partner x).2.val ∈ block s p.2.val at hm
    refine Finset.mem_filter.mpr ⟨((mem_blockPositions s hs len).mp hx).2,?_⟩
    rwa [hc,hindex] at hm
  · intro x hx y hy he
    have hx' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hx).1).1
    have hy' := ((mem_blockPositions s hs len).mp ((OccurrenceMatching.Data.slice_mem _).mp hy).1).1
    have hxy := hx'.trans hy'.symm
    cases x; cases y; dsimp at hxy he; subst hxy
    congr 1
    exact Subtype.ext he
  · intro q hq
    obtain ⟨hq,hq'⟩ := Finset.mem_filter.mp hq
    let x : Position len := ⟨b.1,⟨q,full_subset s hs (len b.1) b.2 hq⟩⟩
    have hx : x ∈ blockPositions s hs len b := (mem_blockPositions s hs len).mpr ⟨rfl,hq⟩
    have he := C.side_of_margin s hs len hsource hlo hhi hx
    refine ⟨x,(OccurrenceMatching.Data.slice_mem _).mpr ⟨hx,he,?_⟩,rfl⟩
    apply (mem_blockPositions s hs len).mpr
    refine ⟨(C.partner_source x e he).trans htarget.symm,?_⟩
    change (C.pairing.partner x).2.val ∈ block s p.2.val
    rw [C.partner_coordinate x e he,hindex]
    exact hq'

/-- A block deep inside an actual comparison has a near-full selected partner. -/
theorem joined_of_margin {b : Block s len} {e : E} {ν : ℤ}
    (hsource : b.1 = C.source e)
    (hsmall : 2*(err : ℝ) < s-1)
    (herr : 2*|(C.offset e : ℝ)-(ν : ℝ)*s|+4 ≤ err)
    (hlo : C.lo e ≤ (b.2.val : ℝ)*s-s)
    (hhi : ((b.2.val : ℝ)+1)*s+s ≤ C.hi e) :
    ∃ p, (C.matchingData s hs len err).Joined b p := by
  have ha : |(C.offset e : ℝ)-(ν : ℝ)*s| ≤ s := by
    have hh := abs_nonneg ((C.offset e : ℝ)-(ν : ℝ)*s)
    linarith
  obtain ⟨hk0,hk1⟩ := partner_full s hs (C.reverse e) (C.offset e) b.2.val ν
    (C.lo e) (C.hi e) (len (C.source (C.flip e))) ha hlo hhi (C.target_range e)
  obtain ⟨j,hj⟩ := fullIndex s hs len hk0 hk1
  let p : Block s len := ⟨C.source (C.flip e),j⟩
  have hslice := C.slice_card_eq s hs len err hsource (p := p) rfl hj hlo hhi
  refine ⟨p,OccurrenceMatching.Data.joined_of_small_deficit _ (e := e) ?_ ?_ ?_ ?_⟩
  · change 2*err < (blockPositions s hs len b).card
    rw [blockPositions_card]
    have hh := card_lower ((b.2.val : ℝ)*s) (((b.2.val : ℝ)+1)*s)
    have hr : 2*(err : ℝ) < (block s b.2.val).card := by simp only [block,Int.cast_natCast]; nlinarith
    exact_mod_cast hr
  · change 2*err < (blockPositions s hs len p).card
    rw [blockPositions_card]
    have hh := card_lower ((p.2.val : ℝ)*s) (((p.2.val : ℝ)+1)*s)
    have hr : 2*(err : ℝ) < (block s p.2.val).card := by simp only [block,Int.cast_natCast]; nlinarith
    exact_mod_cast hr
  · change (blockPositions s hs len b).card- _ ≤ err
    rw [blockPositions_card,hslice]
    have hh := (overlap_deficit s hs.le (C.reverse e) (C.offset e) b.2.val ν).trans herr
    exact_mod_cast hh
  · change (blockPositions s hs len p).card- _ ≤ err
    rw [blockPositions_card,hslice]
    have hc := Fintype.card_congr (overlapEquiv s (C.reverse e) (C.offset e) b.2.val ν)
    simp only [Fintype.card_coe] at hc
    rw [hc]
    have hh := overlap_deficit s hs.le (C.reverse e) (inverseOffset (C.reverse e) (C.offset e))
      (partnerIndex (C.reverse e) ν b.2.val) (inverseOffset (C.reverse e) ν)
    rw [inverse_error] at hh
    have hr := hh.trans herr
    change ((block s j.val).card - _) ≤ _
    rw [hj]
    exact_mod_cast hr

variable [Fintype T] [Fintype E]

def nearCutBlocks (t : T) (cut : ℝ) : Finset (Block s len) :=
  Finset.univ.filter (fun b => b.1 = t ∧ (b.2.val : ℤ) ∈ nearCut s cut)

theorem nearCutBlocks_card (t : T) (cut : ℝ) : (nearCutBlocks s len t cut).card ≤ 11 := by
  apply le_trans ?_ (nearCut_card s cut)
  refine Finset.card_le_card_of_injOn (fun b : Block s len => (b.2.val : ℤ)) ?_ ?_
  · intro b hb
    exact (Finset.mem_filter.mp hb).2.2
  · intro b hb c hc he
    have hb' := (Finset.mem_filter.mp hb).2.1
    have hc' := (Finset.mem_filter.mp hc).2.1
    have hbc := hb'.trans hc'.symm
    cases b; cases c; dsimp at hbc he; subst hbc
    congr 1
    apply Fin.ext
    exact_mod_cast he

def exceptional : Finset (Block s len) :=
  Finset.univ.biUnion (fun e : E =>
    nearCutBlocks s len (C.source e) (C.lo e) ∪ nearCutBlocks s len (C.source e) (C.hi e))

theorem exceptional_card : (C.exceptional s len).card ≤ 22*Fintype.card E := by
  have h1 := Finset.card_biUnion_le (s := (Finset.univ : Finset E))
    (t := fun e => nearCutBlocks s len (C.source e) (C.lo e) ∪ nearCutBlocks s len (C.source e) (C.hi e))
  have h2 : ∀ e : E, (nearCutBlocks s len (C.source e) (C.lo e) ∪
      nearCutBlocks s len (C.source e) (C.hi e)).card ≤ 22 := by
    intro e
    have h := Finset.card_union_le (nearCutBlocks s len (C.source e) (C.lo e))
      (nearCutBlocks s len (C.source e) (C.hi e))
    have h3 := nearCutBlocks_card s len (C.source e) (C.lo e)
    have h4 := nearCutBlocks_card s len (C.source e) (C.hi e)
    omega
  have h3 := Finset.sum_le_sum (s := (Finset.univ : Finset E)) (fun e _ => h2 e)
  simpa [exceptional,Nat.mul_comm] using h1.trans h3

/-- No point of a deep unmatched block belongs to any original comparison. -/
theorem unmatched_unpaired (ν : E → ℤ)
    (hsmall : 2*(err : ℝ) < s-1)
    (herr : ∀ e, 2*|(C.offset e : ℝ)-(ν e : ℝ)*s|+4 ≤ err)
    {b : Block s len} (hb : (C.matchingData s hs len err).matching.partner b = b)
    (hn : b ∉ C.exceptional s len) :
    blockPositions s hs len b ⊆ (C.matchingData s hs len err).unpairedPositions := by
  intro x hx
  simp only [OccurrenceMatching.Data.unpairedPositions,Finset.mem_filter,Finset.mem_univ,true_and]
  change C.pairing.partner x = x
  apply (C.none_iff x).mp
  cases he : C.side x with
  | none => rfl
  | some e =>
    exfalso
    obtain ⟨hxsource,hdom⟩ := (C.side_iff x e).mp he
    obtain ⟨hxb,hxk⟩ := (mem_blockPositions s hs len).mp hx
    have hsource := hxb.symm.trans hxsource
    have hnlo : (b.2.val : ℤ) ∉ nearCut s (C.lo e) := by
      intro h
      apply hn
      exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsource,h⟩)⟩
    have hnhi : (b.2.val : ℤ) ∉ nearCut s (C.hi e) := by
      intro h
      apply hn
      exact Finset.mem_biUnion.mpr ⟨e,Finset.mem_univ _,Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsource,h⟩)⟩
    obtain ⟨hl,hr⟩ := margin_of_not_near s hs (C.lo e) (C.hi e) b.2.val x.2.val hxk hdom hnlo hnhi
    obtain ⟨p,hp⟩ := C.joined_of_margin s hs len err hsource hsmall (herr e) hl hr
    exact (OccurrenceMatching.Data.unmatched_iff _ b).mp hb p hp

include hs in
/-- The full block mass and hence the rounding charge use the total actual
traversal length, with no prescribed occurrence-count estimate. -/
theorem block_mass : s*(Fintype.card (Block s len) : ℝ) ≤ ∑ t, (len t : ℝ) := by
  have he : (Fintype.card (Block s len) : ℝ) = ∑ t, (blockCount s (len t) : ℝ) := by
    simp only [Block,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [he,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  simpa [mul_comm] using (count_bound s hs (len t)).1

theorem unmatched_bound (ν : E → ℤ)
    (hsmall : 2*(err : ℝ) < s-1)
    (herr : ∀ e, 2*|(C.offset e : ℝ)-(ν e : ℝ)*s|+4 ≤ err) :
    s*((C.matchingData s hs len err).unmatchedBlocks.card : ℝ) ≤
      (C.matchingData s hs len err).unpairedPositions.card +
      22*s*Fintype.card E + (∑ t, (len t : ℝ))/s := by
  have hm := OccurrenceMatching.Data.unmatched_mass (C.matchingData s hs len err)
    s hs.le (C.exceptional s len) (fun b => ?_) (fun b hb hn =>
      C.unmatched_unpaired s hs len err ν hsmall herr hb hn)
  · have hex : ((C.exceptional s len).card : ℝ) ≤ 22*Fintype.card E := by
      exact_mod_cast C.exceptional_card s len
    have hb : (Fintype.card (Block s len) : ℝ) ≤ (∑ t, (len t : ℝ))/s :=
      (le_div_iff₀ hs).mpr (by simpa [mul_comm] using block_mass s hs len)
    have hmul := mul_le_mul_of_nonneg_left hex hs.le
    nlinarith
  · change s-1 ≤ (blockPositions s hs len b).card
    rw [blockPositions_card]
    have hh := card_lower ((b.2.val : ℝ)*s) (((b.2.val : ℝ)+1)*s)
    simpa [block,mul_add,add_mul] using hh

end Comparisons
end TorsionFreeZeroDivisors.ComparedBlocks

end

end OAI
