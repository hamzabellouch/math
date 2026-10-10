import Mathlib
import OAI.Algebra.GroupRing.EntropyStages

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.AffineIntervals
open scoped Classical
open BlockAlignment

/-- Boundary action of a signed interval isometry. On half-integer centers it
agrees with the manuscript's letter-index affine action. -/
def boundary (r : Bool) (a x : ℤ) : ℤ := if r then a-x else x+a

def compOffset (r : Bool) (a b : ℤ) : ℤ := if r then a-b else a+b

lemma affine_comp (r s : Bool) (a b x : ℤ) :
    affine r a (affine s b x)=affine (r.xor s) (compOffset r a b) x := by
  cases r <;> cases s <;> simp [affine,compOffset] <;> ring

lemma boundary_comp (r s : Bool) (a b x : ℤ) :
    boundary r a (boundary s b x)=boundary (r.xor s) (compOffset r a b) x := by
  cases r <;> cases s <;> simp [boundary,compOffset] <;> ring

lemma integer_positions (a b : ℤ) : positions a b=Finset.Ico a b := by
  ext x
  rw [mem_positions,Finset.mem_Ico]
  constructor
  · rintro ⟨h1,h2⟩
    constructor
    · by_contra h
      have : x+1≤a := by omega
      have : (x:ℝ)+1≤a := by exact_mod_cast this
      linarith
    · by_contra h
      have : b≤x := by omega
      have : (b:ℝ)≤x := by exact_mod_cast this
      linarith
  · rintro ⟨h1,h2⟩
    have h1' : (a:ℝ)≤x := by exact_mod_cast h1
    have h2' : (x:ℝ)+1≤b := by exact_mod_cast (show x+1≤b by omega)
    constructor <;> linarith

lemma nat_positions (n : ℕ) : positions 0 (n : ℝ)=Finset.Ico (0:ℤ) (n:ℤ) := by
  simpa only [Int.cast_zero,Int.cast_natCast] using integer_positions (0:ℤ) (n:ℤ)

/-- Exact integer endpoints of the inverse image; reflection does not incur
any rounding loss on the source half-integer convention. -/
def preLo (r : Bool) (a lo hi : ℤ) : ℤ := if r then a-hi else lo-a
def preHi (r : Bool) (a lo hi : ℤ) : ℤ := if r then a-lo else hi-a

lemma mem_preimage (r : Bool) (a lo hi x : ℤ) :
    affine r a x∈Finset.Ico lo hi ↔ x∈Finset.Ico (preLo r a lo hi) (preHi r a lo hi) := by
  cases r <;> simp only [affine,preLo,preHi,Bool.false_eq_true,ite_false,ite_true,Finset.mem_Ico] <;> omega

lemma preimage_bounds (r : Bool) (a lo hi l h : ℤ)
    (hl : preLo r a lo hi≤l) (hh : h≤preHi r a lo hi) :
    if r then lo≤a-h ∧ a-l≤hi else lo≤l+a ∧ h+a≤hi := by
  cases r <;> simp only [preLo,preHi,Bool.false_eq_true,ite_false,ite_true] at * <;> omega

/-- Empty comparison sides may be placed at the preimage of target boundary
zero; this has no occurrences and satisfies the global range condition. -/
def anchor (r : Bool) (a : ℤ) : ℤ := if r then a else -a

lemma anchor_bounds (r : Bool) (a : ℤ) (n : ℕ) :
    if r then 0≤a-anchor r a ∧ a-anchor r a≤n
    else 0≤anchor r a+a ∧ anchor r a+a≤n := by
  cases r <;> simp [anchor]

end TorsionFreeZeroDivisors.AffineIntervals
namespace TorsionFreeZeroDivisors.ChunkComparisons
open scoped Classical
open BlockAlignment ComparedBlocks AffineIntervals EntropyStages

variable {P T E : Type*} {lp : P → ℕ} {lt : T → ℕ}

/-- A literal partition into signed integer chunks, not a count of formal pieces. -/
structure Chunking (lp : P → ℕ) (lt : T → ℕ) where
  equiv : Position lt ≃ Position lp
  path : T → P
  reverse : T → Bool
  offset : T → ℤ
  source : ∀ x, (equiv x).1 = path x.1
  coordinate : ∀ x, (equiv x).2.val = affine (reverse x.1) (offset x.1) x.2.val

lemma position_ext {x y : Position lp} (hs : x.1=y.1) (hc : x.2.val=y.2.val) : x=y := by
  rcases x with ⟨x,q⟩; rcases y with ⟨y,r⟩
  dsimp at hs hc
  subst y
  congr 1
  exact Subtype.ext hc

namespace Chunking
variable (K : Chunking lp lt) (C : Comparisons (E := E) lp)

def pairing : Pairing (Position lt) where
  partner x := K.equiv.symm (C.pairing.partner (K.equiv x))
  involutive x := by
    dsimp
    rw [K.equiv.apply_symm_apply,C.pairing.involutive (K.equiv x),K.equiv.symm_apply_apply]

lemma partner_image (x : Position lt) :
    K.equiv ((K.pairing C).partner x)=C.pairing.partner (K.equiv x) := by
  simp [pairing]

def rev (e : E) (t u : T) : Bool :=
  (K.reverse u).xor ((C.reverse e).xor (K.reverse t))

def off (e : E) (t u : T) : ℤ :=
  compOffset (K.reverse u) (inverseOffset (K.reverse u) (K.offset u))
    (compOffset (C.reverse e) (C.offset e) (K.offset t))

lemma new_affine (e : E) (t u : T) (q : ℤ) :
    affine (K.rev C e t u) (K.off C e t u) q =
      affine (K.reverse u) (inverseOffset (K.reverse u) (K.offset u))
        (affine (C.reverse e) (C.offset e) (affine (K.reverse t) (K.offset t) q)) := by
  rw [affine_comp (C.reverse e) (K.reverse t),affine_comp]
  rfl

lemma new_affine_image (e : E) (t u : T) (q : ℤ) :
    affine (K.reverse u) (K.offset u) (affine (K.rev C e t u) (K.off C e t u) q) =
      affine (C.reverse e) (C.offset e) (affine (K.reverse t) (K.offset t) q) := by
  rw [K.new_affine]
  generalize affine (C.reverse e) (C.offset e) (affine (K.reverse t) (K.offset t) q) = z
  cases K.reverse u <;> simp [affine,inverseOffset]

lemma partner_coordinate {x : Position lt} {e : E} (he : C.side (K.equiv x)=some e) :
    ((K.pairing C).partner x).2.val =
      affine (K.rev C e x.1 ((K.pairing C).partner x).1)
        (K.off C e x.1 ((K.pairing C).partner x).1) x.2.val := by
  have h := C.partner_coordinate (K.equiv x) e he
  rw [← K.partner_image, K.coordinate, K.coordinate] at h
  apply affine_injective (K.reverse ((K.pairing C).partner x).1)
    (K.offset ((K.pairing C).partner x).1)
  rw [K.new_affine_image]
  exact h

/-- The image of an old partner is in a given chunk precisely when the
conjugate affine index is in that chunk. -/
lemma partner_chunk_iff {x : Position lt} {e : E} {u : T}
    (he : C.side (K.equiv x)=some e) (hu : K.path u=C.source (C.flip e)) :
    ((K.pairing C).partner x).1=u ↔
      affine (K.rev C e x.1 u) (K.off C e x.1 u) x.2.val ∈ positions 0 (lt u) := by
  constructor
  · intro h
    have hm := ((K.pairing C).partner x).2.property
    rw [K.partner_coordinate C he,h] at hm
    exact hm
  · intro hm
    let y : Position lt := ⟨u,⟨_,hm⟩⟩
    have hy : K.equiv y=C.pairing.partner (K.equiv x) := by
      apply position_ext
      · rw [K.source,C.partner_source _ _ he]
        exact hu
      · rw [K.coordinate,C.partner_coordinate _ _ he,K.coordinate]
        exact K.new_affine_image C e x.1 u x.2.val
    have : y=(K.pairing C).partner x := K.equiv.injective (hy.trans (K.partner_image C x).symm)
    exact (congrArg Sigma.fst this).symm

variable (lo hi : E → ℤ)

def rawLo (e : E) (t u : T) : ℤ :=
  max 0 (max (preLo (K.reverse t) (K.offset t) (lo e) (hi e))
    (preLo (K.rev C e t u) (K.off C e t u) 0 (lt u)))
def rawHi (e : E) (t u : T) : ℤ :=
  min (lt t) (min (preHi (K.reverse t) (K.offset t) (lo e) (hi e))
    (preHi (K.rev C e t u) (K.off C e t u) 0 (lt u)))

def valid (e : E) (t u : T) : Prop :=
  K.path t=C.source e ∧ K.path u=C.source (C.flip e) ∧
    K.rawLo C lo hi e t u ≤ K.rawHi C lo hi e t u

def lower (e : E) (t u : T) : ℤ :=
  if K.valid C lo hi e t u then K.rawLo C lo hi e t u
  else anchor (K.rev C e t u) (K.off C e t u)
def upper (e : E) (t u : T) : ℤ :=
  if K.valid C lo hi e t u then K.rawHi C lo hi e t u
  else anchor (K.rev C e t u) (K.off C e t u)

variable (hlo : ∀ e, C.lo e=(lo e : ℝ)) (hhi : ∀ e, C.hi e=(hi e : ℝ))

include hlo hhi in
lemma interval_iff (x : Position lt) (e : E) (u : T) :
    x.2.val ∈ positions (K.lower C lo hi e x.1 u) (K.upper C lo hi e x.1 u) ↔
      C.side (K.equiv x)=some e ∧ ((K.pairing C).partner x).1=u := by
  rw [integer_positions]
  by_cases hv : K.valid C lo hi e x.1 u
  · rw [lower,upper,ite_eq_left hv,ite_eq_left hv]
    have hx := x.2.property
    simp only [nat_positions] at hx
    have hpart := hv.1
    have htarget := hv.2.1
    have hmem : x.2.val ∈ Finset.Ico (K.rawLo C lo hi e x.1 u) (K.rawHi C lo hi e x.1 u) ↔
        affine (K.reverse x.1) (K.offset x.1) x.2.val ∈ Finset.Ico (lo e) (hi e) ∧
        affine (K.rev C e x.1 u) (K.off C e x.1 u) x.2.val ∈ Finset.Ico (0:ℤ) (lt u:ℤ) := by
      rw [mem_preimage,mem_preimage]
      simp only [rawLo,rawHi,Finset.mem_Ico,max_le_iff,lt_min_iff]
      simp only [Finset.mem_Ico] at hx
      omega
    rw [hmem]
    have hside : C.side (K.equiv x)=some e ↔
        affine (K.reverse x.1) (K.offset x.1) x.2.val ∈ Finset.Ico (lo e) (hi e) := by
      rw [C.side_iff,K.coordinate]
      simp only [K.source,hlo,hhi,integer_positions]
      exact and_iff_right hpart
    rw [← hside]
    apply and_congr_right
    intro he
    rw [K.partner_chunk_iff C he htarget]
    simp only [nat_positions]
  · rw [lower,upper,ite_eq_right hv,ite_eq_right hv,Finset.Ico_self]
    simp only [Finset.notMem_empty,false_iff,not_and]
    intro he hu
    apply hv
    have hp := (C.side_iff (K.equiv x) e).mp he
    have ht := C.partner_source (K.equiv x) e he
    rw [← K.partner_image,K.source,hu] at ht
    refine ⟨(K.source x).symm.trans hp.1,ht,?_⟩
    have hq := hp.2
    rw [hlo,hhi,integer_positions,K.coordinate,mem_preimage] at hq
    have hr := (K.partner_chunk_iff C he ht).mp hu
    simp only [nat_positions] at hr
    rw [mem_preimage] at hr
    have hx := x.2.property
    simp only [nat_positions] at hx
    simp only [Finset.mem_Ico] at hx hq hr
    simp only [rawLo,rawHi,max_le_iff,le_min_iff]
    omega

lemma range_bounds (e : E) (t u : T) :
    if K.rev C e t u then
      0≤K.off C e t u-K.upper C lo hi e t u ∧ K.off C e t u-K.lower C lo hi e t u≤lt u
    else 0≤K.lower C lo hi e t u+K.off C e t u ∧ K.upper C lo hi e t u+K.off C e t u≤lt u := by
  by_cases hv : K.valid C lo hi e t u
  · simp only [lower,upper,ite_eq_left hv]
    apply preimage_bounds
    · exact (le_max_right _ _).trans (le_max_right _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  · simp only [lower,upper,ite_eq_right hv]
    exact anchor_bounds _ _ _

def side (x : Position lt) : Option (E×T×T) :=
  (C.side (K.equiv x)).map (fun e => (e,x.1,((K.pairing C).partner x).1))

lemma side_iff (x : Position lt) (e : E) (t u : T) :
    K.side C x=some (e,t,u) ↔
      C.side (K.equiv x)=some e ∧ x.1=t ∧ ((K.pairing C).partner x).1=u := by
  cases h : C.side (K.equiv x) <;> simp [side,h,Prod.mk.injEq]

/-- Split every side at the boundaries of both chunks. Empty pieces carry no
positions; their chosen endpoint maintains the exact range convention. -/
def comparisons : Comparisons (E := E×T×T) lt where
  pairing := K.pairing C
  side := K.side C
  flip a := (C.flip a.1,a.2.2,a.2.1)
  flip_inv a := by rcases a with ⟨e,t,u⟩; simp [C.flip_inv e]
  flip_ne a := by
    intro h
    exact C.flip_ne a.1 (congrArg Prod.fst h)
  side_partner x a ha := by
    rcases a with ⟨e,t,u⟩
    obtain ⟨he,ht,hu⟩ := (K.side_iff C x e t u).mp ha
    apply (K.side_iff C _ _ _ _).mpr
    refine ⟨?_,hu,?_⟩
    · rw [K.partner_image]
      exact C.side_partner (K.equiv x) e he
    · rw [(K.pairing C).involutive x]
      exact ht
  none_iff x := by
    simp only [side,Option.map_eq_none_iff,C.none_iff]
    constructor
    · intro h
      apply K.equiv.injective
      rw [K.partner_image,h]
    · intro h
      rw [← K.partner_image,h]
  source a := a.2.1
  lo a := K.lower C lo hi a.1 a.2.1 a.2.2
  hi a := K.upper C lo hi a.1 a.2.1 a.2.2
  reverse a := K.rev C a.1 a.2.1 a.2.2
  offset a := K.off C a.1 a.2.1 a.2.2
  side_iff x a := by
    rcases a with ⟨e,t,u⟩
    rw [K.side_iff]
    constructor
    · rintro ⟨he,ht,hu⟩
      refine ⟨ht,?_⟩
      subst t
      exact (K.interval_iff C lo hi hlo hhi x e u).mpr ⟨he,hu⟩
    · rintro ⟨ht,hm⟩
      change x.1=t at ht
      subst t
      obtain ⟨he,hu⟩ := (K.interval_iff C lo hi hlo hhi x e u).mp hm
      exact ⟨he,rfl,hu⟩
  partner_source x a ha := ((K.side_iff C x a.1 a.2.1 a.2.2).mp ha).2.2
  partner_coordinate x a ha := by
    obtain ⟨he,ht,hu⟩ := (K.side_iff C x a.1 a.2.1 a.2.2).mp ha
    simpa only [ht,hu] using K.partner_coordinate C he
  target_range a := by
    have h := K.range_bounds C lo hi a.1 a.2.1 a.2.2
    cases hr : K.rev C a.1 a.2.1 a.2.2 <;> simp only [hr,Bool.false_eq_true,ite_false,ite_true] at h ⊢
    · exact_mod_cast h
    · exact_mod_cast h

lemma fixed_iff (x : Position lt) :
    (K.pairing C).partner x=x ↔ C.pairing.partner (K.equiv x)=K.equiv x := by
  constructor
  · intro h
    rw [← K.partner_image,h]
  · intro h
    apply K.equiv.injective
    rw [K.partner_image,h]

def unpairedEquiv : {x : Position lt // (K.pairing C).partner x=x} ≃
    {x : Position lp // C.pairing.partner x=x} :=
  K.equiv.subtypeEquiv (K.fixed_iff C)

/-- Splitting and orientation normalization neither deletes nor duplicates an
unpaired occurrence. -/
theorem unpaired_card [Fintype P] [Fintype T] :
    Fintype.card {x : Position lt // (K.comparisons C lo hi hlo hhi).pairing.partner x=x} =
      Fintype.card {x : Position lp // C.pairing.partner x=x} :=
  Fintype.card_congr (K.unpairedEquiv C)

lemma xor_labels {A : Type*} (bar : A → A) (hb : Function.Involutive bar)
    (r s t : Bool) (x y : A)
    (h : (if r then bar x else x) = if s then
      bar (if t then bar y else y) else (if t then bar y else y)) :
    x = if t.xor (s.xor r) then bar y else y := by
  have hbb (z : A) : bar (bar z)=z := hb z
  cases r <;> cases s <;> cases t <;> simp only [Bool.xor_false,Bool.xor_true,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true,hbb] at h ⊢
  all_goals first | exact h | simpa only [hbb] using congrArg bar h

/-- Every literal compatible labeling survives splitting with exactly the
xor of the path comparison and the two chain orientations. -/
theorem compatible {A : Type*} (bar : A → A) (hb : Function.Involutive bar)
    (old : Position lp → A) (word : Position lt → A)
    (hn : ∀ x,old (K.equiv x)=if K.reverse x.1 then bar (word x) else word x)
    (hc : ∀ x e,C.side x=some e → old x = if C.reverse e then
      bar (old (C.pairing.partner x)) else old (C.pairing.partner x)) :
    ∀ x a, (K.comparisons C lo hi hlo hhi).side x=some a →
      word x=if (K.comparisons C lo hi hlo hhi).reverse a then
        bar (word ((K.comparisons C lo hi hlo hhi).pairing.partner x))
      else word ((K.comparisons C lo hi hlo hhi).pairing.partner x) := by
  intro x a ha
  obtain ⟨he,ht,hu⟩ := (K.side_iff C x a.1 a.2.1 a.2.2).mp ha
  have h := hc (K.equiv x) a.1 he
  rw [← K.partner_image,hn,hn] at h
  have h' := xor_labels bar hb (K.reverse x.1) (C.reverse a.1)
    (K.reverse ((K.pairing C).partner x).1) (word x) (word ((K.pairing C).partner x)) h
  change word x=(if K.rev C a.1 a.2.1 a.2.2 then
    bar (word ((K.pairing C).partner x)) else word ((K.pairing C).partner x))
  dsimp only [rev]
  exact h'.trans (by congr 1; simp only [ht,hu])

end Chunking
end TorsionFreeZeroDivisors.ChunkComparisons

namespace TorsionFreeZeroDivisors.FiniteChunking
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks AffineIntervals ChunkComparisons

variable {n : ℕ}

def before (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun j => j < i)
def start (f : Fin n → ℕ) (i : Fin n) : ℕ := ∑ j∈before i,f j

lemma not_before (i : Fin n) : i∉before i := by simp [before]

lemma start_next (f : Fin n → ℕ) {i j : Fin n} (h : i < j) :
    start f i+f i ≤ start f j := by
  rw [start,add_comm,← Finset.sum_insert (not_before i)]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl|hk
  · simpa [before] using h
  · have hk' : k < i := by simpa [before] using hk
    simpa [before] using hk'.trans h

lemma start_end (f : Fin n → ℕ) (i : Fin n) : start f i+f i ≤ ∑ j,f j := by
  rw [start,add_comm,← Finset.sum_insert (not_before i)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def localIndex (r : Bool) (n : ℕ) (q : ℤ) : ℤ := affine r (if r then n else 0) q

lemma local_bounds (r : Bool) (n : ℕ) {q : ℤ} (hq : q∈positions 0 n) :
    0≤localIndex r n q ∧ localIndex r n q<n := by
  simp only [nat_positions,Finset.mem_Ico] at hq
  cases r <;> simp only [localIndex,affine,Bool.false_eq_true,ite_false,ite_true] <;> omega

lemma affine_offset (r : Bool) (pre len : ℕ) (q : ℤ) :
    affine r (pre+(if r then (len:ℤ) else 0)) q = pre+localIndex r len q := by
  cases r <;> simp [localIndex,affine] <;> omega

lemma positions_card (n : ℕ) : (positions 0 n).card=n := by
  rw [nat_positions,Int.card_Ico,sub_zero,Int.toNat_natCast]

lemma position_card {T : Type*} [Fintype T] (len : T → ℕ) :
    Fintype.card (Position len)=∑ t,len t := by
  simp only [Position,Fintype.card_sigma,Fintype.card_coe,positions_card]

variable {P : Type*} [Fintype P] (chunks : P → ℕ)
  (len : (p : P) → Fin (chunks p) → ℕ) (rev : (p : P) → Fin (chunks p) → Bool)

abbrev Traversal := (p : P) × Fin (chunks p)
abbrev traversalLength : Traversal chunks → ℕ := fun t => len t.1 t.2
def pathLength (p : P) : ℕ := ∑ i,len p i

def offset (t : Traversal chunks) : ℤ := start (len t.1) t.2 + if rev t.1 t.2 then (len t.1 t.2:ℤ) else 0

def image (x : Position (traversalLength chunks len)) : Position (pathLength chunks len) :=
  ⟨x.1.1,⟨affine (rev x.1.1 x.1.2) (offset chunks len rev x.1) x.2.val,by
    simp only [nat_positions,Finset.mem_Ico]
    have hq := local_bounds (rev x.1.1 x.1.2) (len x.1.1 x.1.2) x.2.property
    have hp : (start (len x.1.1) x.1.2:ℤ)+len x.1.1 x.1.2 ≤ pathLength chunks len x.1.1 := by
      exact_mod_cast start_end (len x.1.1) x.1.2
    rw [offset,affine_offset]
    have hz : (0:ℤ)≤ start (len x.1.1) x.1.2 := Int.natCast_nonneg _
    omega⟩⟩

omit [Fintype P] in
lemma image_val (x : Position (traversalLength chunks len)) :
    (image chunks len rev x).2.val =
      start (len x.1.1) x.1.2+localIndex (rev x.1.1 x.1.2) (len x.1.1 x.1.2) x.2.val :=
  affine_offset _ _ _ _

omit [Fintype P] in
lemma image_injective : Function.Injective (image chunks len rev) := by
  rintro ⟨⟨p,i⟩,q⟩ ⟨⟨r,j⟩,v⟩ hh
  have hp : p=r := congrArg Sigma.fst hh
  subst r
  have hc := congrArg (fun x : Position (pathLength chunks len) => x.2.val) hh
  rw [image_val,image_val] at hc
  dsimp only at hc
  have hq := local_bounds (rev p i) (len p i) q.property
  have hv := local_bounds (rev p j) (len p j) v.property
  have he : i=j := by
    rcases lt_trichotomy i j with hij|hij|hji
    · have hpre : (start (len p) i:ℤ)+len p i ≤ start (len p) j := by
        exact_mod_cast start_next (len p) hij
      omega
    · exact hij
    · have hpre : (start (len p) j:ℤ)+len p j ≤ start (len p) i := by
        exact_mod_cast start_next (len p) hji
      omega
  subst j
  have hqv : q=v := by
    apply Subtype.ext
    apply affine_injective (rev p i) (if rev p i then (len p i:ℤ) else 0)
    unfold localIndex at hc
    omega
  subst v
  rfl

/-- The prescribed offsets define an actual equivalence. In particular, this
partition covers every old letter even when a path is empty. -/
def equiv : Position (traversalLength chunks len) ≃ Position (pathLength chunks len) :=
  Equiv.ofBijective (image chunks len rev) <|
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨image_injective chunks len rev,by
      simp only [position_card,Fintype.sum_sigma,traversalLength,pathLength]⟩

def chunking : Chunking (pathLength chunks len) (traversalLength chunks len) where
  equiv := equiv chunks len rev
  path t := t.1
  reverse t := rev t.1 t.2
  offset := offset chunks len rev
  source _ := rfl
  coordinate _ := rfl

end TorsionFreeZeroDivisors.FiniteChunking

end

end OAI
