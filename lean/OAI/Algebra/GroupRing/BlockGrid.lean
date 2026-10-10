import Mathlib

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.BlockGrid

/-- Partition the unit interval into N half-open equal cells. -/
def cell (N : ℕ) (hN : 0 < N) (x : ℝ) : Fin N :=
  ⟨⌊(N : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) (Int.fract_nonneg x))).mpr
    simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one x) (Nat.cast_pos.mpr hN)⟩

theorem same_cell {N : ℕ} (hN : 0 < N) {x y : ℝ} (he : cell N hN x = cell N hN y) :
    |Int.fract x - Int.fract y| < 1 / (N : ℝ) := by
  have hf := congrArg Fin.val he
  dsimp [cell] at hf
  have hx0 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg x))
  have hy0 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (Int.fract_nonneg y))
  have hx1 := Nat.lt_floor_add_one ((N : ℝ) * Int.fract x)
  have hy1 := Nat.lt_floor_add_one ((N : ℝ) * Int.fract y)
  rw [hf] at hx0 hx1
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [abs_lt]
  constructor
  · apply (neg_lt_iff_pos_add).mpr
    apply (mul_pos_iff_of_pos_left hNr).mp
    have hi : (N : ℝ) * (1 / N) = 1 := by field_simp
    nlinarith
  · apply (lt_div_iff₀ hNr).mpr
    nlinarith

/-- Simultaneous approximation in all d coordinates, with the exact
denominator bound N^d, by the pigeonhole principle. -/
theorem simultaneous {d N : ℕ} (hN : 0 < N) (a : Fin d → ℝ) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ N ^ d ∧
      ∃ z : Fin d → ℤ, ∀ i, |(u : ℝ) * a i - (z i : ℝ)| < 1 / (N : ℝ) := by
  classical
  let code : Fin (N ^ d + 1) → (Fin d → Fin N) :=
    fun k i => cell N hN ((k.val : ℝ) * a i)
  obtain ⟨j, k, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt code (by simp)
  have diff (j k : Fin (N^d+1)) (hjk : j.val < k.val) (he : code j = code k) :
      ∃ u : ℕ, 1 ≤ u ∧ u ≤ N^d ∧
        ∃ z : Fin d → ℤ, ∀ i, |(u : ℝ)*a i - (z i : ℝ)| < 1/(N : ℝ) := by
    refine ⟨k.val-j.val, by omega, by omega,
      (fun i => ⌊(k.val : ℝ)*a i⌋ - ⌊(j.val : ℝ)*a i⌋), ?_⟩
    intro i
    have hi := same_cell hN (congrFun he i).symm
    have hcast : ((k.val-j.val : ℕ) : ℝ) = (k.val : ℝ) - j.val :=
      Nat.cast_sub (Nat.le_of_lt hjk)
    simpa only [code] using (by
      rw [hcast, Int.cast_sub]
      convert hi using 1
      simp only [Int.fract]
      ring_nf)
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with hjk | hkj
  · exact diff j k hjk he
  · exact diff k j hkj he.symm

/-- Scaling the simultaneous approximation gives the common block
scale s=L/(uR), with error at most R/N for every prescribed offset. -/
theorem scale_approximation {d N : ℕ} (hN : 0 < N)
    (L R : ℝ) (hL : 0 < L) (hR : 0 < R) (offset : Fin d → ℝ) :
    ∃ u : ℕ, 1 ≤ u ∧ u ≤ N^d ∧
      ∃ z : Fin d → ℤ,
        let s := L / ((u : ℝ)*R)
        0 < s ∧ L / ((N^d : ℕ)*R) ≤ s ∧ s ≤ L/R ∧
          ∀ i, |offset i / s - R*(z i : ℝ)| < R / N := by
  obtain ⟨u, hu, hub, z, hz⟩ := simultaneous hN (fun i => offset i / L)
  have hur : (0 : ℝ) < u := by exact_mod_cast hu
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (0 : ℝ) < (N^d : ℕ) := by positivity
  refine ⟨u,hu,hub,z,?_,?_,?_,?_⟩
  · exact div_pos hL (mul_pos hur hR)
  · exact div_le_div_of_nonneg_left hL.le (mul_pos hur hR)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hub) hR.le)
  · apply div_le_div_of_nonneg_left hL.le hR
    simpa using mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ u by exact_mod_cast hu) hR.le
  · intro i
    have he := mul_lt_mul_of_pos_left (hz i) hR
    have hscalar : offset i / (L / ((u : ℝ)*R)) - R*(z i : ℝ) =
        R*((u : ℝ)*(offset i/L) - (z i : ℝ)) := by field_simp
    rw [hscalar, abs_mul, abs_of_pos hR]
    simpa [div_eq_mul_inv, mul_assoc] using he

end TorsionFreeZeroDivisors.BlockGrid

/-! Exact half-integer alignment, including the reflection endpoint conventions.
Uniform deficit bounds converge to zero relative to s
when |a/s-ν| does; no rounding of the prescribed real grid s is needed. -/
namespace TorsionFreeZeroDivisors.BlockAlignment

section
open scoped Classical

/-- Integer edge indices whose half-integer centers belong to a real interval. -/
def positions (lo hi : ℝ) : Finset ℤ := Finset.Ico ⌈lo-1/2⌉ ⌈hi-1/2⌉

theorem mem_positions {lo hi : ℝ} {q : ℤ} :
    q ∈ positions lo hi ↔ lo ≤ (q : ℝ)+1/2 ∧ (q : ℝ)+1/2 < hi := by
  simp only [positions,Finset.mem_Ico,Int.ceil_le,Int.lt_ceil]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

/-- Works even for a reversed/empty real interval. -/
theorem card_lower (lo hi : ℝ) : hi-lo-1 ≤ ((positions lo hi).card : ℝ) := by
  have h1 := Int.le_ceil (lo-1/2)
  have h2 := Int.ceil_lt_add_one (lo-1/2)
  have h3 := Int.le_ceil (hi-1/2)
  have h4 : (⌈hi-1/2⌉-⌈lo-1/2⌉ : ℤ) ≤ ((positions lo hi).card : ℤ) := by
    simp only [positions,Int.card_Ico]
    exact Int.self_le_toNat _
  have h5 : ((⌈hi-1/2⌉ : ℤ) : ℝ)-⌈lo-1/2⌉ ≤ ((positions lo hi).card : ℝ) := by exact_mod_cast h4
  linarith

theorem card_upper {lo hi : ℝ} (hab : lo ≤ hi) :
    ((positions lo hi).card : ℝ) ≤ hi-lo+1 := by
  have hc : ⌈lo-1/2⌉ ≤ ⌈hi-1/2⌉ := Int.ceil_mono (by linarith)
  have he : ((positions lo hi).card : ℤ) = ⌈hi-1/2⌉-⌈lo-1/2⌉ := by
    simp only [positions,Int.card_Ico]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hc)
  have he' : ((positions lo hi).card : ℝ) = ((⌈hi-1/2⌉ : ℤ) : ℝ)-⌈lo-1/2⌉ := by exact_mod_cast he
  have h1 := Int.le_ceil (lo-1/2)
  have h2 := Int.ceil_lt_add_one (hi-1/2)
  linarith

def block (s : ℝ) (k : ℤ) : Finset ℤ := positions ((k : ℝ)*s) (((k : ℝ)+1)*s)

def affine (reverse : Bool) (a q : ℤ) : ℤ := if reverse then a-1-q else q+a

def partnerIndex (reverse : Bool) (ν k : ℤ) : ℤ := if reverse then ν-k-1 else k+ν

def overlap (s : ℝ) (reverse : Bool) (a k ν : ℤ) : Finset ℤ :=
  (block s k).filter (fun q => affine reverse a q ∈ block s (partnerIndex reverse ν k))

/-- A central interval survives both translation and reflection. Using one
extra unit of margin removes the open/closed endpoint distinction. -/
theorem core_subset (s : ℝ) (reverse : Bool) (a k ν : ℤ) :
    positions ((k : ℝ)*s+(|a-(ν : ℝ)*s|+1))
      (((k : ℝ)+1)*s-(|a-(ν : ℝ)*s|+1)) ⊆ overlap s reverse a k ν := by
  intro q hq
  obtain ⟨hlo,hhi⟩ := mem_positions.mp hq
  have ha0 := abs_nonneg ((a : ℝ)-(ν : ℝ)*s)
  have ha1 := le_abs_self ((a : ℝ)-(ν : ℝ)*s)
  have ha2 := neg_abs_le ((a : ℝ)-(ν : ℝ)*s)
  refine Finset.mem_filter.mpr ⟨?_,?_⟩
  · apply mem_positions.mpr
    constructor <;> linarith
  · apply mem_positions.mpr
    cases reverse <;> simp only [affine,partnerIndex,Bool.false_eq_true,ite_false,ite_true,
      Int.cast_add,Int.cast_sub,Int.cast_one] <;> constructor <;> nlinarith

/-- An explicit o(s) deficit for the exact grid and signed isometry. -/
theorem overlap_deficit (s : ℝ) (hs : 0 ≤ s) (reverse : Bool) (a k ν : ℤ) :
    (((block s k).card - (overlap s reverse a k ν).card : ℕ) : ℝ) ≤
      2*|a-(ν : ℝ)*s|+4 := by
  have hlo := card_lower ((k : ℝ)*s+(|a-(ν : ℝ)*s|+1))
    (((k : ℝ)+1)*s-(|a-(ν : ℝ)*s|+1))
  have hsub := Finset.card_le_card (core_subset s reverse a k ν)
  have hsub' : ((positions ((k : ℝ)*s+(|a-(ν : ℝ)*s|+1))
    (((k : ℝ)+1)*s-(|a-(ν : ℝ)*s|+1))).card : ℝ) ≤ (overlap s reverse a k ν).card := by exact_mod_cast hsub
  have hhi := card_upper (lo := (k : ℝ)*s) (hi := ((k : ℝ)+1)*s) (by nlinarith)
  have hcard : (overlap s reverse a k ν).card ≤ (block s k).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Nat.cast_sub hcard]
  dsimp [block] at *
  linarith

/-- An overlap larger than half of its block dominates every disjoint one. -/
theorem dominant_unique {B D E : Finset ℤ} (hD : D ⊆ B) (hE : E ⊆ B)
    (hdis : Disjoint D E) (hd : B.card < 2*D.card) (he : B.card < 2*E.card) : False := by
  have hc : D.card+E.card ≤ B.card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hD hE)
  omega

end

open scoped Classical BigOperators

def inverseOffset (reverse : Bool) (a : ℤ) : ℤ := if reverse then a else -a

theorem affine_inverse (reverse : Bool) (a q : ℤ) :
    affine reverse (inverseOffset reverse a) (affine reverse a q) = q := by
  cases reverse <;> simp [affine,inverseOffset]

theorem affine_injective (reverse : Bool) (a : ℤ) : Function.Injective (affine reverse a) :=
  Function.LeftInverse.injective (affine_inverse reverse a)

theorem partner_inverse (reverse : Bool) (ν k : ℤ) :
    partnerIndex reverse (inverseOffset reverse ν) (partnerIndex reverse ν k) = k := by
  cases reverse <;> simp [partnerIndex,inverseOffset]; omega

/-- The overlap on the partner block is exactly the image of the first overlap. -/
def overlapEquiv (s : ℝ) (reverse : Bool) (a k ν : ℤ) :
    overlap s reverse a k ν ≃
      overlap s reverse (inverseOffset reverse a) (partnerIndex reverse ν k) (inverseOffset reverse ν) where
  toFun q := ⟨affine reverse a q.val, by
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp q.property
    apply Finset.mem_filter.mpr
    exact ⟨hp,by rw [affine_inverse,partner_inverse]; exact hq⟩⟩
  invFun q := ⟨affine reverse (inverseOffset reverse a) q.val,by
    obtain ⟨hq,hp⟩ := Finset.mem_filter.mp q.property
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · rwa [partner_inverse] at hp
    · have he : affine reverse a (affine reverse (inverseOffset reverse a) q.val) = q.val := by
        cases reverse <;> simp [affine,inverseOffset]
      rw [he]
      exact hq⟩
  left_inv q := Subtype.ext (affine_inverse reverse a q.val)
  right_inv q := by
    apply Subtype.ext
    cases reverse <;> simp [affine,inverseOffset]

theorem block_disjoint (s : ℝ) (hs : 0 < s) {k j : ℤ} (hne : k ≠ j) :
    Disjoint (block s k) (block s j) := by
  apply Finset.disjoint_left.mpr
  intro q hk hj
  obtain ⟨hk0,hk1⟩ := mem_positions.mp hk
  obtain ⟨hj0,hj1⟩ := mem_positions.mp hj
  rcases lt_or_gt_of_ne hne with hkj | hjk
  · have hh : (k : ℝ)+1 ≤ j := by exact_mod_cast hkj
    nlinarith
  · have hh : (j : ℝ)+1 ≤ k := by exact_mod_cast hjk
    nlinarith

def blockCount (s : ℝ) (ell : ℕ) : ℕ := ⌊(ell : ℝ)/s⌋₊

def tail (s : ℝ) (ell : ℕ) : Finset ℤ := positions ((blockCount s ell : ℝ)*s) ell

theorem count_bound (s : ℝ) (hs : 0 < s) (ell : ℕ) :
    (blockCount s ell : ℝ)*s ≤ ell ∧ (ell : ℝ) < (blockCount s ell+1)*s := by
  have h1 := Nat.floor_le (div_nonneg (Nat.cast_nonneg ell) hs.le)
  have h2 := Nat.lt_floor_add_one ((ell : ℝ)/s)
  constructor
  · exact (le_div_iff₀ hs).mp h1
  · exact (div_lt_iff₀ hs).mp h2

theorem tail_bound (s : ℝ) (hs : 0 < s) (ell : ℕ) :
    ((tail s ell).card : ℝ) ≤ s+1 := by
  have he := count_bound s hs ell
  have hh := card_upper he.1
  dsimp [tail]
  linarith

/-- Literal partition into full blocks and the end fragment. -/
theorem full_or_tail (s : ℝ) (hs : 0 < s) (ell : ℕ) {q : ℤ}
    (hq : q ∈ positions 0 ell) :
    (∃ k : Fin (blockCount s ell), q ∈ block s k.val) ∨ q ∈ tail s ell := by
  obtain ⟨hq0,hq1⟩ := mem_positions.mp hq
  by_cases he : (q : ℝ)+1/2 < (blockCount s ell : ℝ)*s
  · let k := ⌊((q : ℝ)+1/2)/s⌋₊
    have hk : k < blockCount s ell := by
      apply (Nat.floor_lt (div_nonneg hq0 hs.le)).mpr
      exact (div_lt_iff₀ hs).mpr he
    left
    refine ⟨⟨k,hk⟩,?_⟩
    apply mem_positions.mpr
    simp only [Int.cast_natCast]
    exact ⟨(le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hq0 hs.le)),
      (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (((q : ℝ)+1/2)/s))⟩
  · right
    exact mem_positions.mpr ⟨not_lt.mp he,hq1⟩

/-- A full block is entirely within its marked chain. -/
theorem full_subset (s : ℝ) (hs : 0 < s) (ell : ℕ) (k : Fin (blockCount s ell)) :
    block s k.val ⊆ positions 0 ell := by
  intro q hq
  obtain ⟨hlo,hhi⟩ := mem_positions.mp hq
  apply mem_positions.mpr
  have hk : (k.val : ℝ)+1 ≤ blockCount s ell := by exact_mod_cast k.isLt
  have he := (count_bound s hs ell).1
  simp only [Int.cast_natCast] at hlo hhi
  constructor
  · have hkn : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    nlinarith
  · nlinarith

/-- A grid block situated inside a comparison with one-block margins has a
full indicated target block. This includes negative offsets and reflections. -/
theorem partner_full (s : ℝ) (hs : 0 < s) (reverse : Bool) (a k ν : ℤ)
    (lo hi ell : ℝ) (herr : |(a : ℝ)-(ν : ℝ)*s| ≤ s)
    (hlo : lo ≤ (k : ℝ)*s-s) (hhi : ((k : ℝ)+1)*s+s ≤ hi)
    (htarget : if reverse then 0 ≤ (a : ℝ)-hi ∧ (a : ℝ)-lo ≤ ell
      else 0 ≤ lo+(a : ℝ) ∧ hi+(a : ℝ) ≤ ell) :
    0 ≤ partnerIndex reverse ν k ∧ ((partnerIndex reverse ν k : ℤ)+1 : ℝ)*s ≤ ell := by
  have he1 : (a : ℝ)-(ν : ℝ)*s ≤ s := (le_abs_self _).trans herr
  have he2 : -s ≤ (a : ℝ)-(ν : ℝ)*s := by
    have hh := neg_abs_le ((a : ℝ)-(ν : ℝ)*s)
    linarith
  cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,partnerIndex,
    Int.cast_add,Int.cast_sub,Int.cast_one] at htarget ⊢
  · constructor
    · have hz : (0 : ℝ) ≤ (k : ℝ)+(ν : ℝ) := by nlinarith [htarget.1]
      exact_mod_cast hz
    · nlinarith [htarget.2]
  · constructor
    · have hz : (0 : ℝ) ≤ (ν : ℝ)-(k : ℝ)-1 := by nlinarith [htarget.1]
      exact_mod_cast hz
    · nlinarith [htarget.2]

theorem inverse_error (reverse : Bool) (a ν : ℤ) (s : ℝ) :
    |(inverseOffset reverse a : ℝ)-(inverseOffset reverse ν : ℝ)*s| =
      |(a : ℝ)-(ν : ℝ)*s| := by
  cases reverse
  · simp only [inverseOffset,Bool.false_eq_true,ite_false,Int.cast_neg]
    have he : -(a : ℝ)- -(ν : ℝ)*s = -((a : ℝ)-(ν : ℝ)*s) := by ring
    rw [he,abs_neg]
  · rfl

/-- Uniformly bounded exceptional grid indices near one real cut. -/
def nearCut (s t : ℝ) : Finset ℤ := Finset.Icc ⌈t/s-5⌉ ⌊t/s+5⌋

theorem mem_nearCut (s t : ℝ) (k : ℤ) :
    k ∈ nearCut s t ↔ |(k : ℝ)-t/s| ≤ 5 := by
  simp only [nearCut,Finset.mem_Icc,Int.ceil_le,Int.le_floor,abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem nearCut_card (s t : ℝ) : (nearCut s t).card ≤ 11 := by
  have h1 := Int.le_ceil (t/s-5)
  have h2 := Int.floor_le (t/s+5)
  have hi : ⌊t/s+5⌋+1-⌈t/s-5⌉ ≤ (11 : ℤ) := by
    have hr : ((⌊t/s+5⌋ : ℤ) : ℝ)+1-⌈t/s-5⌉ ≤ 11 := by linarith
    exact_mod_cast hr
  simp only [nearCut,Int.card_Icc]
  omega

/-- A block containing a compared position and avoiding both endpoint
neighborhoods is deep inside that exact comparison interval. -/
theorem margin_of_not_near (s : ℝ) (hs : 0 < s) (lo hi : ℝ) (k q : ℤ)
    (hq : q ∈ block s k) (hdom : q ∈ positions lo hi)
    (hnlo : k ∉ nearCut s lo) (hnhi : k ∉ nearCut s hi) :
    lo ≤ (k : ℝ)*s-s ∧ ((k : ℝ)+1)*s+s ≤ hi := by
  have hlo := not_le.mp (mt (mem_nearCut s lo k).mpr hnlo)
  have hhi := not_le.mp (mt (mem_nearCut s hi k).mpr hnhi)
  obtain ⟨hk0,hk1⟩ := mem_positions.mp hq
  obtain ⟨hq0,hq1⟩ := mem_positions.mp hdom
  rcases (lt_abs.mp hlo) with hl | hl
  · have hz : 5+lo/s < (k : ℝ) := by linarith
    have hz' := (div_lt_iff₀ hs).mp (show lo/s < (k : ℝ)-5 by linarith)
    constructor
    · nlinarith
    · rcases (lt_abs.mp hhi) with hh | hh
      · have ht := (div_lt_iff₀ hs).mp (show hi/s < (k : ℝ)-5 by linarith)
        nlinarith
      · have ht := (lt_div_iff₀ hs).mp (show (k : ℝ)+5 < hi/s by linarith)
        nlinarith
  · have ht := (lt_div_iff₀ hs).mp (show (k : ℝ)+5 < lo/s by linarith)
    nlinarith

end TorsionFreeZeroDivisors.BlockAlignment

/-! Extraction of the actual partial matching of block occurrences from the
original comparison pairing. Comparison sides are retained,
so a block cannot join itself by aggregating several short comparisons. -/

end

end OAI
