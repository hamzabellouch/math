import OAI.Combinatorics.EditDistance.DelimiterAlignment

namespace OAI

/-!
# Binary delimiter codes and padding
-/

namespace EditCode
open EditDistortion
variable {A : Type*} {t : ℕ}

def width (t : ℕ) : ℕ := 2 * t + 3

def bit (label : A → Fin t → Bool) (a : A) (r : ℕ) : Bool :=
  if r < 2 then true else
    if h : r % 2 = 1 ∧ r / 2 - 1 < t then label a ⟨r / 2 - 1,h.2⟩ else false

def block (label : A → Fin t → Bool) (a : A) : List Bool :=
  List.ofFn (fun r : Fin (width t) => bit label a r)

def encode (label : A → Fin t → Bool) (x : List A) : List Bool := x.flatMap (block label)

def padded (label : A → Fin t → Bool) (x : List A) (r : ℕ) : List Bool :=
  encode label x ++ List.replicate r false

@[simp] lemma block_length (label : A → Fin t → Bool) (a : A) :
    (block label a).length = width t := List.length_ofFn

@[simp] lemma width_pos : 0 < width t := by unfold width; omega

@[simp] lemma encode_length (label : A → Fin t → Bool) (x : List A) :
    (encode label x).length = width t * x.length := by
  induction x with
  | nil => simp [encode]
  | cons a x ih => simp_all [encode, Nat.mul_add, Nat.add_comm]

@[simp] lemma padded_length (label : A → Fin t → Bool) (x : List A) (r : ℕ) :
    (padded label x r).length = width t * x.length + r := by simp [padded]

@[simp] lemma bit_zero (label : A → Fin t → Bool) (a : A) : bit label a 0 = true := by simp [bit]
@[simp] lemma bit_one (label : A → Fin t → Bool) (a : A) : bit label a 1 = true := by simp [bit]

lemma bit_label (label : A → Fin t → Bool) (a : A) (i : Fin t) :
    bit label a (2 * i.val + 3) = label a i := by
  have hm : (2 * i.val + 3) % 2 = 1 := by omega
  have hd : (2 * i.val + 3) / 2 - 1 = i.val := by omega
  simp [bit, show ¬2*i.val+3<2 by omega, hm, hd]

lemma bit_even (label : A → Fin t → Bool) (a : A) {r : ℕ}
    (hr : 2 ≤ r) (he : r % 2 = 0) : bit label a r = false := by
  simp [bit,show ¬r<2 by omega,he]

lemma bit_last (label : A → Fin t → Bool) (a : A) :
    bit label a (width t - 1) = false := by
  apply bit_even
  · unfold width; omega
  · unfold width; omega

lemma bit_consecutive (label : A → Fin t → Bool) {a : A} {r : ℕ}
    (h₁ : bit label a r = true) (h₂ : bit label a (r+1) = true) : r = 0 := by
  by_contra h
  by_cases he : r % 2 = 0
  · have hr : 2 ≤ r := by omega
    rw [bit_even label a hr he] at h₁
    cases h₁
  · have he : (r+1)%2=0 := by omega
    rw [bit_even label a (by omega) he] at h₂
    cases h₂

lemma encode_get_block (label : A → Fin t → Bool) (x : List A)
    (i : Fin x.length) (r : Fin (width t)) :
    (encode label x)[width t * i.val + r.val]'(by
      rw [encode_length]
      have hm := Nat.mul_le_mul_left (width t) i.isLt
      simp only [Nat.mul_succ] at hm
      have := r.isLt
      omega) = bit label (x.get i) r := by
  induction x with
  | nil => exact Fin.elim0 i
  | cons a x ih =>
    by_cases hi : i.val = 0
    · simp only [encode, List.flatMap_cons]
      rw [List.getElem_append_left (by simp [hi])]
      simp [block,hi,List.get_eq_getElem]
    · let j : Fin x.length := ⟨i.val-1,by simpa only [List.length_cons] using (show i.val-1<x.length by
        have := i.isLt; simp only [List.length_cons] at this; omega)⟩
      have hij : i.val = j.val+1 := by dsimp [j]; omega
      simp only [encode, List.flatMap_cons]
      rw [List.getElem_append_right (by rw [block_length]; rw [hij]; nlinarith)]
      simp only [block_length]
      have he : width t * i.val + r.val - width t = width t * j.val + r.val := by rw [hij,Nat.mul_add,Nat.mul_one]; omega
      simp only [he]
      have hget : (a :: x).get i = x.get j := by
        simp only [List.get_eq_getElem,hij,List.getElem_cons_succ]
      rw [hget]
      exact ih j

lemma padded_get_block (label : A → Fin t → Bool) (x : List A) (pad : ℕ)
    (i : Fin x.length) (r : Fin (width t)) :
    (padded label x pad)[width t * i.val + r.val]'(by
      rw [padded_length]
      have hm := Nat.mul_le_mul_left (width t) i.isLt
      simp only [Nat.mul_succ] at hm
      have := r.isLt
      omega) = bit label (x.get i) r := by
  unfold padded
  rw [List.getElem_append_left (by
    rw [encode_length]
    have hm := Nat.mul_le_mul_left (width t) i.isLt
    simp only [Nat.mul_succ] at hm
    have := r.isLt
    omega),encode_get_block]

lemma padded_get_padding (label : A → Fin t → Bool) (x : List A) (pad n : ℕ)
    (hn : n < (padded label x pad).length) (hp : width t * x.length ≤ n) :
    (padded label x pad)[n] = false := by
  unfold padded at hn ⊢
  rw [List.getElem_append_right (by simpa using hp)]
  simp

lemma padded_delimiter (label : A → Fin t → Bool) (x : List A) (pad n : ℕ)
    (hn : n+1 < (padded label x pad).length)
    (h₁ : (padded label x pad)[n]'(by omega) = true)
    (h₂ : (padded label x pad)[n+1] = true) :
    ∃ i : Fin x.length, n = width t * i.val := by
  have hnp : n < width t * x.length := by
    by_contra h
    rw [padded_get_padding label x pad n (by omega) (by omega)] at h₁
    cases h₁
  let i : Fin x.length := ⟨n / width t, (Nat.div_lt_iff_lt_mul width_pos).mpr (by nlinarith)⟩
  let r : Fin (width t) := ⟨n % width t, Nat.mod_lt _ width_pos⟩
  have hnE : n = width t * i.val + r.val := by
    dsimp [i,r]
    have := Nat.mod_add_div n (width t)
    omega
  have hrLast : r.val ≠ width t - 1 := by
    intro he
    have h := padded_get_block label x pad i r
    simp only [←hnE] at h
    have hb := bit_last label (x.get i)
    simp only [show (r : ℕ) = width t-1 from he,hb] at h
    rw [h] at h₁
    cases h₁
  let r' : Fin (width t) := ⟨r.val+1,by have := r.isLt; omega⟩
  have hb₁ : bit label (x.get i) r = true := by
    have hv := padded_get_block label x pad i r
    simp only [←hnE] at hv
    exact hv.symm.trans h₁
  have hb₂ : bit label (x.get i) (r.val+1) = true := by
    rw [← padded_get_block label x pad i r']
    have he : width t*i.val+r'.val=n+1 := by dsimp [r']; omega
    simpa only [he] using h₂
  have hr0 := bit_consecutive label hb₁ hb₂
  exact ⟨i,by omega⟩

lemma block_injective (label : A → Fin t → Bool) (hi : Function.Injective label) :
    Function.Injective (block label) := by
  intro a b he
  apply hi
  funext i
  have hir : 2*i.val+3<width t := by unfold width; omega
  have hv := congrArg (fun l : List Bool => l[2*i.val+3]?) he
  simp only [block, List.getElem?_ofFn] at hv
  simp only [dite_eq_left hir] at hv
  simpa only [bit_label, Option.some.injEq] using hv

end EditCode

end OAI
