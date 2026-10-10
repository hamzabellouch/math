import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredMaskCells

namespace OAI

/-! # Live families and products while constructing raw leaf records

The explicit-domain entrypoint consumes the three index lists. It keeps
the component families while constructing both Cartesian products and
then the records. The finite-set refinement preserves the generator's complete value and work counter.
-/

namespace LowSpaceSubsetSum.StoredRecordCells

variable {n : ℕ}

def generate (top mixer background : List (Fin n))
    (ht : top.length ≤ n) (hm : mixer.length ≤ n) (hb : background.length ≤ n)
    (k l : ℕ) : (List (LeafRecord n) × ℕ) × ℕ :=
  let t := StoredMaskCells.select top ht k
  let m := StoredMaskCells.select mixer hm l
  let b := StoredMaskCells.all background hb
  let tm := t.1.1 ×ˢ m.1.1
  let out := (tm ×ˢ b.1.1).map fun y => (⟨y.1.1, y.1.2, y.2⟩ : LeafRecord n)
  ((out, t.1.2 + m.1.2 + b.1.2 + 4 * tm.length + 8 * out.length),
    t.2 + m.2 + b.2 + 8 * (n + 2) *
      (t.1.1.length + m.1.1.length + b.1.1.length + tm.length + out.length + 4))

def source (top mixer background : List (Fin n))
    (ht : top.length ≤ n) (hm : mixer.length ≤ n) (hb : background.length ≤ n)
    (k l : ℕ) : List (LeafRecord n) × ℕ :=
  let t := IndexedMask.measuredSelected top ht k
  let m := IndexedMask.measuredSelected mixer hm l
  let b := IndexedMask.measuredAll background hb
  let tm := t.1 ×ˢ m.1
  let out := (tm ×ˢ b.1).map fun y => (⟨y.1.1, y.1.2, y.2⟩ : LeafRecord n)
  (out, t.2 + m.2 + b.2 + 4 * tm.length + 8 * out.length)

theorem generate_value (top mixer background : List (Fin n))
    (ht : top.length ≤ n) (hm : mixer.length ≤ n) (hb : background.length ≤ n)
    (k l : ℕ) :
    (generate top mixer background ht hm hb k l).1 = source top mixer background ht hm hb k l := by
  simp only [generate, source, StoredMaskCells.select_value, StoredMaskCells.all_value]

private theorem factors (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    a ≤ a * b * c ∧ b ≤ a * b * c ∧ c ≤ a * b * c ∧ a * b ≤ a * b * c := by
  have hab : 1 ≤ a * b := by nlinarith
  have habc := Nat.mul_le_mul_left (a * b) hc
  simp only [Nat.mul_one] at habc
  have ha' : a ≤ a*b := by simpa using Nat.mul_le_mul_left a hb
  have hb' : b ≤ a*b := by simpa using Nat.mul_le_mul_right b ha
  constructor
  · exact ha'.trans habc
  constructor
  · exact hb'.trans habc
  constructor
  · simpa using Nat.mul_le_mul_right c hab
  · exact habc

private theorem peak_bound (A a b c t m z : ℕ)
    (hA : A ≤ A ^ 3)
    (hfac : a ≤ a*b*c ∧ b ≤ a*b*c ∧ c ≤ a*b*c ∧ a*b ≤ a*b*c)
    (ht : t ≤ 256 * A ^ 3 * (a + 1))
    (hm : m ≤ 256 * A ^ 3 * (b + 1))
    (hz : z ≤ 32 * A * (c + 1)) :
    t + m + z + 8*A*(a+b+c+a*b+a*b*c+4) ≤ 1024*A^3*(a*b*c+1) := by
  let N := a*b*c
  have ht' := ht.trans (Nat.mul_le_mul_left (256*A^3) (by omega : a+1 ≤ N+1))
  have hm' := hm.trans (Nat.mul_le_mul_left (256*A^3) (by omega : b+1 ≤ N+1))
  have hz' := hz.trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left 32 hA) (by omega : c+1 ≤ N+1))
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hA)
    (show a+b+c+a*b+a*b*c+4 ≤ 5*(N+1) by dsimp only [N]; omega)
  change _ ≤ 1024*A^3*(N+1)
  nlinarith only [ht', hm', hz', hp, Nat.zero_le (A^3*(N+1))]

theorem generate_cells (top mixer background : List (Fin n))
    (ht : top.length ≤ n) (hm : mixer.length ≤ n) (hb : background.length ≤ n)
    (k l : ℕ) (hk : k ≤ top.length) (hl : l ≤ mixer.length) :
    (generate top mixer background ht hm hb k l).2 ≤
      1024 * (n + 2) ^ 3 *
        (top.length.choose k * mixer.length.choose l * 2 ^ background.length + 1) := by
  have hts := StoredMaskCells.select_cells top ht k hk
  have hms := StoredMaskCells.select_cells mixer hm l hl
  have hbs := StoredMaskCells.all_cells background hb
  have ha := Nat.choose_pos hk
  have hb' := Nat.choose_pos hl
  have hc : 1 ≤ 2 ^ background.length := Nat.one_le_two_pow
  have fac := factors _ _ _ ha hb' hc
  have hA : n + 2 ≤ (n + 2)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n+2) (by decide : 1 ≤ 3)
  have hp := peak_bound (n+2) _ _ _ _ _ _ hA fac hts hms hbs
  simpa only [generate, StoredMaskCells.select_value, StoredMaskCells.all_value,
    IndexedMask.measuredSelected_value, IndexedMask.measuredAll_value,
    List.length_product, List.length_map, IndexedMask.selected_length, IndexedMask.all_length]
    using hp

def run (L : RepresentationLeaf (Fin n)) : (List (LeafRecord n) × ℕ) × ℕ :=
  if L.topCount ≤ L.top.card ∧ L.localCount ≤ L.mixer.card then
    let dt := RepresentationLeaf.domainSort L.top
    let dm := RepresentationLeaf.domainSort L.mixer
    let db := RepresentationLeaf.domainSort L.background
    let r := generate dt.1 dm.1 db.1
      (by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ L.top)
      (by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ L.mixer)
      (by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ L.background)
      L.topCount L.localCount
    ((r.1.1, dt.2 + dm.2 + db.2 + r.1.2 + 3*(n+1)), r.2 + 16*(n+1))
  else (([], 3*(n+1)), 16*(n+1))

theorem run_value (L : RepresentationLeaf (Fin n)) :
    (run L).1 = L.measuredStoredRecords := by
  simp only [run, RepresentationLeaf.measuredStoredRecords]
  split
  · simp only [generate_value, source]
    congr 1; omega
  · rfl

theorem run_cells (I : Instance n) (L : RepresentationLeaf (Fin n)) (hn : 10000 ≤ n) :
    (run L).2 ≤ inputScale I ^ 5 * (L.occurrences.card + 1) := by
  have hu : n + 2 ≤ inputScale I := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale I := by omega
  have hpow := Nat.pow_le_pow_left hu 3
  have hp : 2048 * (n+2)^3 ≤ inputScale I ^ 5 := by
    have hlarge : 2048 ≤ inputScale I ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul hlarge hpow
    calc
      _ ≤ inputScale I^2 * inputScale I^3 := hm
      _ = _ := by rw [← pow_add]
  have hcube : n+2 ≤ (n+2)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ n+2) (by decide : 1 ≤ 3)
  have hsmall : 16*(n+1) ≤ 1024*(n+2)^3 := by omega
  have h1 : 1 ≤ L.occurrences.card + 1 := by omega
  have hm0 := Nat.mul_le_mul_left (1024*(n+2)^3) h1
  simp only [Nat.mul_one] at hm0
  have hsmall' := hsmall.trans hm0
  have hfinal := Nat.mul_le_mul_right (L.occurrences.card+1) hp
  simp only [Nat.mul_assoc] at hsmall' hfinal
  unfold run
  split
  · rename_i hf
    have hg := generate_cells (RepresentationLeaf.domainSort L.top).1
      (RepresentationLeaf.domainSort L.mixer).1 (RepresentationLeaf.domainSort L.background).1
      (by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ L.top)
      (by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ L.mixer)
      (by rw [RepresentationLeaf.domainSort_length]; simpa using Finset.card_le_univ L.background)
      L.topCount L.localCount (by simpa using hf.1) (by simpa using hf.2)
    simp only [RepresentationLeaf.domainSort_length, ← RepresentationLeaf.occurrences_card] at hg
    simp only [Nat.mul_assoc] at hg
    dsimp only
    omega
  · dsimp only
    exact hsmall'.trans (by omega)

end LowSpaceSubsetSum.StoredRecordCells

end OAI
