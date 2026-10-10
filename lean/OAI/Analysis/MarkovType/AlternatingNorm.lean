import OAI.Analysis.MarkovType.OrderedNorm
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

namespace C00

def alternating (k : ℕ) : C00 :=
  ∑ j ∈ Finset.range k, (basis (2 * j) - basis (2 * j + 1))

def alternatingArray (k : ℕ) (i : Fin (2 * k)) : ℝ := (-1) ^ i.val

def alternatingEven {k : ℕ} (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

def alternatingOdd {k : ℕ} (j : Fin k) : Fin (2 * k) :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

@[simp] theorem alternating_zero : alternating 0 = 0 := by
  simp [alternating]

@[simp] theorem alternating_one : alternating 1 = basis 0 - basis 1 := by
  simp [alternating]

@[simp] theorem alternatingArray_even {k : ℕ} (j : Fin k) :
    alternatingArray k (alternatingEven j) = 1 := by
  simp [alternatingArray, alternatingEven, pow_mul]

@[simp] theorem alternatingArray_odd {k : ℕ} (j : Fin k) :
    alternatingArray k (alternatingOdd j) = -1 := by
  simp [alternatingArray, alternatingOdd, pow_add, pow_mul]

theorem place_alternatingArray {k : ℕ} (ι : Fin (2 * k) → ℕ) :
    place ι (alternatingArray k) =
      ∑ j : Fin k,
        (basis (ι (alternatingEven j)) - basis (ι (alternatingOdd j))) := by
  classical
  let e : Fin k × Fin 2 ≃ Fin (2 * k) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))
  have he0 (j : Fin k) : e (j, 0) = alternatingEven j := by
    apply Fin.ext
    simp [e, finProdFinEquiv, alternatingEven]
  have he1 (j : Fin k) : e (j, 1) = alternatingOdd j := by
    apply Fin.ext
    simp [e, finProdFinEquiv, alternatingOdd, Nat.add_comm]
  unfold place
  rw [← e.sum_comp (fun i => Finsupp.single (ι i) (alternatingArray k i)),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two, he0, he1]
  simp [basis, sub_eq_add_neg]

theorem alternating_eq_ofArray (k : ℕ) :
    alternating k = ofArray (alternatingArray k) := by
  rw [ofArray, place_alternatingArray]
  simpa only [alternating, alternatingEven, alternatingOdd] using
    (Fin.sum_univ_eq_sum_range
      (fun j => basis (2 * j) - basis (2 * j + 1)) k).symm

theorem alternating_apply (k i : ℕ) :
    alternating k i = if i < 2 * k then (-1 : ℝ) ^ i else 0 := by
  classical
  rw [alternating_eq_ofArray]
  split_ifs with hi
  · simpa [alternatingArray] using
      (ofArray_apply (alternatingArray k) (⟨i, hi⟩ : Fin (2 * k)))
  · simp only [ofArray, place, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.single_eq_of_ne
    have := j.isLt
    omega

theorem alternating_apply_zero {k : ℕ} (hk : 0 < k) :
    alternating k 0 = 1 := by
  rw [alternating_eq_ofArray]
  simpa [alternatingArray] using
    (ofArray_apply (alternatingArray k) (⟨0, by omega⟩ : Fin (2 * k)))

theorem alternating_ne_zero {k : ℕ} (hk : 0 < k) : alternating k ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : C00 => x 0) h
  simp [alternating_apply_zero hk] at h0

def shift (t : ℕ) (x : C00) : C00 :=
  Finsupp.mapDomain.addMonoidHom (fun i => t + i) x

@[simp] theorem shift_zero (t : ℕ) : shift t 0 = 0 := by
  exact map_zero (Finsupp.mapDomain.addMonoidHom (fun i => t + i))

@[simp] theorem shift_basis (t i : ℕ) : shift t (basis i) = basis (t + i) := by
  simp [shift, basis]

theorem shift_apply_add (t : ℕ) (x : C00) (i : ℕ) :
    shift t x (t + i) = x i := by
  change Finsupp.mapDomain (fun j => t + j) x (t + i) = x i
  exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => Nat.add_left_cancel h) x i

theorem shift_apply_add_right (t : ℕ) (x : C00) (i : ℕ) :
    shift t x (i + t) = x i := by
  simpa only [Nat.add_comm] using shift_apply_add t x i

theorem shift_apply_lt (t : ℕ) (x : C00) {i : ℕ} (hi : i < t) :
    shift t x i = 0 := by
  change Finsupp.mapDomain (fun j => t + j) x i = 0
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  change t + j = i at hj
  omega

theorem shift_ofArray {m : ℕ} (t : ℕ) (a : Fin m → ℝ) :
    shift t (ofArray a) = place (fun i => t + i.val) a := by
  unfold shift ofArray place
  rw [map_sum]
  simp only [Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

theorem shift_alternating (t k : ℕ) :
    shift t (alternating k) =
      ∑ j ∈ Finset.range k,
        (basis (t + 2 * j) - basis (t + (2 * j + 1))) := by
  unfold shift alternating
  rw [map_sum]
  simp_rw [map_sub]
  simp only [basis, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

theorem alternating_add (k l : ℕ) :
    alternating (k + l) = alternating k + shift (2 * k) (alternating l) := by
  calc
    alternating (k + l) = alternating k +
        ∑ j ∈ Finset.range l,
          (basis (2 * (k + j)) - basis (2 * (k + j) + 1)) := by
      exact Finset.sum_range_add
        (fun j => basis (2 * j) - basis (2 * j + 1)) k l
    _ = alternating k + shift (2 * k) (alternating l) := by
      rw [shift_alternating]
      simp only [Nat.mul_add, Nat.add_assoc]

def alternatingPlacement {k : ℕ} (lo hi : Fin k → ℕ)
    (i : Fin (2 * k)) : ℕ :=
  if i.val % 2 = 0 then
    lo ⟨i.val / 2, by have := i.isLt; omega⟩
  else
    hi ⟨i.val / 2, by have := i.isLt; omega⟩

@[simp] theorem alternatingPlacement_even {k : ℕ} (lo hi : Fin k → ℕ)
    (j : Fin k) :
    alternatingPlacement lo hi (alternatingEven j) = lo j := by
  have hbound : 2 * j.val / 2 < k := by
    have := j.isLt
    omega
  change (if 2 * j.val % 2 = 0 then
    lo ⟨2 * j.val / 2, hbound⟩ else
    hi ⟨2 * j.val / 2, hbound⟩) = lo j
  calc
    _ = lo ⟨2 * j.val / 2, hbound⟩ := ite_eq_left (by omega)
    _ = lo j := by
      apply congrArg lo
      apply Fin.ext
      change 2 * j.val / 2 = j.val
      omega

@[simp] theorem alternatingPlacement_odd {k : ℕ} (lo hi : Fin k → ℕ)
    (j : Fin k) :
    alternatingPlacement lo hi (alternatingOdd j) = hi j := by
  have hbound : (2 * j.val + 1) / 2 < k := by
    have := j.isLt
    omega
  change (if (2 * j.val + 1) % 2 = 0 then
    lo ⟨(2 * j.val + 1) / 2, hbound⟩ else
    hi ⟨(2 * j.val + 1) / 2, hbound⟩) = hi j
  calc
    _ = hi ⟨(2 * j.val + 1) / 2, hbound⟩ := ite_eq_right (by omega)
    _ = hi j := by
      apply congrArg hi
      apply Fin.ext
      change (2 * j.val + 1) / 2 = j.val
      omega

theorem alternatingPlacement_strictMono {k : ℕ} (lo hi : Fin k → ℕ)
    (hpair : ∀ j, lo j < hi j)
    (hnext : ∀ i j, i < j → hi i < lo j) :
    StrictMono (alternatingPlacement lo hi) := by
  intro a b hab
  have hab' : a.val < b.val := hab
  let a' : Fin k := ⟨a.val / 2, by have := a.isLt; omega⟩
  let b' : Fin k := ⟨b.val / 2, by have := b.isLt; omega⟩
  change (if a.val % 2 = 0 then lo a' else hi a') <
    (if b.val % 2 = 0 then lo b' else hi b')
  by_cases hquot : a.val / 2 < b.val / 2
  · have hn := hnext a' b' hquot
    have hpa := hpair a'
    have hpb := hpair b'
    split_ifs <;> omega
  · have heq : a' = b' := by
      apply Fin.ext
      change a.val / 2 = b.val / 2
      omega
    have ha0 : a.val % 2 = 0 := by omega
    have hb1 : b.val % 2 ≠ 0 := by omega
    rw [ite_eq_left ha0, ite_eq_right hb1, heq]
    exact hpair b'

end C00

namespace OrderedNorm

def alternatingNorm (N : OrderedNorm) (k : ℕ) : ℝ := N (C00.alternating k)

@[simp] theorem alternatingNorm_zero (N : OrderedNorm) :
    N.alternatingNorm 0 = 0 := by
  simp [alternatingNorm]

theorem alternatingNorm_nonneg (N : OrderedNorm) (k : ℕ) :
    0 ≤ N.alternatingNorm k := N.nonneg _

theorem alternatingNorm_pos (N : OrderedNorm) {k : ℕ} (hk : 0 < k) :
    0 < N.alternatingNorm k := by
  apply lt_of_le_of_ne (N.alternatingNorm_nonneg k)
  intro h
  exact C00.alternating_ne_zero hk ((N.eq_zero_iff _).mp h.symm)

theorem placed_alternatingNorm (N : OrderedNorm) {k : ℕ}
    (ι : Fin (2 * k) → ℕ) (hι : StrictMono ι) :
    N (C00.place ι (C00.alternatingArray k)) = N.alternatingNorm k := by
  change N (C00.place ι (C00.alternatingArray k)) = N (C00.alternating k)
  rw [N.spreading ι hι, ← C00.alternating_eq_ofArray]

theorem placed_alternating_pairs_norm (N : OrderedNorm) {k : ℕ}
    (ι : Fin (2 * k) → ℕ) (hι : StrictMono ι) :
    N (∑ j : Fin k,
      (C00.basis (ι (C00.alternatingEven j)) -
        C00.basis (ι (C00.alternatingOdd j)))) = N.alternatingNorm k := by
  rw [← C00.place_alternatingArray]
  exact N.placed_alternatingNorm ι hι

theorem alternatingPairs_norm (N : OrderedNorm) {k : ℕ}
    (lo hi : Fin k → ℕ) (hpair : ∀ j, lo j < hi j)
    (hnext : ∀ i j, i < j → hi i < lo j) :
    N (∑ j : Fin k, (C00.basis (lo j) - C00.basis (hi j))) =
      N.alternatingNorm k := by
  simpa only [C00.alternatingPlacement_even, C00.alternatingPlacement_odd] using
    N.placed_alternating_pairs_norm (C00.alternatingPlacement lo hi)
      (C00.alternatingPlacement_strictMono lo hi hpair hnext)

theorem shift_alternatingNorm (N : OrderedNorm) (t k : ℕ) :
    N (C00.shift t (C00.alternating k)) = N.alternatingNorm k := by
  rw [C00.alternating_eq_ofArray, C00.shift_ofArray]
  exact N.placed_alternatingNorm (fun i => t + i.val) (by
    intro i j hij
    exact Nat.add_lt_add_left (show i.val < j.val from hij) t)

theorem alternatingNorm_subadditive (N : OrderedNorm) (k l : ℕ) :
    N.alternatingNorm (k + l) ≤ N.alternatingNorm k + N.alternatingNorm l := by
  change N (C00.alternating (k + l)) ≤ _
  rw [C00.alternating_add]
  calc
    N (C00.alternating k + C00.shift (2 * k) (C00.alternating l)) ≤
        N (C00.alternating k) + N (C00.shift (2 * k) (C00.alternating l)) :=
      N.add_le _ _
    _ = N.alternatingNorm k + N.alternatingNorm l := by
      simpa only [alternatingNorm] using
        congrArg (fun z => N (C00.alternating k) + z) (N.shift_alternatingNorm (2 * k) l)

theorem alternatingNorm_twice_le (N : OrderedNorm) (k : ℕ) :
    N.alternatingNorm (2 * k) ≤ 2 * N.alternatingNorm k := by
  simpa only [two_mul] using N.alternatingNorm_subadditive k k

theorem basis_sub_basis_norm (N : OrderedNorm) {i j : ℕ} (hij : i < j) :
    N (C00.basis i - C00.basis j) = N.alternatingNorm 1 := by
  let ι : Fin (2 * 1) → ℕ := fun q => if q.val = 0 then i else j
  have hι : StrictMono ι := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have hab' : a.val < b.val := hab
    have ha0 : a.val = 0 := by omega
    have hb1 : b.val = 1 := by omega
    change (if a.val = 0 then i else j) < (if b.val = 0 then i else j)
    rw [ite_eq_left ha0, ite_eq_right (by omega)]
    exact hij
  simpa [Fin.sum_univ_one, C00.alternatingEven, C00.alternatingOdd, ι] using
    N.placed_alternating_pairs_norm ι hι

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
