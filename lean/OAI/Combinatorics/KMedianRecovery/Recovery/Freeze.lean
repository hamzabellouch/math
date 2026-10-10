import Mathlib

namespace OAI

namespace MetricKMedianRecovery.BirdInteger
open Matrix Function
open scoped BigOperators

section Bridge
variable {R : Type*} [CommRing R] {n : ℕ}
lemma sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

lemma sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := calc
  _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k ∈ Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

lemma iterate_get_eq_spec (A : Array R) (hA : A.size = n*n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail,ih,Matrix.of_apply,BirdDet.get_eq]

lemma bird_eq_spec (A : Array R) (hA : A.size=n*n) :
    BirdDet.birdDet n A=BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,←iterate_get_eq_spec A hA k]

lemma spec_eq_det (A : Matrix (Fin n) (Fin n) R) : BirdDet.Spec.birdDet A=A.det := by
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  have har : ar.size=n*n := Array.size_ofFn
  have he : Matrix.ofArray ar har=A := Matrix.ofArray_ofFn A
  rw [←he,←bird_eq_spec ar har,←BirdDet.det_eq_birdDet ar har]
end Bridge

def freeze {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  Matrix.ofArray ar Array.size_ofFn

@[simp] lemma freeze_eq {R : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : freeze A=A :=
  Matrix.ofArray_ofFn A

def iterate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : ℕ → Matrix (Fin n) (Fin n) ℤ
  | 0 => freeze A
  | t+1 => freeze (BirdDet.Spec.stepEntry A (iterate A t))

lemma iterate_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    iterate A t=(BirdDet.Spec.stepEntry A)^[t] A := by
  induction t with
  | zero => simp [iterate]
  | succ t ih => simp only [iterate,freeze_eq,ih,iterate_succ_apply']

def determinant : {n : ℕ} → Matrix (Fin n) (Fin n) ℤ → ℤ
  | 0,_ => 1
  | k+1,A => (-1)^k * iterate A k 0 0

lemma determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : determinant A=A.det := by
  rw [←spec_eq_det]
  cases n with
  | zero => rfl
  | succ k => simp only [determinant,BirdDet.Spec.birdDetSpec_succ,iterate_eq]

lemma sum_natAbs_bound {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℤ) (B : ℕ)
    (hf : ∀ i∈s,(f i).natAbs≤B) : (∑ i∈s,f i).natAbs≤n*B := by
  calc
    _ ≤ ∑ i∈s,(f i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i∈s,B := Finset.sum_le_sum hf
    _ = s.card*B := by simp
    _ ≤ n*B := Nat.mul_le_mul_right B (by simpa using s.card_le_univ)

lemma step_height {n a b : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j,(A i j).natAbs≤2^a) (hF : ∀ i j,(F i j).natAbs≤2^b) (i j : Fin n) :
    (BirdDet.Spec.stepEntry A F i j).natAbs≤2^(a+b+n+1) := by
  have hd := sum_natAbs_bound (Finset.Ioi i) (fun k => F k k) (2^b) (fun k _ => hF k k)
  have hs := sum_natAbs_bound (Finset.Ioi i) (fun k => F i k*A k j) (2^b*2^a)
    (fun k _ => by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hF i k) (hA k j))
  calc
    _ ≤ (∑ k∈Finset.Ioi i,F k k).natAbs*(A i j).natAbs+
        (∑ k∈Finset.Ioi i,F i k*A k j).natAbs := by
      simpa only [BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Int.natAbs_mul,Int.natAbs_neg] using
        Int.natAbs_add_le (-(∑ k∈Finset.Ioi i,F k k)*A i j) (∑ k∈Finset.Ioi i,F i k*A k j)
    _ ≤ (n*2^b)*2^a+n*(2^b*2^a) := Nat.add_le_add (Nat.mul_le_mul hd (hA i j)) hs
    _ ≤ (2^n*2^b)*2^a+2^n*(2^b*2^a) := by
      gcongr <;> exact Nat.le_of_lt Nat.lt_two_pow_self
    _ = _ := by simp only [pow_add,pow_one]; ring

theorem iterate_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j,(A i j).natAbs≤2^a) (t : ℕ) (i j : Fin n) :
    (iterate A t i j).natAbs≤2^((t+1)*a+t*(n+1)) := by
  induction t generalizing i j with
  | zero => simpa [iterate] using hA i j
  | succ t ih =>
    simp only [iterate,freeze_eq]
    convert step_height A (iterate A t) hA (fun i j => ih i j) i j using 1
    congr 1
    ring

theorem determinant_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j,(A i j).natAbs≤2^a) :
    (determinant A).natAbs≤2^((n+1)*a+n*(n+1)) := by
  cases n with
  | zero => simpa [determinant] using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^a)
  | succ n =>
    have hi := iterate_height A hA n 0 0
    simp only [determinant,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,
      one_pow,one_mul]
    exact hi.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

end MetricKMedianRecovery.BirdInteger

end OAI
