import OAI.MathematicalPhysics.Heisenberg.TensorLift

namespace OAI


noncomputable section
open scoped Classical
open Matrix
namespace Heisenberg.Exposure

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

lemma det_two_rows (A : Matrix n n R) {i j : n} (hij : i ≠ j)
    (v : n → R) (u : R) :
    ((A.updateRow i (A i + u • v)).updateRow j (A j - u • v)).det =
      A.det + u * ((A.updateRow i v).det - (A.updateRow j v).det) := by
  have h₁ : (A.updateRow i (A i + u • v)).updateRow j (A j) =
      A.updateRow i (A i + u • v) := by
    rw [← Matrix.updateRow_ne (M := A) (b := A i + u • v) hij.symm]
    exact Matrix.updateRow_eq_self _ _
  have h₂ : ((A.updateRow i (A i + u • v)).updateRow j v).det =
      (A.updateRow j v).det := by
    rw [Matrix.updateRow_comm A hij, Matrix.det_updateRow_add,
      Matrix.det_updateRow_smul]
    have hrow : (A.updateRow j v).updateRow i (A i) = A.updateRow j v := by
      rw [← Matrix.updateRow_ne (M := A) (b := v) hij]
      exact Matrix.updateRow_eq_self _ _
    rw [hrow]
    have hz : ((A.updateRow j v).updateRow i v).det = 0 := by
      apply Matrix.det_zero_of_row_eq hij
      simp [Matrix.updateRow_self, Matrix.updateRow_ne hij.symm]
    rw [hz, mul_zero, add_zero]
  rw [sub_eq_add_neg, Matrix.det_updateRow_add, ← neg_smul,
    Matrix.det_updateRow_smul, h₁, h₂, Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  ring

def swapMix (i j : n) (u : R) : Matrix n n R :=
  (1 - u) • (1 : Matrix n n R) + u • (Equiv.swap i j).permMatrix R

lemma one_sub_swapMix_mul (D : Matrix n n R) {i j : n} (hij : i ≠ j)
    (u : R) :
    1 - swapMix i j u * D =
      (((1 - D).updateRow i ((1 - D) i + u • (D i - D j))).updateRow j
        ((1 - D) j - u • (D i - D j))) := by
  unfold swapMix
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext k l
  by_cases hi : k = i
  · subst k
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.submatrix_apply, Equiv.swap_apply_left,
      id_eq, Matrix.updateRow_apply, hij, ite_false, ite_true,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  · by_cases hj : k = j
    · subst k
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.submatrix_apply, Equiv.swap_apply_right,
        id_eq, Matrix.updateRow_apply, ite_true,
        Pi.sub_apply, Pi.smul_apply]
      ring
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.submatrix_apply,
        Equiv.swap_apply_of_ne_of_ne hi hj, id_eq, Matrix.updateRow_apply,
        hi, hj, ite_false]
      ring

theorem det_swapMix (D : Matrix n n R) (i j : n) (u : R) :
    (1 - D * swapMix i j u).det =
      (1 - u) * (1 - D).det + u * (1 - D * (Equiv.swap i j).permMatrix R).det := by
  by_cases hij : i = j
  · subst j
    simp only [Equiv.swap_self, Matrix.permMatrix_refl]
    have he : swapMix i i u = (1 : Matrix n n R) := by
      simp [swapMix, ← add_smul]
    rw [he, Matrix.mul_one]
    ring
  rw [Matrix.det_one_sub_mul_comm, one_sub_swapMix_mul D hij, det_two_rows _ hij]
  have h₁ := det_two_rows (1 - D) hij (D i - D j) (1 : R)
  rw [← one_sub_swapMix_mul D hij] at h₁
  simp only [swapMix, sub_self, zero_smul, one_smul, zero_add, one_mul] at h₁
  rw [Matrix.det_one_sub_mul_comm D ((Equiv.swap i j).permMatrix R), h₁]
  ring

def DeterminantLaw {Ω : Type*} [Fintype Ω]
    (p : Ω → R) (X : Ω → Matrix n n R) : Prop :=
  ∀ D : Matrix n n R,
    ∑ ω, p ω * (1 - D * X ω).det =
      (1 - D * ∑ ω, p ω • X ω).det

theorem determinantLaw_bernoulli (i j : n) (u : R) :
    DeterminantLaw (fun b : Bool => if b then u else 1 - u)
      (fun b => if b then (Equiv.swap i j).permMatrix R else 1) := by
  intro D
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true,
    ite_false, Matrix.mul_one]
  rw [add_comm (u • _), ← swapMix, det_swapMix]
  ring

lemma determinantLaw_deterministic (X : Matrix n n R) :
    DeterminantLaw (fun _ : Unit => (1 : R)) (fun _ => X) := by
  intro D
  simp

theorem DeterminantLaw.independent_mul {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    {p : Ω → R} {q : Ψ → R} {X : Ω → Matrix n n R} {Y : Ψ → Matrix n n R}
    (hX : DeterminantLaw p X) (hY : DeterminantLaw q Y) :
    DeterminantLaw (fun z : Ω × Ψ => p z.1 * q z.2)
      (fun z => X z.1 * Y z.2) := by
  intro D
  let MX := ∑ ω, p ω • X ω
  let MY := ∑ ψ, q ψ • Y ψ
  have hmean : (∑ z : Ω × Ψ, (p z.1 * q z.2) • (X z.1 * Y z.2)) = MX * MY := by
    dsimp [MX, MY]
    rw [Fintype.sum_prod_type, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hmean, Fintype.sum_prod_type]
  calc
    (∑ ω, ∑ ψ, (p ω * q ψ) * (1 - D * (X ω * Y ψ)).det) =
        ∑ ω, p ω * (1 - D * X ω * MY).det := by
      apply Finset.sum_congr rfl
      intro ω _
      simp_rw [mul_assoc (p ω), ← Matrix.mul_assoc D]
      rw [← Finset.mul_sum, hY]
    _ = ∑ ω, p ω * (1 - MY * D * X ω).det := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Matrix.det_one_sub_mul_comm (D * X ω) MY, Matrix.mul_assoc]
    _ = (1 - MY * D * MX).det := hX (MY * D)
    _ = (1 - D * (MX * MY)).det := by
      rw [Matrix.mul_assoc MY, Matrix.det_one_sub_mul_comm MY (D * MX),
        Matrix.mul_assoc]

end Heisenberg.Exposure

open scoped Classical
open Matrix
namespace Heisenberg.Exposure

variable {Q : Type*} [Fintype Q] [DecidableEq Q]
variable (R : Type*) [Field R]

def partialMatrix (f : Q → Option Q) : Matrix Q Q R :=
  fun i j => if f i = some j then 1 else 0

def walk (f : Q → Option Q) : ℕ → Q → Option Q
  | 0, i => some i
  | n + 1, i => (f i).bind (walk f n)

omit [Fintype Q] [DecidableEq Q] in
lemma walk_add (f : Q → Option Q) (n m : ℕ) (i : Q) :
    walk f (n + m) i = (walk f n i).bind (walk f m) := by
  induction n generalizing i with
  | zero => simp [walk]
  | succ n ih =>
    simp only [Nat.succ_add, walk]
    cases h : f i with
    | none => simp
    | some j => simpa using ih j

omit [Fintype Q] [DecidableEq Q] in
lemma walk_eq_none_of_le (f : Q → Option Q) {n m : ℕ} (hnm : n ≤ m)
    {i : Q} (hi : walk f n i = none) : walk f m i = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [walk_add, hi]
  rfl

lemma pow_partialMatrix (f : Q → Option Q) (n : ℕ) (i j : Q) :
    (partialMatrix R f ^ n) i j = if walk f n i = some j then 1 else 0 := by
  induction n generalizing i with
  | zero => simp [walk, Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    cases h : f i with
    | none => simp [partialMatrix, h, walk]
    | some k =>
      simp only [partialMatrix, h, Option.some.injEq, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simpa [walk, h] using ih k

def Escapes (f : Q → Option Q) (i : Q) : Prop := ∃ n, walk f n i = none

omit [Fintype Q] [DecidableEq Q] in
lemma escapes_of_none {f : Q → Option Q} {i : Q} (hi : f i = none) : Escapes f i :=
  ⟨1, by simp [walk, hi]⟩

omit [Fintype Q] [DecidableEq Q] in
lemma escapes_iff_of_some {f : Q → Option Q} {i j : Q} (h : f i = some j) :
    Escapes f i ↔ Escapes f j := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [walk] at hn
    | succ n => exact ⟨n, by simpa [walk, h] using hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by simpa [walk, h] using hn⟩

lemma nilpotent_partialMatrix (f : Q → Option Q) (h : ∀ i, Escapes f i) :
    IsNilpotent (partialMatrix R f) := by
  choose n hn using h
  refine ⟨∑ i, n i, ?_⟩
  ext i j
  rw [pow_partialMatrix]
  have hi : walk f (∑ i, n i) i = none :=
    walk_eq_none_of_le f (Finset.single_le_sum (fun k _ => Nat.zero_le (n k))
      (Finset.mem_univ i)) (hn i)
  simp [hi]

lemma det_one_sub_of_nilpotent {A : Matrix Q Q R} (h : IsNilpotent A) :
    (1 - A).det = 1 := by
  have hc : A.charpoly = Polynomial.X ^ Fintype.card Q :=
    sub_eq_zero.mp <| isNilpotent_iff_eq_zero.mp <|
      Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have he := congrArg (Polynomial.eval (1 : R)) hc
  simpa [Matrix.eval_charpoly] using he

lemma det_one_sub_partialMatrix_of_not_all (f : Q → Option Q)
    (h : ¬ ∀ i, Escapes f i) : (1 - partialMatrix R f).det = 0 := by
  let v : Q → R := fun i => if Escapes f i then 0 else 1
  have hv : partialMatrix R f *ᵥ v = v := by
    ext i
    cases hi : f i with
    | none => simp [Matrix.mulVec, dotProduct, partialMatrix, hi, v, escapes_of_none hi]
    | some j =>
      simp only [Matrix.mulVec, dotProduct, partialMatrix, hi, Option.some.injEq,
        ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp [v, escapes_iff_of_some hi]
  have hz : (1 - partialMatrix R f) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hv, sub_self]
  by_contra hne
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hne hz
  push Not at h
  obtain ⟨i, hi⟩ := h
  have := congrFun hv0 i
  simp [v, hi] at this

theorem det_one_sub_partialMatrix (f : Q → Option Q) :
    (1 - partialMatrix R f).det = if ∀ i, Escapes f i then 1 else 0 := by
  split_ifs with h
  · exact det_one_sub_of_nilpotent R (nilpotent_partialMatrix R f h)
  · exact det_one_sub_partialMatrix_of_not_all R f h

end Heisenberg.Exposure
end

end OAI
