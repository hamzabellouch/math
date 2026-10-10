import OAI.MathematicalPhysics.Heisenberg.FirstReturns

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.Exposure

section
variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

lemma conditional_hitWeight_sum (μ : Ω → R) (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) :
    (∑ ω, if AllHit (π ω) then μ ω / hitWeight μ π else 0) = 1 := by
  have ht := conditional_resolvent_determinant μ π h hg (0 : Matrix J J R)
  simpa only [Matrix.zero_mul, sub_zero, Matrix.det_one, mul_one] using ht

theorem conditional_resolvent_first_moment (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) :
    (∑ ω, if AllHit (π ω) then
      (μ ω / hitWeight μ π) • hittingResolvent R (columnPerm R (π ω)) else 0) =
      hittingResolvent R (∑ ω, μ ω • columnPerm R (π ω)) := by
  ext i j
  have ht := conditional_resolvent_determinant μ π h hg (Matrix.single j i (1 : R))
  simp only [det_one_sub_single_mul] at ht
  have he : (∑ ω, if AllHit (π ω) then (μ ω / hitWeight μ π) *
      (1 - hittingResolvent R (columnPerm R (π ω)) i j) else 0) =
      (∑ ω, if AllHit (π ω) then μ ω / hitWeight μ π else 0) -
      (∑ ω, if AllHit (π ω) then (μ ω / hitWeight μ π) *
        hittingResolvent R (columnPerm R (π ω)) i j else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> ring
  rw [he, conditional_hitWeight_sum μ π h hg] at ht
  have hh := sub_right_injective ht
  simp only [Matrix.sum_apply]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> rfl

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q]

lemma reachesPin (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) :
    ∃ n : ℕ, ∃ j : J, (π ^ n) x = Sum.inl j := by
  obtain ⟨j, hj⟩ := h x
  obtain ⟨n, hn⟩ := hj.exists_nat_pow_eq
  exact ⟨n, j, hn⟩

def firstPinTime (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) : ℕ :=
  Nat.find (reachesPin π h x)

def firstPin (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) : J :=
  Classical.choose (Nat.find_spec (reachesPin π h x))

lemma firstPin_spec (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q) :
    (π ^ firstPinTime π h x) x = Sum.inl (firstPin π h x) :=
  Classical.choose_spec (Nat.find_spec (reachesPin π h x))

lemma firstPinTime_min (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (x : J ⊕ Q)
    {n : ℕ} {j : J} (hj : (π ^ n) x = Sum.inl j) : firstPinTime π h x ≤ n :=
  Nat.find_min' (reachesPin π h x) ⟨j, hj⟩

@[simp] lemma firstPinTime_inl (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) :
    firstPinTime π h (Sum.inl j) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact firstPinTime_min π h _ (by simp : (π ^ 0) (Sum.inl j) = Sum.inl j)

@[simp] lemma firstPin_inl (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) :
    firstPin π h (Sum.inl j) = j := by
  have hs := firstPin_spec π h (Sum.inl j)
  simpa using hs.symm

lemma firstPinTime_inr_pos (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (q : Q) :
    0 < firstPinTime π h (Sum.inr q) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hs := firstPin_spec π h (Sum.inr q)
  simp [hz] at hs

lemma firstPinTime_step (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (q : Q) :
    firstPinTime π h (Sum.inr q) = firstPinTime π h (π (Sum.inr q)) + 1 := by
  apply Nat.le_antisymm
  · apply firstPinTime_min π h _ (j := firstPin π h (π (Sum.inr q)))
    rw [pow_succ, Equiv.Perm.mul_apply]
    exact firstPin_spec π h _
  · have hp := firstPinTime_inr_pos π h q
    have he : (π ^ (firstPinTime π h (Sum.inr q) - 1)) (π (Sum.inr q)) =
        Sum.inl (firstPin π h (Sum.inr q)) := by
      rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hp]
      exact firstPin_spec π h _
    have hm := firstPinTime_min π h _ he
    omega

lemma firstPin_step (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (q : Q) :
    firstPin π h (Sum.inr q) = firstPin π h (π (Sum.inr q)) := by
  have hs := firstPin_spec π h (Sum.inr q)
  rw [firstPinTime_step, pow_succ, Equiv.Perm.mul_apply] at hs
  exact Sum.inl.inj (hs.symm.trans (firstPin_spec π h _))

def nextPin (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) : J :=
  firstPin π h (π (Sum.inl j))

lemma nextPin_spec (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J) :
    (π ^ (firstPinTime π h (π (Sum.inl j)) + 1)) (Sum.inl j) =
      Sum.inl (nextPin π h j) := by
  rw [pow_succ, Equiv.Perm.mul_apply]
  exact firstPin_spec π h _

lemma nextPin_is_first (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) (j : J)
    {n : ℕ} (hn : 0 < n) {k : J} (hk : (π ^ n) (Sum.inl j) = Sum.inl k) :
    firstPinTime π h (π (Sum.inl j)) + 1 ≤ n := by
  have he : (π ^ (n - 1)) (π (Sum.inl j)) = Sum.inl k := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hn]
    exact hk
  have hm := firstPinTime_min π h _ he
  omega

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

def firstPinMatrix (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) : Matrix J (J ⊕ Q) R :=
  fun i x => if firstPin π h x = i then 1 else 0

def nextPinMatrix (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) : Matrix J J R :=
  fun i j => if nextPin π h j = i then 1 else 0

omit [DecidableEq Q] in
lemma firstPinMatrix_boundary (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    (firstPinMatrix R π h).toCols₁ = 1 := by
  ext i j
  simp [firstPinMatrix, Matrix.one_apply, eq_comm]

lemma firstPinMatrix_step (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    firstPinMatrix R π h * columnPerm R π =
      Matrix.fromCols (nextPinMatrix R π h) (firstPinMatrix R π h).toCols₂ := by
  ext i x
  change ((firstPinMatrix R π h) i ᵥ* columnPerm R π) x = _
  rw [columnPerm, Matrix.transpose_permMatrix, Matrix.vecMul_permMatrix]
  cases x with
  | inl j => rfl
  | inr q =>
    change (if firstPin π h (π (Sum.inr q)) = i then (1 : R) else 0) =
      (if firstPin π h (Sum.inr q) = i then (1 : R) else 0)
    rw [firstPin_step]

theorem nextPinMatrix_eq_resolvent (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    nextPinMatrix R π h = hittingResolvent R (columnPerm R π) := by
  let K := columnPerm R π
  let V := (firstPinMatrix R π h).toCols₂
  have hs := firstPinMatrix_step R π h
  have hf : firstPinMatrix R π h = Matrix.fromCols 1 V := by
    rw [← Matrix.fromCols_toCols (firstPinMatrix R π h), firstPinMatrix_boundary]
  rw [hf] at hs
  change Matrix.fromCols 1 V * K = Matrix.fromCols (nextPinMatrix R π h) V at hs
  conv_lhs at hs => arg 2; rw [← Matrix.fromBlocks_toBlocks K]
  rw [Matrix.fromCols_mul_fromBlocks, Matrix.one_mul, Matrix.one_mul] at hs
  have hJ := congrArg Matrix.toCols₁ hs
  have hQ := congrArg Matrix.toCols₂ hs
  simp only [Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols] at hJ hQ
  have hV : V * (1 - K.toBlocks₂₂) = K.toBlocks₁₂ := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    exact sub_eq_iff_eq_add.mpr hQ.symm
  have hd : IsUnit (1 - K.toBlocks₂₂).det := by
    have he : (1 - K.toBlocks₂₂).det = 1 := by
      simpa only [K, Matrix.toBlocks₂₂, Matrix.submatrix, ite_eq_left h] using
        det_one_sub_columnPerm_QQ R π
    rw [he]
    exact isUnit_one
  have hv : V = K.toBlocks₁₂ * (1 - K.toBlocks₂₂)⁻¹ := by
    rw [← hV, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  rw [← hJ, hv]
  rfl

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q]

lemma nextPin_injective (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) :
    Function.Injective (nextPin π h) := by
  have haux (j k : J)
      (hn : firstPinTime π h (π (Sum.inl j)) + 1 ≤
        firstPinTime π h (π (Sum.inl k)) + 1)
      (he : nextPin π h j = nextPin π h k) : j = k := by
    let n := firstPinTime π h (π (Sum.inl j)) + 1
    let m := firstPinTime π h (π (Sum.inl k)) + 1
    have hnm : n ≤ m := hn
    have hn0 : 0 < n := Nat.succ_pos _
    have hm0 : 0 < m := Nat.succ_pos _
    have hb : (π ^ (m - n)) (Sum.inl k) = Sum.inl j := by
      apply (π ^ n).injective
      calc
        (π ^ n) ((π ^ (m - n)) (Sum.inl k)) = (π ^ m) (Sum.inl k) := by
          rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hnm]
        _ = Sum.inl (nextPin π h k) := nextPin_spec π h k
        _ = Sum.inl (nextPin π h j) := congrArg Sum.inl he.symm
        _ = (π ^ n) (Sum.inl j) := (nextPin_spec π h j).symm
    have hz : m - n = 0 := by
      by_contra hne
      have ht := nextPin_is_first π h k (Nat.pos_of_ne_zero hne) hb
      change m ≤ m - n at ht
      omega
    simpa only [hz, pow_zero, Equiv.Perm.one_apply, Sum.inl.injEq] using hb.symm
  intro j k he
  rcases le_total (firstPinTime π h (π (Sum.inl j)) + 1)
    (firstPinTime π h (π (Sum.inl k)) + 1) with hle | hle
  · exact haux j k hle he
  · exact (haux k j hle he.symm).symm

def nextPinEquiv (π : Equiv.Perm (J ⊕ Q)) (h : AllHit π) : Equiv.Perm J :=
  Equiv.ofBijective (nextPin π h)
    ⟨nextPin_injective π h, Finite.surjective_of_injective (nextPin_injective π h)⟩

end

variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

theorem conditional_nextPin_first_moment (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) :
    (∑ ω, if hw : AllHit (π ω) then
      (μ ω / hitWeight μ π) • nextPinMatrix R (π ω) hw else 0) =
      hittingResolvent R (∑ ω, μ ω • columnPerm R (π ω)) := by
  rw [← conditional_resolvent_first_moment μ π h hg]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hw : AllHit (π ω)
  · simp only [dite_eq_left hw, ite_eq_left hw, nextPinMatrix_eq_resolvent]
  · simp only [dite_eq_right hw, ite_eq_right hw]

end Heisenberg.Exposure
end

end OAI
