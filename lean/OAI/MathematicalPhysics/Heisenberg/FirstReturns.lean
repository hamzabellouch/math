import OAI.MathematicalPhysics.Heisenberg.DeterminantExposure

namespace OAI

noncomputable section

open scoped Classical
open Matrix
namespace Heisenberg.Exposure

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

def restrictPerm (π : Equiv.Perm (J ⊕ Q)) (q : Q) : Option Q :=
  match π (Sum.inr q) with
  | Sum.inl _ => none
  | Sum.inr r => some r

def AllHit (π : Equiv.Perm (J ⊕ Q)) : Prop :=
  ∀ x, ∃ j, π.SameCycle x (Sum.inl j)

omit [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q] in
lemma cycle_hit_of_walk_none (π : Equiv.Perm (J ⊕ Q)) (n : ℕ) (q : Q)
    (h : walk (restrictPerm π) n q = none) :
    ∃ j, π.SameCycle (Sum.inr q) (Sum.inl j) := by
  induction n generalizing q with
  | zero => simp [walk] at h
  | succ n ih =>
    cases he : π (Sum.inr q) with
    | inl j =>
      refine ⟨j, ?_⟩
      rw [← he]
      exact Equiv.Perm.SameCycle.rfl.apply_right
    | inr r =>
      have hr : walk (restrictPerm π) n r = none := by simpa [walk, restrictPerm, he] using h
      obtain ⟨j, hj⟩ := ih r hr
      refine ⟨j, ?_⟩
      rw [← he] at hj
      exact hj.of_apply_left

omit [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q] in
lemma escapes_of_pow_hit (π : Equiv.Perm (J ⊕ Q)) (n : ℕ) (q : Q) (j : J)
    (h : (π ^ n) (Sum.inr q) = Sum.inl j) : Escapes (restrictPerm π) q := by
  induction n generalizing q with
  | zero => simp at h
  | succ n ih =>
    cases he : π (Sum.inr q) with
    | inl k => exact escapes_of_none (by simp [restrictPerm, he])
    | inr r =>
      have hr : restrictPerm π q = some r := by simp [restrictPerm, he]
      apply (escapes_iff_of_some hr).mpr
      apply ih r
      simpa [pow_succ, Equiv.Perm.mul_apply, he] using h

omit [DecidableEq J] [DecidableEq Q] in
lemma escapes_restrictPerm_iff (π : Equiv.Perm (J ⊕ Q)) (q : Q) :
    Escapes (restrictPerm π) q ↔ ∃ j, π.SameCycle (Sum.inr q) (Sum.inl j) := by
  constructor
  · rintro ⟨n, hn⟩
    exact cycle_hit_of_walk_none π n q hn
  · rintro ⟨j, hj⟩
    obtain ⟨n, hn⟩ := hj.exists_nat_pow_eq
    exact escapes_of_pow_hit π n q j hn

omit [DecidableEq J] [DecidableEq Q] in
lemma allHit_iff_escapes (π : Equiv.Perm (J ⊕ Q)) :
    AllHit π ↔ ∀ q, Escapes (restrictPerm π) q := by
  constructor
  · intro h q
    exact (escapes_restrictPerm_iff π q).mpr (h (Sum.inr q))
  · intro h x
    cases x with
    | inl j => exact ⟨j, Equiv.Perm.SameCycle.rfl⟩
    | inr q => exact (escapes_restrictPerm_iff π q).mp (h q)

def columnPerm (π : Equiv.Perm (J ⊕ Q)) : Matrix (J ⊕ Q) (J ⊕ Q) R :=
  (π.permMatrix R).transpose

omit [Fintype J] [Fintype Q] in
lemma columnPerm_QQ (π : Equiv.Perm (J ⊕ Q)) :
    (columnPerm R π).submatrix Sum.inr Sum.inr = (partialMatrix R (restrictPerm π)).transpose := by
  ext i j
  simp only [columnPerm, Matrix.submatrix_apply, Matrix.transpose_apply,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    partialMatrix]
  have heq : (Sum.inr i ∈ some (π (Sum.inr j))) ↔ restrictPerm π j = some i := by
    simp only [Option.mem_some_iff]
    unfold restrictPerm
    cases π (Sum.inr j) <;> simp [eq_comm]
  simp only [heq]

theorem det_one_sub_columnPerm_QQ (π : Equiv.Perm (J ⊕ Q)) :
    (1 - (columnPerm R π).submatrix Sum.inr Sum.inr).det = if AllHit π then 1 else 0 := by
  rw [columnPerm_QQ, ← Matrix.transpose_one, ← Matrix.transpose_sub, Matrix.det_transpose,
    det_one_sub_partialMatrix]
  simp only [← allHit_iff_escapes]

def pinTestMatrix (W : Matrix J J R) : Matrix (J ⊕ Q) (J ⊕ Q) R :=
  Matrix.fromBlocks W 0 0 1

theorem det_pinTest_of_not_allHit (π : Equiv.Perm (J ⊕ Q)) (W : Matrix J J R)
    (h : ¬ AllHit π) : (1 - pinTestMatrix R (Q := Q) W * columnPerm R π).det = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, ∀ j, ¬ π.SameCycle x (Sum.inl j) := by
    simpa only [AllHit, not_forall, not_exists] using h
  let v : (J ⊕ Q) → R := fun y => if π.SameCycle x y then 1 else 0
  have hv : columnPerm R π *ᵥ v = v := by
    rw [columnPerm, Matrix.transpose_permMatrix, Matrix.permMatrix_mulVec]
    ext y
    simp [v]
  have hvJ : v ∘ Sum.inl = 0 := by
    ext j
    simp [v, hx j]
  have hd : pinTestMatrix R (Q := Q) W *ᵥ v = v := by
    rw [pinTestMatrix, Matrix.fromBlocks_mulVec, hvJ]
    simp only [Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero, zero_add, Matrix.one_mulVec]
    ext y
    cases y with
    | inl j => simpa [Function.comp_def] using (congrFun hvJ j).symm
    | inr q => rfl
  have hz : (1 - pinTestMatrix R (Q := Q) W * columnPerm R π) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, hd, sub_self]
  by_contra hne
  have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hne hz
  have := congrFun hv0 x
  simp [v, Equiv.Perm.SameCycle.rfl] at this

end

section
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
variable (R : Type*) [Field R]

def hittingResolvent (K : Matrix (J ⊕ Q) (J ⊕ Q) R) : Matrix J J R :=
  K.toBlocks₁₁ + K.toBlocks₁₂ * (1 - K.toBlocks₂₂)⁻¹ * K.toBlocks₂₁

lemma pinTest_block_form (K : Matrix (J ⊕ Q) (J ⊕ Q) R) (W : Matrix J J R) :
    1 - pinTestMatrix R (Q := Q) W * K =
      Matrix.fromBlocks (1 - W * K.toBlocks₁₁) (-(W * K.toBlocks₁₂))
        (-K.toBlocks₂₁) (1 - K.toBlocks₂₂) := by
  have hk : pinTestMatrix R (Q := Q) W * K =
      Matrix.fromBlocks (W * K.toBlocks₁₁) (W * K.toBlocks₁₂)
        K.toBlocks₂₁ K.toBlocks₂₂ := by
    conv_lhs => arg 2; rw [← Matrix.fromBlocks_toBlocks K]
    simp [pinTestMatrix, Matrix.fromBlocks_multiply]
  rw [hk]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply, Matrix.fromBlocks]

theorem det_pinTest_schur (K : Matrix (J ⊕ Q) (J ⊕ Q) R) (W : Matrix J J R)
    (hK : (1 - K.toBlocks₂₂).det ≠ 0) :
    (1 - pinTestMatrix R (Q := Q) W * K).det =
      (1 - K.toBlocks₂₂).det * (1 - W * hittingResolvent R K).det := by
  let _ : Invertible (1 - K.toBlocks₂₂) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hK)
  rw [pinTest_block_form, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 2
  simp only [hittingResolvent, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc, sub_sub]

theorem det_pinTest_zero (K : Matrix (J ⊕ Q) (J ⊕ Q) R) :
    (1 - pinTestMatrix R (Q := Q) 0 * K).det = (1 - K.toBlocks₂₂).det := by
  rw [pinTest_block_form]
  simp only [Matrix.zero_mul, sub_zero, neg_zero]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]

theorem det_pinTest_allHit (π : Equiv.Perm (J ⊕ Q)) (W : Matrix J J R)
    (h : AllHit π) :
    (1 - pinTestMatrix R (Q := Q) W * columnPerm R π).det =
      (1 - W * hittingResolvent R (columnPerm R π)).det := by
  have he : (1 - (columnPerm R π).toBlocks₂₂).det = 1 := by
    simpa only [Matrix.toBlocks₂₂, Matrix.submatrix, ite_eq_left h] using det_one_sub_columnPerm_QQ R π
  rw [det_pinTest_schur R _ _ (by rw [he]; exact one_ne_zero), he, one_mul]

end

section

variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]
variable {R : Type*} [Field R]

def hitWeight (μ : Ω → R) (π : Ω → Equiv.Perm (J ⊕ Q)) : R :=
  ∑ ω, if AllHit (π ω) then μ ω else 0

theorem allHit_determinant (μ : Ω → R) (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω))) :
    hitWeight μ π = (1 - (∑ ω, μ ω • columnPerm R (π ω)).toBlocks₂₂).det := by
  have ht := h (pinTestMatrix R (Q := Q) (0 : Matrix J J R))
  rw [det_pinTest_zero] at ht
  convert ht using 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [det_pinTest_zero]
  have he := det_one_sub_columnPerm_QQ R (π ω)
  simp only [Matrix.toBlocks₂₂, Matrix.submatrix] at he ⊢
  rw [he]
  by_cases hh : AllHit (π ω) <;> simp [hh]

theorem allHit_determinant_before_division (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω))) (W : Matrix J J R) :
    (∑ ω, if AllHit (π ω) then μ ω * (1 - W * hittingResolvent R (columnPerm R (π ω))).det
      else 0) = (1 - pinTestMatrix R (Q := Q) W * ∑ ω, μ ω • columnPerm R (π ω)).det := by
  rw [← h]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hh : AllHit (π ω)
  · rw [ite_eq_left hh, det_pinTest_allHit R _ _ hh]
  · rw [ite_eq_right hh, det_pinTest_of_not_allHit R _ _ hh, mul_zero]

theorem conditional_resolvent_determinant (μ : Ω → R)
    (π : Ω → Equiv.Perm (J ⊕ Q))
    (h : DeterminantLaw μ (fun ω => columnPerm R (π ω)))
    (hg : hitWeight μ π ≠ 0) (W : Matrix J J R) :
    (∑ ω, if AllHit (π ω) then (μ ω / hitWeight μ π) *
      (1 - W * hittingResolvent R (columnPerm R (π ω))).det else 0) =
      (1 - W * hittingResolvent R (∑ ω, μ ω • columnPerm R (π ω))).det := by
  have he := allHit_determinant μ π h
  have hk : (1 - (∑ ω, μ ω • columnPerm R (π ω)).toBlocks₂₂).det ≠ 0 := he ▸ hg
  have ht := allHit_determinant_before_division μ π h W
  rw [det_pinTest_schur R _ _ hk, ← he] at ht
  calc
    _ = (∑ ω, if AllHit (π ω) then μ ω *
        (1 - W * hittingResolvent R (columnPerm R (π ω))).det else 0) / hitWeight μ π := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp [div_mul_eq_mul_div]
    _ = _ := by rw [ht, mul_div_cancel_left₀ _ hg]

end

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {R : Type*} [CommRing R]

lemma det_one_sub_single_mul (A : Matrix J J R) (i j : J) :
    (1 - Matrix.single i j (1 : R) * A).det = 1 - A j i := by
  let U : Matrix J Unit R := fun k _ => if k = i then 1 else 0
  let V : Matrix Unit J R := fun _ k => A j k
  have hm : Matrix.single i j (1 : R) * A = U * V := by
    ext k l
    rw [Matrix.mul_apply, Matrix.mul_apply]
    by_cases hk : k = i
    · subst k
      simp [U, V, Matrix.single_apply]
    · simp [U, V, hk, Ne.symm hk]
  rw [hm, Matrix.det_one_sub_mul_comm, Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply]
  simp [U, V]

end Heisenberg.Exposure
end

end OAI
