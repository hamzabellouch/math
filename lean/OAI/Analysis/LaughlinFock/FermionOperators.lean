import Mathlib
import OAI.Analysis.LaughlinFock.Model

namespace OAI

/-! Fermion Operators. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open scoped BigOperators Polynomial
open Polynomial
def fermionSign {Q : ℕ} (j : Orbital Q) (B : Occupation Q) : ℂ :=
  (-1 : ℂ) ^ (B.filter (fun i => i < j)).card

theorem annihilator_apply {Q : ℕ} (j : Orbital Q) (A B : Occupation Q) :
    annihilator Q j A B =
      if j ∈ B ∧ A = B.erase j then fermionSign j B else 0 := rfl

@[simp] theorem fermionSign_star {Q : ℕ} (j : Orbital Q) (B : Occupation Q) :
    star (fermionSign j B) = fermionSign j B := by simp [fermionSign]

@[simp] theorem fermionSign_mul_self {Q : ℕ} (j : Orbital Q) (B : Occupation Q) :
    fermionSign j B * fermionSign j B = 1 := by
  unfold fermionSign
  rw [← mul_pow]
  simp

private theorem sign_insert_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hi : i ∉ B) (hij : i < j) :
    fermionSign j (insert i B) = -fermionSign j B := by
  simp [fermionSign, Finset.filter_insert, hi, hij, pow_succ]

private theorem sign_insert_not_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hij : ¬ i < j) : fermionSign j (insert i B) = fermionSign j B := by
  simp [fermionSign, Finset.filter_insert, hij]

private theorem sign_erase_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hi : i ∈ B) (hij : i < j) :
    fermionSign j (B.erase i) = -fermionSign j B := by
  have h := sign_insert_lt i j (B.erase i) (Finset.notMem_erase i B) hij
  rw [Finset.insert_erase hi] at h
  rw [h]
  simp

private theorem sign_erase_not_lt {Q : ℕ} (i j : Orbital Q) (B : Occupation Q)
    (hij : ¬ i < j) : fermionSign j (B.erase i) = fermionSign j B := by
  by_cases hi : i ∈ B
  · have h := sign_insert_not_lt i j (B.erase i) hij
    rw [Finset.insert_erase hi] at h
    exact h.symm
  · rw [Finset.erase_eq_of_notMem hi]

 
def creator (Q : ℕ) (j : Orbital Q) : FockMatrix Q := fun A B =>
  if j ∉ B ∧ A = insert j B then fermionSign j B else 0

 
theorem mul_annihilator_apply {Q : ℕ} (M : FockMatrix Q) (j : Orbital Q)
    (A B : Occupation Q) :
    (M * annihilator Q j) A B =
      if j ∈ B then M A (B.erase j) * fermionSign j B else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ B
  · simp [annihilator, hj, mul_ite, fermionSign]
  · simp [annihilator, hj]

 
theorem mul_creator_apply {Q : ℕ} (M : FockMatrix Q) (j : Orbital Q)
    (A B : Occupation Q) :
    (M * creator Q j) A B =
      if j ∉ B then M A (insert j B) * fermionSign j B else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : j ∈ B
  · simp [creator, hj]
  · simp [creator, hj, mul_ite]

 
theorem creator_eq_adjoint (Q : ℕ) (j : Orbital Q) :
    creator Q j = (annihilator Q j)ᴴ := by
  classical
  ext A B
  by_cases hc : j ∉ B ∧ A = insert j B
  · rcases hc with ⟨hj, rfl⟩
    simp [creator, annihilator_apply, Matrix.conjTranspose_apply, hj, sign_insert_not_lt j j B (lt_irrefl j)]
  · have hd : ¬ (j ∈ A ∧ B = A.erase j) := by
      rintro ⟨hj, rfl⟩
      apply hc
      exact ⟨Finset.notMem_erase _ _, (Finset.insert_erase hj).symm⟩
    simp [creator, annihilator, Matrix.conjTranspose_apply, hc, hd]

 
theorem annihilator_square (Q : ℕ) (j : Orbital Q) :
    annihilator Q j * annihilator Q j = 0 := by
  classical
  ext A B
  rw [mul_annihilator_apply]
  by_cases hj : j ∈ B <;> simp [annihilator, hj]

 
theorem annihilator_anticommute (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * annihilator Q j + annihilator Q j * annihilator Q i = 0 := by
  classical
  by_cases hij : i=j
  · subst j; rw [annihilator_square]; simp
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, mul_annihilator_apply]
  by_cases hi : i ∈ B
  · by_cases hj : j ∈ B
    · simp only [hi, hj, ite_true, annihilator_apply,
        Finset.mem_erase, ne_eq, hij, Ne.symm hij, not_false_eq_true, true_and, and_true]
      rw [Finset.erase_right_comm]
      by_cases hab : A = (B.erase i).erase j
      · simp only [hab, ite_true]
        rcases lt_or_gt_of_ne hij with hij | hji
        · rw [sign_erase_lt i j B hi hij,
            sign_erase_not_lt j i B (not_lt.mpr hij.le)]
          ring
        · rw [sign_erase_lt j i B hj hji,
            sign_erase_not_lt i j B (not_lt.mpr hji.le)]
          ring
      · simp [hab]
    · simp [hi, hj, annihilator, Finset.mem_erase]
  · simp [hi, annihilator, Finset.mem_erase]

 
theorem creator_mul_annihilator (Q : ℕ) (j : Orbital Q) :
    creator Q j * annihilator Q j =
      Matrix.diagonal (fun B : Occupation Q => if j ∈ B then (1 : ℂ) else 0) := by
  classical
  ext A B
  rw [mul_annihilator_apply]
  by_cases hAB : A = B
  · subst A
    by_cases hj : j ∈ B <;>
      simp [hj, creator,
        sign_erase_not_lt j j B (lt_irrefl j)]
  · by_cases hj : j ∈ B <;> simp [creator, hj, hAB]

 
theorem annihilator_mul_creator (Q : ℕ) (j : Orbital Q) :
    annihilator Q j * creator Q j =
      Matrix.diagonal (fun B : Occupation Q => if j ∈ B then (0 : ℂ) else 1) := by
  classical
  ext A B
  rw [mul_creator_apply]
  by_cases hAB : A = B
  · subst A
    by_cases hj : j ∈ B <;>
      simp [annihilator_apply, hj,
        sign_insert_not_lt j j B (lt_irrefl j)]
  · by_cases hj : j ∈ B <;> simp [annihilator_apply, hj, hAB]

 
theorem annihilator_creator_anticommute (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * creator Q j + creator Q j * annihilator Q i =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, annihilator_mul_creator, creator_mul_annihilator]
    ext A B
    by_cases hi : i ∈ A <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hi]
  rw [ite_eq_right hij]
  ext A B
  simp only [Matrix.add_apply, Matrix.zero_apply, mul_annihilator_apply, mul_creator_apply]
  by_cases hi : i ∈ B
  · by_cases hj : j ∈ B
    · simp [hi, hj, creator, Finset.mem_erase, Ne.symm hij]
    · simp only [hi, hj, not_false_eq_true, ite_true, annihilator_apply, creator,
        Finset.mem_insert, Finset.mem_erase, hij, Ne.symm hij, false_or,
        ne_eq, not_false_eq_true, true_and]
      have he : (insert j B).erase i = insert j (B.erase i) := by
        ext k
        simp only [Finset.mem_erase, Finset.mem_insert]
        by_cases hki : k=i <;> by_cases hkj : k=j <;> simp_all
      rw [he]
      by_cases hAB : A = insert j (B.erase i)
      · simp only [hAB, ite_true]
        rcases lt_or_gt_of_ne hij with hij | hji
        · rw [sign_insert_not_lt j i B (not_lt.mpr hij.le), sign_erase_lt i j B hi hij]
          ring
        · rw [sign_insert_lt j i B hj hji, sign_erase_not_lt i j B (not_lt.mpr hji.le)]
          ring
      · simp [hAB]
  · by_cases hj : j ∈ B <;> simp [hi, hj, annihilator_apply, hij]

 
theorem annihilator_adjoint_anticommute (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * (annihilator Q j)ᴴ + (annihilator Q j)ᴴ * annihilator Q i =
      if i = j then 1 else 0 := by
  rw [← creator_eq_adjoint]
  exact annihilator_creator_anticommute Q i j

 

theorem annihilator_norm_sq (Q : ℕ) (j : Orbital Q) (ψ : Occupation Q → ℂ) :
    (∑ A : Occupation Q, ‖(annihilator Q j *ᵥ ψ) A‖^2) =
      ∑ B : Occupation Q, if j ∈ B then ‖ψ B‖^2 else 0 := by
  classical
  have hg := congrArg Complex.re (gram_quadratic_form (annihilator Q j) ψ)
  rw [← creator_eq_adjoint, creator_mul_annihilator] at hg
  have hs : (star (annihilator Q j *ᵥ ψ) ⬝ᵥ (annihilator Q j *ᵥ ψ)).re =
      ∑ A : Occupation Q, ‖(annihilator Q j *ᵥ ψ) A‖^2 := by
    simp [dotProduct, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow]
  rw [hs] at hg
  rw [← hg]
  simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro B _
  by_cases hj : j ∈ B <;>
    simp [hj, RCLike.star_def, RCLike.conj_mul, ← Complex.ofReal_pow]

 
theorem annihilator_contracts (Q : ℕ) (j : Orbital Q) (ψ : Occupation Q → ℂ) :
    (∑ A : Occupation Q, ‖(annihilator Q j *ᵥ ψ) A‖^2) ≤
      ∑ B : Occupation Q, ‖ψ B‖^2 := by
  rw [annihilator_norm_sq]
  apply Finset.sum_le_sum
  intro B _
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

 

theorem fourAnnihilator_norm_le_pair (Q p : ℕ) (j k : Orbital Q)
    (ψ : Occupation Q → ℂ) :
    (∑ A : Occupation Q,
      ‖((annihilator Q k * annihilator Q j * pairAnnihilator Q p) *ᵥ ψ) A‖^2) ≤
      ∑ A : Occupation Q, ‖(pairAnnihilator Q p *ᵥ ψ) A‖^2 := by
  have hk := annihilator_contracts Q k (annihilator Q j *ᵥ (pairAnnihilator Q p *ᵥ ψ))
  have hj := annihilator_contracts Q j (pairAnnihilator Q p *ᵥ ψ)
  simpa only [← Matrix.mulVec_mulVec] using hk.trans hj

 
def orbitalDelta (Q : ℕ) (i j : Orbital Q) : FockMatrix Q := if i=j then 1 else 0

private theorem delta_comm (Q : ℕ) (i j : Orbital Q) (M : FockMatrix Q) :
    M * orbitalDelta Q i j = orbitalDelta Q i j * M := by
  classical
  by_cases hij : i=j <;> simp [orbitalDelta, hij]

private theorem annihilator_creator_swap (Q : ℕ) (i j : Orbital Q) :
    annihilator Q i * creator Q j =
      orbitalDelta Q i j - creator Q j * annihilator Q i :=
  eq_sub_of_add_eq (annihilator_creator_anticommute Q i j)

 

theorem pair_normal_order (Q : ℕ) (i j k l : Orbital Q) :
    (annihilator Q j * annihilator Q i) * (creator Q k * creator Q l) =
      orbitalDelta Q i k * orbitalDelta Q j l -
      orbitalDelta Q j k * orbitalDelta Q i l -
      orbitalDelta Q i k * creator Q l * annihilator Q j +
      orbitalDelta Q j k * creator Q l * annihilator Q i +
      orbitalDelta Q i l * creator Q k * annihilator Q j -
      orbitalDelta Q j l * creator Q k * annihilator Q i +
      creator Q k * creator Q l * annihilator Q j * annihilator Q i := by
  classical
  let I := annihilator Q i
  let J := annihilator Q j
  let K := creator Q k
  let L := creator Q l
  let E := orbitalDelta Q i k
  let F := orbitalDelta Q j k
  let G := orbitalDelta Q i l
  let H := orbitalDelta Q j l
  have hIK : I*K = E-K*I := annihilator_creator_swap Q i k
  have hJK : J*K = F-K*J := annihilator_creator_swap Q j k
  have hIL : I*L = G-L*I := annihilator_creator_swap Q i l
  have hJL : J*L = H-L*J := annihilator_creator_swap Q j l
  have hJE : J*E = E*J := delta_comm Q i k J
  have hKJG : (K*J)*G = G*(K*J) := delta_comm Q i l (K*J)
  have hKH : K*H = H*K := delta_comm Q j l K
  change (J*I)*(K*L) = E*H-F*G-E*L*J+F*L*I+G*K*J-H*K*I+K*L*J*I
  calc
    _ = J*(I*K)*L := by noncomm_ring
    _ = J*(E-K*I)*L := by rw [hIK]
    _ = J*E*L-(J*K)*(I*L) := by noncomm_ring
    _ = E*J*L-(F-K*J)*(G-L*I) := by rw [hJE, hJK, hIL]
    _ = E*(J*L)-(F-K*J)*(G-L*I) := by noncomm_ring
    _ = E*(H-L*J)-(F-K*J)*(G-L*I) := by rw [hJL]
    _ = E*H-F*G-E*L*J+F*L*I+(K*J)*G-K*(J*L)*I := by noncomm_ring
    _ = E*H-F*G-E*L*J+F*L*I+G*(K*J)-K*(H-L*J)*I := by rw [hKJG, hJL]
    _ = E*H-F*G-E*L*J+F*L*I+G*K*J-(K*H)*I+K*L*J*I := by noncomm_ring
    _ = _ := by rw [hKH]
end LaughlinFock
end

end OAI
