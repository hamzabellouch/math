import Mathlib

namespace OAI

/-! Unit entries, orthogonality, characters and the cubic matrix. -/

open scoped BigOperators Matrix

namespace HadamardSix

abbrev Index := Fin 6
abbrev Matrix6 := Matrix Index Index ℂ
abbrev Charge := Index → ℤ

def Unimodular (H : Matrix6) : Prop := ∀ i j, ‖H i j‖ = 1

def IsComplexHadamard (H : Matrix6) : Prop :=
  Unimodular H ∧ H.conjTranspose * H = (6 : ℂ) • (1 : Matrix6)

def HadamardEquivalent (H K : Matrix6) : Prop :=
  ∃ (r c : Equiv.Perm Index) (u v : Index → ℂ),
    (∀ i, ‖u i‖ = 1) ∧ (∀ j, ‖v j‖ = 1) ∧
    ∀ i j, K i j = u i * H (r i) (c j) * v j

def Balanced (a : Charge) : Prop := ∑ i, a i = 0

noncomputable def character (x : Index → ℂ) (a : Charge) : ℂ :=
  ∏ i, x i ^ a i

noncomputable def g (H : Matrix6) (a : Charge) : ℂ :=
  (6 : ℂ)⁻¹ * ∑ k, character (fun i => H i k) a

def permuteCharge (p : Equiv.Perm Index) (a : Charge) : Charge := fun i => a (p i)

def alpha : Charge := ![1, 1, 1, -1, -1, -1]

noncomputable def omega : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

def taoExponent (i j : Index) : ℤ :=
  if i = 0 ∨ j = 0 ∨ i = j then 0
  else if ((i.val : ℤ) - (j.val : ℤ)) % 5 = 1 ∨
    ((i.val : ℤ) - (j.val : ℤ)) % 5 = 4 then 1
  else -1

noncomputable def taoMatrix : Matrix6 := fun i j => omega ^ taoExponent i j

lemma unit_ne_zero {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  intro h
  simp [h] at hz

lemma unit_mul_star {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

lemma unit_star_mul {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  rw [mul_comm]
  exact unit_mul_star hz

lemma unit_inv {z : ℂ} (hz : ‖z‖ = 1) : z⁻¹ = star z := by
  apply inv_eq_of_mul_eq_one_right
  exact unit_mul_star hz

lemma Unimodular.entry_ne_zero {H : Matrix6} (hH : Unimodular H) (i j : Index) :
    H i j ≠ 0 := unit_ne_zero (hH i j)

lemma IsComplexHadamard.unimodular {H : Matrix6} (hH : IsComplexHadamard H) :
    Unimodular H := hH.1

lemma IsComplexHadamard.mul_conjTranspose {H : Matrix6} (hH : IsComplexHadamard H) :
    H * H.conjTranspose = (6 : ℂ) • (1 : Matrix6) := by
  have hleft : ((6 : ℂ)⁻¹ • H.conjTranspose) * H = 1 := by
    rw [Matrix.smul_mul, hH.2, smul_smul]
    norm_num
  have hright := mul_eq_one_comm.mp hleft
  rw [Matrix.mul_smul] at hright
  have h := congrArg (fun K : Matrix6 => (6 : ℂ) • K) hright
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul] using h

lemma IsComplexHadamard.column_orthogonality {H : Matrix6} (hH : IsComplexHadamard H)
    (j k : Index) :
    ∑ i, star (H i j) * H i k = if j = k then 6 else 0 := by
  have h := congr_fun (congr_fun hH.2 j) k
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] using h

lemma IsComplexHadamard.row_orthogonality {H : Matrix6} (hH : IsComplexHadamard H)
    (i j : Index) :
    ∑ k, H i k * star (H j k) = if i = j then 6 else 0 := by
  have h := congr_fun (congr_fun hH.mul_conjTranspose i) j
  simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] using h

lemma isComplexHadamard_of_rows {H : Matrix6} (hu : Unimodular H)
    (hr : ∀ i j, ∑ k, H i k * star (H j k) = if i = j then 6 else 0) :
    IsComplexHadamard H := by
  have heq : H * H.conjTranspose = (6 : ℂ) • (1 : Matrix6) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.smul_apply] using hr i j
  have hleft : H * ((6 : ℂ)⁻¹ • H.conjTranspose) = 1 := by
    rw [Matrix.mul_smul, heq, smul_smul]
    norm_num
  have hright := mul_eq_one_comm.mp hleft
  rw [Matrix.smul_mul] at hright
  have h := congrArg (fun K : Matrix6 => (6 : ℂ) • K) hright
  refine ⟨hu, ?_⟩
  simpa only [smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0), one_smul] using h

lemma IsComplexHadamard.transpose {H : Matrix6} (hH : IsComplexHadamard H) :
    IsComplexHadamard H.transpose := by
  refine isComplexHadamard_of_rows (fun i j => hH.1 j i) ?_
  intro i j
  simpa [mul_comm, eq_comm] using hH.column_orthogonality j i

lemma IsComplexHadamard.conjugate {H : Matrix6} (hH : IsComplexHadamard H) :
    IsComplexHadamard (fun i j => star (H i j)) := by
  refine isComplexHadamard_of_rows (fun i j => by simpa using hH.1 i j) ?_
  intro i j
  have h := congrArg star (hH.row_orthogonality i j)
  simpa only [star_sum, star_mul, star_star, apply_ite star, star_ofNat, star_zero, mul_comm]
    using h

end HadamardSix

end OAI
