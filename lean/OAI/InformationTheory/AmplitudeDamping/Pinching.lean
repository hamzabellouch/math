import OAI.InformationTheory.AmplitudeDamping.LogDetEntropy

namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem inv_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * A * (star U : Matrix ι ι ℂ))⁻¹ =
      (U : Matrix ι ι ℂ) * A⁻¹ * (star U : Matrix ι ι ℂ) := by
  have hu : (U : Matrix ι ι ℂ)⁻¹ = (star U : Matrix ι ι ℂ) :=
    Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self U)
  have hs : (star U : Matrix ι ι ℂ)⁻¹ = (U : Matrix ι ι ℂ) :=
    Matrix.inv_eq_right_inv (by simpa only [Unitary.coe_star] using Unitary.coe_star_mul_self U)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hu, hs, Matrix.mul_assoc]

theorem blockLogDet_unitary (U V : Matrix.unitaryGroup ι ℂ) (Z D E : Matrix ι ι ℂ) :
    blockLogDet ((U : Matrix ι ι ℂ)*Z*(star V : Matrix ι ι ℂ))
      ((U : Matrix ι ι ℂ)*D*(star U : Matrix ι ι ℂ))
      ((V : Matrix ι ι ℂ)*E*(star V : Matrix ι ι ℂ)) = blockLogDet Z D E := by
  have he : (U : Matrix ι ι ℂ)*D*(star U : Matrix ι ι ℂ) +
      ((U : Matrix ι ι ℂ)*Z*(star V : Matrix ι ι ℂ)) *
      (((V : Matrix ι ι ℂ)*E*(star V : Matrix ι ι ℂ))⁻¹) *
      ((U : Matrix ι ι ℂ)*Z*(star V : Matrix ι ι ℂ))ᴴ =
      (U : Matrix ι ι ℂ)*(D+Z*E⁻¹*Zᴴ)*(star U : Matrix ι ι ℂ) := by
    rw [inv_unitary_conj]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
    have hv : star (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self V
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (V : Matrix ι ι ℂ)) (V : Matrix ι ι ℂ),
      hv, Matrix.one_mul, Matrix.mul_add, Matrix.add_mul]
  unfold blockLogDet
  rw [he]
  change Real.log ‖(Unitary.conjStarAlgAut ℂ _ U (D+Z*E⁻¹*Zᴴ)).det‖ -
    Real.log ‖(Unitary.conjStarAlgAut ℂ _ U D).det‖ = _
  rw [det_unitary_conj, det_unitary_conj]

def flipSign (k : ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal (fun i ↦ if i = k then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      by_cases hi : i = k <;> simp [hi]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]⟩

def partialPinch (s : Finset ι) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ if i = j ∨ (i ∉ s ∧ j ∉ s) then A i j else 0

omit [Fintype ι] in
theorem partialPinch_empty (A : Matrix ι ι ℂ) : partialPinch ∅ A = A := by
  ext i j; simp [partialPinch]

theorem partialPinch_univ (A : Matrix ι ι ℂ) :
    partialPinch Finset.univ A = Matrix.diagonal (fun i ↦ A i i) := by
  ext i j
  by_cases h : i = j <;> simp [partialPinch, Matrix.diagonal, h]

theorem flipSign_conj_apply (k i j : ι) (A : Matrix ι ι ℂ) :
    ((flipSign k : Matrix ι ι ℂ) * A * (star (flipSign k) : Matrix ι ι ℂ)) i j =
      (if i = k then (-1 : ℂ) else 1) * A i j * (if j = k then (-1 : ℂ) else 1) := by
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [flipSign, Matrix.star_eq_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, hi, hj]

theorem partialPinch_insert (s : Finset ι) (k : ι) (A : Matrix ι ι ℂ) :
    partialPinch (insert k s) A = (1/2 : ℝ) • partialPinch s A +
      (1/2 : ℝ) • ((flipSign k : Matrix ι ι ℂ) * partialPinch s A *
        (star (flipSign k) : Matrix ι ι ℂ)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, flipSign_conj_apply, partialPinch,
    Finset.mem_insert, not_or]
  by_cases hij : i = j
  · subst j
    by_cases hi : i = k <;> simp [hi, Complex.real_smul] <;> ring
  · by_cases hi : i = k <;> by_cases hj : j = k <;>
      by_cases his : i ∈ s <;> by_cases hjs : j ∈ s <;>
      simp_all [Complex.real_smul]; ring

theorem flipSign_diagonal (k : ι) (z : ι → ℂ) :
    (flipSign k : Matrix ι ι ℂ) * Matrix.diagonal z *
      (star (flipSign k) : Matrix ι ι ℂ) = Matrix.diagonal z := by
  ext i j
  rw [flipSign_conj_apply]
  by_cases h : i = j
  · subst j; by_cases hi : i = k <;> simp [hi]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem partialPinch_posDef {D : Matrix ι ι ℂ} (hD : D.PosDef) (s : Finset ι) :
    (partialPinch s D).PosDef := by
  induction s using Finset.induction_on with
  | empty => simpa only [partialPinch_empty] using hD
  | @insert k s _ ih =>
    rw [partialPinch_insert]
    exact posDef_segment ih (ih.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := flipSign k))))
      (by norm_num) (by norm_num) (by norm_num)

theorem blockLogDet_partialPinch_le (z : ι → ℂ) {D E : Matrix ι ι ℂ}
    (hD : D.PosDef) (hE : E.PosDef) (s : Finset ι) :
    blockLogDet (Matrix.diagonal z) (partialPinch s D) (partialPinch s E) ≤
      blockLogDet (Matrix.diagonal z) D E := by
  induction s using Finset.induction_on with
  | empty => simp only [partialPinch_empty, le_refl]
  | @insert k s _ ih =>
    have hDp := partialPinch_posDef hD s
    have hEp := partialPinch_posDef hE s
    have hDc := hDp.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := flipSign k)))
    have hEc := hEp.mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_iff_isUnit.mpr (Unitary.isUnit_coe (U := flipSign k)))
    have hh := (convexOn_blockLogDet (Matrix.diagonal z)).2
      (x := (partialPinch s D, partialPinch s E))
      (y := ((flipSign k : Matrix ι ι ℂ) * partialPinch s D * (star (flipSign k) : Matrix ι ι ℂ),
        (flipSign k : Matrix ι ι ℂ) * partialPinch s E * (star (flipSign k) : Matrix ι ι ℂ)))
      ⟨hDp,hEp⟩ ⟨hDc,hEc⟩
      (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
    have he := blockLogDet_unitary (flipSign k) (flipSign k) (Matrix.diagonal z)
      (partialPinch s D) (partialPinch s E)
    rw [flipSign_diagonal] at he
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hh
    rw [← partialPinch_insert, ← partialPinch_insert, he] at hh
    linarith

theorem blockLogDet_diagonal_le (z : ι → ℂ) {D E : Matrix ι ι ℂ}
    (hD : D.PosDef) (hE : E.PosDef) :
    blockLogDet (Matrix.diagonal z) (Matrix.diagonal (fun i ↦ D i i))
      (Matrix.diagonal (fun i ↦ E i i)) ≤ blockLogDet (Matrix.diagonal z) D E := by
  simpa only [partialPinch_univ] using blockLogDet_partialPinch_le z hD hE Finset.univ

end GAD

end

end OAI
