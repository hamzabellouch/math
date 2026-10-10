import OAI.LinearAlgebra.MatrixState.HilbertSchmidt

namespace OAI

section
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace RowColumn.MatrixState
variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev quarterRoot (A : Matrix C C ℂ) := CFC.sqrt (CFC.sqrt A)
def inverseQuarter (A : Matrix C C ℂ) : Matrix C C ℂ :=
  cfc (fun x : ℝ => x⁻¹) (quarterRoot A)
def quarterSupport (A : Matrix C C ℂ) : Matrix C C ℂ := quarterRoot A * inverseQuarter A

lemma quarter_positive (A : Matrix C C ℂ) : (quarterRoot A).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (CFC.sqrt A))
lemma quarter_square (A : Matrix C C ℂ) : quarterRoot A * quarterRoot A = CFC.sqrt A :=
  CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)
lemma quarter_four (A : Matrix C C ℂ) (hA : A.PosSemidef) : quarterRoot A ^ 4 = A := by
  calc
    _ = (quarterRoot A * quarterRoot A) * (quarterRoot A * quarterRoot A) := by noncomm_ring
    _ = A := by rw [quarter_square, CFC.sqrt_mul_sqrt_self A hA.nonneg]

lemma inverseQuarter_positive (A : Matrix C C ℂ) : (inverseQuarter A).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  apply inv_nonneg.mpr
  exact spectrum_nonneg_of_nonneg (CFC.sqrt_nonneg _) hx

lemma inverseQuarter_commute (A : Matrix C C ℂ) : Commute (inverseQuarter A) (quarterRoot A) := by
  exact (Commute.refl _).cfc (by rw [Matrix.star_eq_conjTranspose, (quarter_positive A).isHermitian.eq]; exact Commute.refl _) _

lemma quarter_inverse_quarter (A : Matrix C C ℂ) :
    quarterRoot A * inverseQuarter A * quarterRoot A = quarterRoot A := by
  let Q := quarterRoot A
  have hQ : IsSelfAdjoint Q := (quarter_positive A).isHermitian
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Q) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  change Q * cfc (fun x : ℝ => x⁻¹) Q * Q = Q
  calc
    _ = cfc (fun x : ℝ => x * x⁻¹ * x) Q := by
      rw [cfc_mul _ _ Q (hc _) (hc _), cfc_mul _ _ Q (hc _) (hc _), cfc_id' ℝ Q hQ]
    _ = Q := by
      rw [show (fun x : ℝ => x*x⁻¹*x) = (fun x => x) by funext x; simp, cfc_id' ℝ Q hQ]

lemma quarterSupport_hermitian (A : Matrix C C ℂ) : (quarterSupport A).IsHermitian := by
  change star (quarterRoot A * inverseQuarter A) = _
  rw [star_mul, Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose, (quarter_positive A).isHermitian.eq, (inverseQuarter_positive A).isHermitian.eq]
  exact inverseQuarter_commute A

lemma quarterSupport_mul_self (A : Matrix C C ℂ) : quarterSupport A * quarterSupport A = quarterSupport A := by
  change (quarterRoot A * inverseQuarter A) * (quarterRoot A * inverseQuarter A) = _
  rw [← mul_assoc, quarter_inverse_quarter]
  rfl

lemma quarterSupport_mul (A : Matrix C C ℂ) (hA : A.PosSemidef) : quarterSupport A * A = A := by
  conv_lhs => rhs; rw [← quarter_four A hA]
  conv_rhs => rw [← quarter_four A hA]
  change (quarterRoot A * inverseQuarter A) * quarterRoot A ^ 4 = quarterRoot A ^ 4
  calc
    _ = (quarterRoot A * inverseQuarter A * quarterRoot A) * quarterRoot A ^ 3 := by noncomm_ring
    _ = _ := by rw [quarter_inverse_quarter]; noncomm_ring

lemma quarter_whitening_mean (A : Matrix C C ℂ) (hA : A.PosSemidef) :
    inverseQuarter A * A * inverseQuarter A = quarterRoot A * quarterRoot A := by
  conv_lhs => lhs; rhs; rw [← quarter_four A hA]
  have hc := inverseQuarter_commute A
  calc
    _ = (inverseQuarter A * quarterRoot A) * quarterRoot A * quarterRoot A *
      (quarterRoot A * inverseQuarter A) := by noncomm_ring
    _ = (quarterRoot A * inverseQuarter A) * quarterRoot A * quarterRoot A *
      (quarterRoot A * inverseQuarter A) := by rw [hc.eq]
    _ = (quarterRoot A * inverseQuarter A) * quarterRoot A * quarterRoot A *
      (inverseQuarter A * quarterRoot A) := by conv_lhs => rhs; rw [← hc.eq]
    _ = (quarterRoot A * inverseQuarter A * quarterRoot A) *
      (quarterRoot A * inverseQuarter A * quarterRoot A) := by noncomm_ring
    _ = _ := by rw [quarter_inverse_quarter]

/-- Kernel propagation for positive matrices, used to justify all inverses on
supports in the quarter-root normalization, including singular states. -/
lemma positive_kernel_mono (S A P : Matrix C C ℂ) (hS : S.PosSemidef)
    (hle : S ≤ A) (hP : P.IsHermitian) (hPA : P*A=0) : P*S=0 := by
  have hcong : P*S*P ≤ P*A*P := by
    have hh := (show (A-S).PosSemidef from hle).conjTranspose_mul_mul_same P
    change (P*A*P-P*S*P).PosSemidef
    simpa only [hP.eq, Matrix.mul_sub, Matrix.sub_mul] using hh
  have hp : 0 ≤ P*S*P := by
    simpa only [hP.eq] using (hS.conjTranspose_mul_mul_same P).nonneg
  rw [hPA, zero_mul] at hcong
  have hz : P*S*P=0 := le_antisymm hcong hp
  let R : Matrix C C ℂ := CFC.sqrt S
  have hs : star R=R := (CFC.sqrt_nonneg S).isSelfAdjoint
  have hsq : R*R=S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hr : R*P=0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    rw [star_mul, hs, Matrix.star_eq_conjTranspose, hP.eq, ← mul_assoc, mul_assoc P R R, hsq, hz]
  have hl : P*R=0 := by simpa only [star_mul, hs, Matrix.star_eq_conjTranspose, hP.eq, star_zero] using congrArg star hr
  rw [← hsq, ← mul_assoc, hl, zero_mul]

lemma quarterSupport_of_le (A S : Matrix C C ℂ) (hA : A.PosSemidef)
    (hS : S.PosSemidef) (hle : S ≤ A) : quarterSupport A * S = S := by
  have hP : (1-quarterSupport A).IsHermitian := (Matrix.isHermitian_one).sub (quarterSupport_hermitian A)
  have hz : (1-quarterSupport A)*A=0 := by rw [sub_mul, one_mul, quarterSupport_mul A hA, sub_self]
  have hh := positive_kernel_mono S A (1-quarterSupport A) hS hle hP hz
  rw [sub_mul, one_mul] at hh
  exact (sub_eq_zero.mp hh).symm

lemma undo_quarter_whitening (A S : Matrix C C ℂ) (hS : S.IsHermitian)
    (hsupp : quarterSupport A * S=S) :
    quarterRoot A * (inverseQuarter A * S * inverseQuarter A) * quarterRoot A = S := by
  have hsupp' : S*quarterSupport A=S := by
    simpa only [star_mul, Matrix.star_eq_conjTranspose, hS.eq, (quarterSupport_hermitian A).eq] using congrArg star hsupp
  calc
    _ = quarterSupport A * S * quarterSupport A := by
      have hc := (inverseQuarter_commute A).eq
      dsimp only [quarterSupport]
      noncomm_ring [hc]
    _ = S := by rw [hsupp,hsupp']

end RowColumn.MatrixState

end
end

end OAI
