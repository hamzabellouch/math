import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteSymmetryCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorEigenvector

namespace OAI

/-! The backward symmetry evolution is a contraction in product coordinates. -/

namespace DefocusingNLS
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def symmetryCoordinateEvolution (G : V →L[ℂ] V) (t : ℝ) :
    SymmetryCoordinates G →L[ℂ] SymmetryCoordinates G :=
  (ContinuousLinearMap.id ℂ _).prodMap
    (((Real.exp t : ℂ) • ContinuousLinearMap.id ℂ _).prodMap
      ((Real.exp (t/2) : ℂ) • ContinuousLinearMap.id ℂ _))

theorem symmetryCoordinateEvolution_inverse (G : V →L[ℂ] V) (t : ℝ)
    (u : SymmetryCoordinates G) :
    symmetryCoordinateEvolution G t (symmetryCoordinateEvolution G (-t) u)=u := by
  change (u.1, ((Real.exp t : ℂ) • ((Real.exp (-t) : ℂ) • u.2.1),
    (Real.exp (t/2) : ℂ) • ((Real.exp ((-t)/2) : ℂ) • u.2.2)))=u
  rw [smul_smul,smul_smul,← Complex.ofReal_mul,← Complex.ofReal_mul,
    ← Real.exp_add,← Real.exp_add]
  simp only [add_neg_cancel,neg_div,Real.exp_zero,Complex.ofReal_one,one_smul]

theorem symmetryCoordinateEvolution_backward_norm (G : V →L[ℂ] V)
    (t : ℝ) (ht : 0≤t) : ‖symmetryCoordinateEvolution G (-t)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖(u.1, ((Real.exp (-t) : ℂ) • u.2.1,
    (Real.exp ((-t)/2) : ℂ) • u.2.2))‖ ≤ 1*‖u‖
  simp only [Prod.norm_def,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),one_mul]
  apply max_le_max le_rfl
  apply max_le_max
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))

theorem symmetryCoordinateEvolution_intertwines [CompleteSpace V]
    (G : V →L[ℂ] V) (t : ℝ) (u : SymmetryCoordinates G) :
    NormedSpace.exp (t • G) (symmetryCoordinateSum G u)=
      symmetryCoordinateSum G (symmetryCoordinateEvolution G t u) := by
  have h0 : G (u.1 : V)=(0 : ℂ) • (u.1 : V) :=
    Module.End.mem_eigenspace_iff.mp u.1.property
  have h1 : G (u.2.1 : V)=(1 : ℂ) • (u.2.1 : V) :=
    Module.End.mem_eigenspace_iff.mp u.2.1.property
  have hh : G (u.2.2 : V)=(1/2 : ℂ) • (u.2.2 : V) :=
    Module.End.mem_eigenspace_iff.mp u.2.2.property
  change NormedSpace.exp (t • G) ((u.1 : V)+(u.2.1 : V)+(u.2.2 : V))=
    (u.1 : V)+(Real.exp t : ℂ) • (u.2.1 : V)+(Real.exp (t/2) : ℂ) • (u.2.2 : V)
  rw [map_add,map_add,real_smul_operator_exp_apply_of_eigenvector G 0 _ h0,
    real_smul_operator_exp_apply_of_eigenvector G 1 _ h1,
    real_smul_operator_exp_apply_of_eigenvector G (1/2) _ hh]
  have hct : (t : ℂ)*(1/2 : ℂ)=((t/2 : ℝ) : ℂ) := by push_cast; ring
  simp only [mul_zero,Complex.exp_zero,one_smul,mul_one,hct,← Complex.ofReal_exp]

end DefocusingNLS

end OAI
