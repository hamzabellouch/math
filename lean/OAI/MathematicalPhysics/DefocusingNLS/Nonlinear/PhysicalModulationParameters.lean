import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame

namespace OAI

/-! # The invertible leading map for the fourteen modulation parameters -/

namespace DefocusingNLS

noncomputable def physicalModulationParameterEquiv (b : ℝ) :
    ProfileSymmetryParameters ≃L[ℝ] ProfileSymmetryParameters where
  toFun p := (-p.1 + b * p.2.2, p.2.1, p.2.2)
  invFun p := (-p.1 + b * p.2.2, p.2.1, p.2.2)
  left_inv p := by
    rcases p with ⟨θ, v, t⟩
    simp only [Prod.mk.injEq, and_true]
    ring
  right_inv p := by
    rcases p with ⟨θ, v, t⟩
    simp only [Prod.mk.injEq, and_true]
    ring
  map_add' p q := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
      ring
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem physicalModulationParameterEquiv_apply (b : ℝ) (p : ProfileSymmetryParameters) :
    physicalModulationParameterEquiv b p = (-p.1 + b * p.2.2, p.2.1, p.2.2) := rfl

end DefocusingNLS

end OAI
