import OAI.Analysis.KadisonKastler.RepresentedCorner

namespace OAI

/-! # Extending a corner unitary by the identity

A unitary on a closed subspace extends to a unitary on the ambient Hilbert
space, acting as the identity on the orthogonal complement. Its displacement
from the identity is exactly the displacement in the corner.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

@[simp] theorem starProjection_mul_cornerExtension (T : E →L[ℂ] E) :
    E.starProjection * cornerExtension E T = cornerExtension E T := by
  rw [← cornerExtension_one E, ← cornerExtension_mul, one_mul]

@[simp] theorem cornerExtension_mul_starProjection (T : E →L[ℂ] E) :
    cornerExtension E T * E.starProjection = cornerExtension E T := by
  rw [← cornerExtension_one E, ← cornerExtension_mul, mul_one]

@[simp] theorem complement_mul_cornerExtension (T : E →L[ℂ] E) :
    (1 - E.starProjection) * cornerExtension E T = 0 := by
  rw [sub_mul, one_mul, starProjection_mul_cornerExtension, sub_self]

@[simp] theorem cornerExtension_mul_complement (T : E →L[ℂ] E) :
    cornerExtension E T * (1 - E.starProjection) = 0 := by
  rw [mul_sub, mul_one, cornerExtension_mul_starProjection, sub_self]

variable [CompleteSpace H]

private theorem corner_starProjection_star : star E.starProjection = E.starProjection := by
  rw [← cornerExtension_one E, ← cornerExtension_star]
  exact congrArg (cornerExtension E) (star_one (R := E →L[ℂ] E))

omit [CompleteSpace H] in
private theorem corner_complement_sq :
    (1 - E.starProjection) * (1 - E.starProjection) = 1 - E.starProjection := by
  have hp : E.starProjection * E.starProjection = E.starProjection := by
    simpa only [cornerExtension_one] using
      starProjection_mul_cornerExtension E (1 : E →L[ℂ] E)
  rw [mul_sub, sub_mul, sub_mul, one_mul, mul_one, one_mul, hp, sub_self, sub_zero]

theorem cornerExtension_add_complement_mem_unitary (v : unitary (E →L[ℂ] E)) :
    cornerExtension E (v : E →L[ℂ] E) + (1 - E.starProjection) ∈
      unitary (H →L[ℂ] H) := by
  have hstar : star (1 - E.starProjection) = 1 - E.starProjection := by
    rw [star_sub, star_one, corner_starProjection_star]
  apply Unitary.mem_iff.mpr
  constructor
  · rw [star_add, hstar, ← cornerExtension_star, add_mul, mul_add, mul_add,
      ← cornerExtension_mul, Unitary.star_mul_self_of_mem v.property,
      cornerExtension_one, cornerExtension_mul_complement,
      complement_mul_cornerExtension, corner_complement_sq]
    abel
  · rw [star_add, hstar, ← cornerExtension_star, add_mul, mul_add, mul_add,
      ← cornerExtension_mul, Unitary.mul_star_self_of_mem v.property,
      cornerExtension_one, cornerExtension_mul_complement,
      complement_mul_cornerExtension, corner_complement_sq]
    abel

/-- The unitary equal to `v` on `E` and to the identity on `Eᗮ`. -/
def cornerUnitary (v : unitary (E →L[ℂ] E)) : unitary (H →L[ℂ] H) :=
  ⟨cornerExtension E (v : E →L[ℂ] E) + (1 - E.starProjection),
    cornerExtension_add_complement_mem_unitary E v⟩

@[simp] theorem coe_cornerUnitary (v : unitary (E →L[ℂ] E)) :
    (cornerUnitary E v : H →L[ℂ] H) =
      cornerExtension E (v : E →L[ℂ] E) + (1 - E.starProjection) := rfl

@[simp] theorem cornerUnitary_apply (v : unitary (E →L[ℂ] E)) (x : E) :
    (cornerUnitary E v : H →L[ℂ] H) (x : H) = ((v : E →L[ℂ] E) x : H) := by
  simp only [coe_cornerUnitary, add_apply, sub_apply, one_apply_eq_self,
    cornerExtension_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.starProjection_mem_subspace_eq_self, sub_self, add_zero]

theorem cornerUnitary_sub_one (v : unitary (E →L[ℂ] E)) :
    (cornerUnitary E v : H →L[ℂ] H) - 1 =
      cornerExtension E ((v : E →L[ℂ] E) - 1) := by
  rw [coe_cornerUnitary, map_sub, cornerExtension_one]
  abel

@[simp] theorem norm_cornerUnitary_sub_one (v : unitary (E →L[ℂ] E)) :
    ‖(cornerUnitary E v : H →L[ℂ] H) - 1‖ = ‖(v : E →L[ℂ] E) - 1‖ := by
  rw [cornerUnitary_sub_one, norm_cornerExtension]

theorem cornerUnitary_mem {M : VonNeumannAlgebra H}
    (hp : E.starProjection ∈ M) (v : unitary (E →L[ℂ] E))
    (hv : (v : E →L[ℂ] E) ∈ representedCorner E M hp) :
    (cornerUnitary E v : H →L[ℂ] H) ∈ M :=
  M.add_mem hv (M.sub_mem M.one_mem hp)

/-- Extending by the identity intertwines corner and ambient conjugation. -/
theorem unitaryConj_cornerExtension (v : unitary (E →L[ℂ] E)) (T : E →L[ℂ] E) :
    unitaryConj (cornerUnitary E v) (cornerExtension E T) =
      cornerExtension E (unitaryConj v T) := by
  have hl : (cornerUnitary E v : H →L[ℂ] H) * cornerExtension E T =
      cornerExtension E ((v : E →L[ℂ] E) * T) := by
    rw [coe_cornerUnitary, add_mul, complement_mul_cornerExtension, add_zero,
      ← cornerExtension_mul]
  have hr (S : E →L[ℂ] E) :
      cornerExtension E S * star (cornerUnitary E v : H →L[ℂ] H) =
        cornerExtension E (S * star (v : E →L[ℂ] E)) := by
    rw [coe_cornerUnitary, star_add, star_sub, star_one, corner_starProjection_star,
      mul_add, cornerExtension_mul_complement, add_zero,
      ← cornerExtension_star, ← cornerExtension_mul]
  unfold unitaryConj
  rw [hl, hr]

end

end KadisonKastler

end OAI
