import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Computability.UniqueGames.Quadratic.Block

namespace OAI

section

/-! The binary-linear parametrization and dimension of the v2 quadratic block. -/

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev lineBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (line v).restrictScalars (ZMod 2)

abbrev hyperplaneBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (hyperplane v).restrictScalars (ZMod 2)

omit [Algebra (ZMod 2) F] in
private theorem Q_cancel (a w : Vec F) : Q a + (w + Q a) = w := by
  calc
    _ = w + (Q a + Q a) := by ac_rfl
    _ = w := by rw [vec_add_self, add_zero]

/-- The parametrization `(a,w) ↦ (a,Q(a)+w)` is a binary-linear bijection.
It is not asserted to be field-linear: squaring along a field line is only
binary-linear. -/
def blockParametrization (v : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ₗ[ZMod 2] U v where
  toFun p := ⟨((p.1 : Vec F), Q (p.1 : Vec F) + (p.2 : Vec F)),
    pair_mem_U v p.1 p.2 p.1.2 p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 + Q p.1.1, p.2.2⟩)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) = p.2
      have h : Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) =
          Q (p.1 : Vec F) + ((p.2 : Vec F) + Q (p.1 : Vec F)) := by rw [add_assoc]
      rw [h, Q_cancel]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Q_cancel p.1.1 p.1.2
  map_add' := by
    intro p q
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Q ((p.1 : Vec F) + (q.1 : Vec F)) + ((p.2 : Vec F) + (q.2 : Vec F)) =
        (Q (p.1 : Vec F) + (p.2 : Vec F)) + (Q (q.1 : Vec F) + (q.2 : Vec F))
      rw [Q_add_of_mem_line v p.1 q.1 p.1.2 q.1.2]
      ac_rfl
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · apply Subtype.ext
      apply Prod.ext <;> simp [Q_zero]
    · simp

/-- The dot-product functional over the large field. -/
def dotLinear (v : Vec F) : Vec F →ₗ[F] F where
  toFun := dot v
  map_add' := dot_add_right v
  map_smul' := by intro t y; exact dot_smul_right v y t

omit [CharP F 2] [Algebra (ZMod 2) F] in
@[simp] theorem dotLinear_apply (v y : Vec F) : dotLinear v y = dot v y := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_ker (v : Vec F) : LinearMap.ker (dotLinear v) = hyperplane v := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_surjective (v : Vec F) (hv : v ≠ 0) :
    Function.Surjective (dotLinear v) := by
  classical
  have hi : ∃ i : Fin 3, v i ≠ 0 := by
    by_cases h : ∀ i, v i = 0
    · exact False.elim (hv (funext h))
    · exact not_forall.mp h
  obtain ⟨i, hi⟩ := hi
  intro z
  refine ⟨Pi.single i (z / v i), ?_⟩
  have hsingle (j : Fin 3) (a : F) : dot v (Pi.single j a) = v j * a := by
    fin_cases j <;> simp [dot]
  change dot v (Pi.single i (z / v i)) = z
  rw [hsingle]
  calc
    v i * (z / v i) = (v i * (v i)⁻¹) * z := by ring
    _ = z := by rw [mul_inv_cancel₀ hi, one_mul]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (hyperplane v) = 2 := by
  have h := (dotLinear v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (dotLinear_surjective v hv),
    finrank_top, Module.finrank_self, dotLinear_ker,
    Module.finrank_fin_fun] at h
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_line (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (line v) = 1 :=
  finrank_span_singleton hv

variable [FiniteDimensional (ZMod 2) F]

omit [CharP F 2] [FiniteDimensional (ZMod 2) F] in
theorem finrank_lineBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (lineBinary v) = Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (lineBinary v),
    ((line v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_line v hv, mul_one]

omit [CharP F 2] [FiniteDimensional (ZMod 2) F] in
theorem finrank_hyperplaneBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (hyperplaneBinary v) = 2 * Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (hyperplaneBinary v),
    ((hyperplane v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_hyperplane v hv,
    mul_comm]

/-- If the field has binary dimension `d`, every nonzero-generator block has
binary dimension `3d`, the dimension of its input/output alphabet. -/
theorem finrank_U (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = 3 * Module.finrank (ZMod 2) F := by
  rw [← (blockParametrization v).finrank_eq, Module.finrank_prod,
    finrank_lineBinary v hv, finrank_hyperplaneBinary v hv]
  omega

theorem finrank_U_eq_finrank_vec (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = Module.finrank (ZMod 2) (Vec F) := by
  rw [finrank_U v hv, ← Module.finrank_mul_finrank (ZMod 2) F (Vec F),
    Module.finrank_fin_fun, mul_comm]

end UniqueGamesTheorem.Quadratic

end

end OAI
