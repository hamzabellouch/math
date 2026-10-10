import Mathlib.LinearAlgebra.BilinearForm.Properties
import OAI.Computability.UniqueGames.Quadratic.AlignmentCertificateLemmas
import OAI.Computability.UniqueGames.Quadratic.Block

namespace OAI

section

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem dot_add_first (x y z : Vec F) :
    dot (x + y) z = dot x z + dot y z := by
  simp only [dot, Pi.add_apply]
  ring

/-- The trace dot product, as an actual binary bilinear form. -/
def traceDotForm : LinearMap.BilinForm (ZMod 2) (Vec F) where
  toFun z :=
    { toFun := fun y => traceBinary (dot z y)
      map_add' := by
        intro x y
        rw [dot_add_right, map_add]
      map_smul' := by
        intro c y
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hc with rfl | rfl <;> simp }
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro y
    change traceBinary (dot (z + w) y) =
      traceBinary (dot z y) + traceBinary (dot w y)
    rw [dot_add_first, map_add]
  map_smul' := by
    intro c z
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl <;> ext y <;> simp

omit [Finite F] in
@[simp] theorem traceDotForm_apply (z y : Vec F) :
    traceDotForm z y = traceBinary (dot z y) := rfl

/-- Nondegeneracy holds coordinate by coordinate over the finite field. -/
theorem traceDotForm_nondegenerate :
    (traceDotForm (F := F)).Nondegenerate := by
  constructor
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot z (Pi.single i t) = t * z i := by
      fin_cases i <;> simp [dot, mul_comm]
    simpa only [traceDotForm_apply, hd] using h
  · intro z hz
    ext i
    apply (trace_mul_vanish_iff (z i)).mp
    intro t
    have h := hz (Pi.single i t)
    have hd : dot (Pi.single i t) z = t * z i := by
      fin_cases i <;> simp [dot]
    simpa only [traceDotForm_apply, hd] using h

/-- The exact binary trace-pairing identification. -/
def traceDualEquiv : Vec F ≃ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2) :=
  traceDotForm.toDual traceDotForm_nondegenerate

@[simp] theorem traceDualEquiv_apply (z y : Vec F) :
    traceDualEquiv z y = traceBinary (dot z y) := rfl

@[simp] theorem traceDualEquiv_symm_apply
    (γ : Vec F →ₗ[ZMod 2] ZMod 2) (y : Vec F) :
    traceBinary (dot (traceDualEquiv.symm γ) y) = γ y := by
  change traceDualEquiv (traceDualEquiv.symm γ) y = γ y
  rw [LinearEquiv.apply_symm_apply]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Taking trace coordinates preserves linear dependence on the family index. -/
def representTraceFamily (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) :
    W →ₗ[ZMod 2] Vec F :=
  traceDualEquiv.symm.toLinearMap.comp γ

theorem representTraceFamily_spec
    (γ : W →ₗ[ZMod 2] (Vec F →ₗ[ZMod 2] ZMod 2)) (z : W) (y : Vec F) :
    traceBinary (dot (representTraceFamily γ z) y) = γ z y :=
  traceDualEquiv_symm_apply (γ z) y

end

end UniqueGamesTheorem.Quadratic

end

end OAI
