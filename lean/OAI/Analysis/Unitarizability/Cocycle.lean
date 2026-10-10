import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

def conjugate (U : G →* R) (g : G) (T : R) : R := U g * T * U g⁻¹

@[simp] theorem conjugate_one (U : G →* R) (T : R) : conjugate U 1 T = T := by
  simp [conjugate]

theorem conjugate_mul (U : G →* R) (g h : G) (T : R) :
    conjugate U (g * h) T = conjugate U g (conjugate U h T) := by
  simp [conjugate, map_mul, mul_assoc]

theorem conjugate_sub (U : G →* R) (g : G) (A B : R) :
    conjugate U g (A - B) = conjugate U g A - conjugate U g B := by
  simp [conjugate, mul_sub, sub_mul]

def coboundary (U : G →* R) (T : R) (g : G) : R := T - conjugate U g T

@[simp] theorem coboundary_one (U : G →* R) (T : R) : coboundary U T 1 = 0 := by
  simp [coboundary]

/-- The coboundary cocycle identity, before taking direct sums. -/
theorem coboundary_cocycle (U : G →* R) (T : R) (g h : G) :
    coboundary U T (g * h) = coboundary U T g + conjugate U g (coboundary U T h) := by
  simp only [coboundary, conjugate_mul, conjugate_sub]
  abel

theorem conjugate_eq_self_iff_commute (U : G →* R) (g : G) (T : R) :
    conjugate U g T = T ↔ Commute (U g) T := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hginv : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  constructor
  · intro h
    have hh := congrArg (fun x : R => x * U g) h
    change U g * T = T * U g
    simpa [conjugate, mul_assoc, hinv] using hh
  · intro h
    change U g * T * U g⁻¹ = T
    rw [h.eq, mul_assoc, hginv, mul_one]

/-- Comparing the two implementers gives the commutant element T - B. -/
theorem equal_coboundaries_iff_commute_sub (U : G →* R) (T B : R) (g : G) :
    coboundary U T g = coboundary U B g ↔ Commute (U g) (T - B) := by
  rw [← conjugate_eq_self_iff_commute, conjugate_sub]
  simp only [coboundary]
  constructor
  · intro h
    calc
      conjugate U g T - conjugate U g B =
          (T - (T - conjugate U g T)) - (B - (B - conjugate U g B)) := by abel
      _ = T - B := by rw [h]; abel
  · intro h
    calc
      T - conjugate U g T = B - conjugate U g B +
          ((T - B) - (conjugate U g T - conjugate U g B)) := by abel
      _ = B - conjugate U g B := by rw [h]; abel

/-- Algebraic upper triangular operator product, without any norm assertion. -/
def triangular (a b : R) : R × R → R × R :=
  fun x => (a * x.1 + b * a * x.2, a * x.2)

theorem triangular_cocycle_mul (U : G →* R) (D : G → R)
    (hD : ∀ g h, D (g * h) = D g + conjugate U g (D h))
    (g h : G) (x : R × R) :
    triangular (U g) (D g) (triangular (U h) (D h) x) =
      triangular (U (g * h)) (D (g * h)) x := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hinv_assoc (z : R) : U g⁻¹ * (U g * z) = z := by
    rw [← mul_assoc, hinv, one_mul]
  simp only [triangular, map_mul, hD, conjugate, Prod.mk.injEq]
  constructor
  · simp only [add_mul, mul_add, mul_assoc, hinv_assoc]
    abel
  · simp only [mul_assoc]

end Ring
end Dixmier

end OAI
