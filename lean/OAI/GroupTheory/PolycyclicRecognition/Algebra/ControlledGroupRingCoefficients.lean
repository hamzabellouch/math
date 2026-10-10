import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomogeneousCochainCoordinates

namespace OAI

/-! # Recovering group-ring coefficients from controlled scalar cochains

Diagonal translation turns a scalar cochain into a finitely supported
coefficient function. The covariance formula is the actual left regular
action needed to identify these cochains with the standard group resolution.
-/

noncomputable section
namespace PolycyclicRecognition
open Function
variable {G R : Type*} [Group G] [CommRing R] {n : ℕ}

/-- Only finitely many diagonal translates of a fixed tuple can have a
nonzero value under a controlled cochain. -/
theorem finite_support_diagonal_translate (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) :
    (support (fun h => c (fun i => h⁻¹ * x i))).Finite := by
  let S : Set G := Set.range (fun p : Fin (n + 1) × Fin (n + 1) => (x p.1)⁻¹ * x p.2)
  have hS : S.Finite := Set.finite_range _
  have hi : Injective (fun h : G => fun i : Fin (n + 1) => h⁻¹ * x i) := by
    intro a b hab
    exact inv_injective (mul_right_cancel (congrFun hab 0))
  apply ((c.property S hS).preimage hi.injOn).subset
  intro h hh
  refine ⟨?_, hh⟩
  intro i j
  refine ⟨(i, j), ?_⟩
  simp [mul_assoc]

/-- The group-ring value of a scalar homogeneous cochain. -/
def controlledGroupRingValue (c : controlledCochains R G n) (x : Fin (n + 1) → G) :
    G →₀ R := Finsupp.ofSupportFinite (fun h => c (fun i => h⁻¹ * x i))
      (finite_support_diagonal_translate c x)

@[simp] theorem controlledGroupRingValue_apply (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (h : G) :
    controlledGroupRingValue c x h = c (fun i => h⁻¹ * x i) := rfl

@[simp] theorem controlledGroupRingValue_one (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) : controlledGroupRingValue c x 1 = c x := by
  simp

/-- Equivariance is forced by diagonal translation; the group action is
not inserted as an assumption on the coarse map. -/
theorem controlledGroupRingValue_covariance (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (g h : G) :
    controlledGroupRingValue c (fun i => g * x i) h =
      controlledGroupRingValue c x (g⁻¹ * h) := by
  simp [mul_assoc]

/-- Recovering the coefficient at the identity recovers the scalar cochain. -/
theorem controlledGroupRingValue_injective :
    Injective (fun c : controlledCochains R G n => controlledGroupRingValue c) := by
  intro c d h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun F => F x 1) h
  simpa using hx

end PolycyclicRecognition

end

end OAI
