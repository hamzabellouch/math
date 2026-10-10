import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactLieLaws
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteLieNorm

namespace OAI

/-! # The actual Lie law in a chosen basis

Transport the original bracket to Euclidean coordinates, retaining its exact
word identities. A bound on basis structure constants gives a bound in the
finite-dimensional parameter space used for normalized-law compactness.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}
  (b : Basis (Fin n) ℝ L)

/-- Coordinate transport of the bracket, initially as a bilinear map. -/
def basisBracketLinear : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x :=
    { toFun y := b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm y⁆
      map_add' := by intro y z; simp only [map_add, lie_add]
      map_smul' := by intro c y; simp only [map_smul, lie_smul, RingHom.id_apply] }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change b.equivFun ⁅b.equivFun.symm (x + y), b.equivFun.symm z⁆ =
      b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm z⁆ +
        b.equivFun ⁅b.equivFun.symm y, b.equivFun.symm z⁆
    rw [map_add, add_lie, map_add]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change b.equivFun ⁅b.equivFun.symm (c • x), b.equivFun.symm y⁆ =
      c • b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm y⁆
    rw [map_smul, smul_lie, map_smul]

/-- The same coordinate bracket in the normed space of continuous bilinear maps. -/
def basisBracket : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (((LinearMap.toContinuousLinearMap :
    ((Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ≃ₗ[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ))).toLinearMap).comp
      (basisBracketLinear b)).toContinuousLinearMap

@[simp] theorem basisBracket_apply (x y : Fin n → ℝ) :
    basisBracket b x y = b.equivFun ⁅b.equivFun.symm x, b.equivFun.symm y⁆ := rfl

/-- The transported operation is a genuine Lie bracket, not only a bounded
bilinear operation. -/
theorem isLieBracket_basisBracket : IsLieBracket (basisBracket b) := by
  constructor
  · intro x
    simp
  · intro x y z
    simp only [basisBracket_apply, LinearEquiv.symm_apply_apply]
    rw [← map_add, ← leibniz_lie]

/-- Word evaluation commutes exactly with the coordinate transport. -/
theorem evalBilinearWord_basisBracket {I : Type*} (X : I → L) (w : FreeMagma I) :
    evalBilinearWord (basisBracket b) (fun i => b.equivFun (X i)) w =
      b.equivFun (evalBracketWord X w) := by
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a c ha hc =>
    simp only [evalBilinearWord, ha, hc, basisBracket_apply, LinearEquiv.symm_apply_apply,
      evalBracketWord]


/-- The structure-constant estimate controls the norm of the actual law
in the fixed coordinate parameter space. -/
theorem norm_basisBracket_le {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) :
    ‖basisBracket b‖ ≤ (n : ℝ) ^ 2 * C := by
  apply norm_bilinear_le_of_bound (basisBracket b) (by positivity)
  intro x y
  have h := norm_basis_bracket_le b hC hb (b.equivFun.symm x) (b.equivFun.symm y)
  simpa only [basisBracket_apply, LinearEquiv.apply_symm_apply, Fintype.card_fin] using h

end PolycyclicRecognition

end

end OAI
