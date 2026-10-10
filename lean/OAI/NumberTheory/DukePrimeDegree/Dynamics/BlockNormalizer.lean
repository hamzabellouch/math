import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockOrbit
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.Subgroup

namespace OAI

/-!
# The connected normalizer of the block algebra

Conjugation permutes the primitive block projections. In a connected
family starting at the identity these projections cannot move, since
their diagonal coordinates remain idempotents. Consequently the identity
component of the block-algebra normalizer preserves every block.
-/

noncomputable section
open Matrix Set
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def blockProjection {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  blockScalarAlgHom r (fun q => if q = Quotient.mk r k then 1 else 0)

lemma blockProjection_mem {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    blockProjection r k ∈ blockScalarAlgebra r := ⟨_, rfl⟩

lemma blockProjection_mul_self {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    blockProjection r k * blockProjection r k = blockProjection r k := by
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  dsimp only
  split_ifs <;> norm_num

private lemma continuous_idempotent_constant {T : Type*} [TopologicalSpace T]
    [PreconnectedSpace T] (f : T → ℝ) (hf : Continuous f)
    (hid : ∀ x, f x * f x = f x) (x y : T) : f x = f y := by
  have hvals : Set.MapsTo f Set.univ ({0, 1} : Set ℝ) := by
    intro z _
    have hfactor : f z * (f z - 1) = 0 := by nlinarith [hid z]
    rcases mul_eq_zero.mp hfactor with h | h
    · simp [h]
    · have he : f z = 1 := sub_eq_zero.mp h
      simp [he]
  exact isPreconnected_univ.constant_of_mapsTo (Set.toFinite _).isDiscrete
    hf.continuousOn hvals (Set.mem_univ x) (Set.mem_univ y)

/-- The concrete normalizer of the real block-scalar matrix algebra. -/
def blockScalarNormalizer {n : ℕ} (r : Setoid (Fin n)) : Subgroup (G n) where
  carrier := {g | ∀ M : Matrix (Fin n) (Fin n) ℝ,
    slMatrixConjugation g M ∈ blockScalarAlgebra r ↔ M ∈ blockScalarAlgebra r}
  one_mem' := by intro M; rw [slMatrixConjugation_one]
  mul_mem' := by
    intro g h hg hh M
    rw [slMatrixConjugation_mul, hh, hg]
  inv_mem' := by
    intro g hg M
    have he := hg (slMatrixConjugation g⁻¹ M)
    rw [slMatrixConjugation_inverse] at he
    exact he.symm

/-- A connected family of normalizer matrices through the identity
fixes each block projection individually. -/
theorem connected_normalizer_fixes_blockProjection {n : ℕ}
    (r : Setoid (Fin n)) {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (f : T → G n) (hf : Continuous f) (t₀ : T) (h₀ : f t₀ = 1)
    (hnorm : ∀ t, f t ∈ blockScalarNormalizer r) (t : T) (k : Fin n) :
    slMatrixConjugation (f t) (blockProjection r k) = blockProjection r k := by
  let F : T → Matrix (Fin n) (Fin n) ℝ :=
    fun s => slMatrixConjugation (f s) (blockProjection r k)
  have hF : Continuous F := by unfold F slMatrixConjugation; fun_prop
  have hD (s : T) : F s = Matrix.diagonal (fun i => F s i i) :=
    ((mem_blockScalarAlgebra_iff r _).mp
      ((hnorm s _).mpr (blockProjection_mem r k))).1
  have hsq (s : T) : F s * F s = F s := by
    change slMatrixConjugationHom (f s) (blockProjection r k) *
      slMatrixConjugationHom (f s) (blockProjection r k) = _
    rw [← map_mul, blockProjection_mul_self]
    rfl
  have hi (i : Fin n) (s : T) : F s i i * F s i i = F s i i := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) (hsq s)
    rw [hD s, Matrix.diagonal_mul_diagonal] at he
    simpa only [Matrix.diagonal_apply_eq] using he
  have hconst (i : Fin n) : F t i i = F t₀ i i :=
    continuous_idempotent_constant (fun s => F s i i) (hF.matrix_elem i i) (hi i) t t₀
  have hF₀ : F t₀ = blockProjection r k := by
    change slMatrixConjugation (f t₀) (blockProjection r k) = _
    rw [h₀, slMatrixConjugation_one]
  change F t = _
  rw [hD t, ← hF₀, hD t₀]
  congr 1
  funext i
  exact hconst i

lemma slMatrixConjugation_eq_self_iff {n : ℕ} (g : G n)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    slMatrixConjugation g M = M ↔ Commute M g.val := by
  constructor
  · intro h
    have he := congrArg (fun A => g.val * A) h
    have hg : g.val * g⁻¹.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
    change M * g.val = g.val * M
    simpa only [slMatrixConjugation, ← mul_assoc, hg, one_mul] using he
  · exact slMatrixConjugation_eq_self g M

/-- Every matrix in such a connected family preserves each coordinate
block. This is the connected part of the normalizer calculation. -/
theorem connected_normalizer_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (f : T → G n) (hf : Continuous f) (t₀ : T) (h₀ : f t₀ = 1)
    (hnorm : ∀ t, f t ∈ blockScalarNormalizer r) (t : T) :
    f t ∈ blockMatrixGroup r := by
  have hzero : ∀ i j, ¬ r i j → (f t).val i j = 0 := by
    intro i j hij
    have he := ((slMatrixConjugation_eq_self_iff _ _).mp
      (connected_normalizer_fixes_blockProjection r f hf t₀ h₀ hnorm t i)).eq
    have hc := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he
    have hq : Quotient.mk r j ≠ Quotient.mk r i := by
      intro heq
      exact hij (r.symm (Quotient.exact heq))
    simpa [blockProjection, Matrix.diagonal_mul, Matrix.mul_diagonal, hq] using hc
  have hcomm := (commute_blockScalars_iff r (f t).val).mpr hzero
  intro c hc
  apply slMatrixConjugation_eq_self
  apply Commute.symm
  apply hcomm
  refine (mem_blockScalarAlgebra_iff r _).mpr ⟨by simp, ?_⟩
  intro i j hij
  simpa only [Matrix.diagonal_apply_eq] using hc i j hij

/-- The identity component of the block-algebra normalizer is contained
in the actual block-diagonal matrix subgroup. -/
theorem blockScalarNormalizer_identityComponent_le {n : ℕ}
    (r : Setoid (Fin n))
    (g : Subgroup.connectedComponentOfOne (blockScalarNormalizer r)) :
    g.val.val ∈ blockMatrixGroup r := by
  let T := Subgroup.connectedComponentOfOne (blockScalarNormalizer r)
  let : PreconnectedSpace T := Subtype.preconnectedSpace
    isConnected_connectedComponent.isPreconnected
  let f : T → G n := fun h => h.val.val
  apply connected_normalizer_mem_blockMatrixGroup r f (by unfold f; fun_prop) 1 (by rfl)
  intro t
  exact t.val.property

end DukePrimeDegree

end

end OAI
