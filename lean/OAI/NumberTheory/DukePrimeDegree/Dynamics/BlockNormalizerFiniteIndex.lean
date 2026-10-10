import OAI.NumberTheory.DukePrimeDegree.Dynamics.BlockGroupNormalizer
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Finite.Perm

namespace OAI

/-!
# The finite quotient of the block normalizer

Conjugation acts on the finite set of idempotents in the block-scalar
algebra. The kernel is precisely the block matrix group. Thus the latter
has finite index in the full normalizer, including its disconnected part.
-/

noncomputable section
open Matrix Set
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

def BlockIdempotent {n : ℕ} (r : Setoid (Fin n)) :=
  {M : Matrix (Fin n) (Fin n) ℝ // M ∈ blockScalarAlgebra r ∧ M * M = M}

lemma blockIdempotent_diagonal {n : ℕ} (r : Setoid (Fin n)) (e : BlockIdempotent r) :
    e.val = Matrix.diagonal (fun i => e.val i i) :=
  ((mem_blockScalarAlgebra_iff r e.val).mp e.property.1).1

lemma blockIdempotent_entry_zero_or_one {n : ℕ} (r : Setoid (Fin n))
    (e : BlockIdempotent r) (i : Fin n) : e.val i i = 0 ∨ e.val i i = 1 := by
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) e.property.2
  rw [blockIdempotent_diagonal r e, Matrix.diagonal_mul_diagonal] at he
  simp only [Matrix.diagonal_apply_eq] at he
  have hfactor : e.val i i * (e.val i i - 1) = 0 := by nlinarith [he]
  exact (mul_eq_zero.mp hfactor).imp_right sub_eq_zero.mp

instance blockIdempotentFinite {n : ℕ} (r : Setoid (Fin n)) : Finite (BlockIdempotent r) := by
  let f : BlockIdempotent r → Fin n → Bool := fun e i => decide (e.val i i = 1)
  apply Finite.of_injective f
  intro e e' he
  apply Subtype.ext
  rw [blockIdempotent_diagonal r e, blockIdempotent_diagonal r e']
  congr 1
  funext i
  have hi := congrFun he i
  change decide (e.val i i = 1) = decide (e'.val i i = 1) at hi
  rcases blockIdempotent_entry_zero_or_one r e i with h | h <;>
    rcases blockIdempotent_entry_zero_or_one r e' i with h' | h' <;> simp_all

lemma slMatrixConjugation_eq_self_of_mem_blockMatrixGroup {n : ℕ}
    (r : Setoid (Fin n)) (g : G n) (hg : g ∈ blockMatrixGroup r)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ blockScalarAlgebra r) :
    slMatrixConjugation g M = M := by
  obtain ⟨hD, hc⟩ := (mem_blockScalarAlgebra_iff r M).mp hM
  rw [hD]
  exact hg _ hc

lemma blockMatrixGroup_le_scalarNormalizer {n : ℕ} (r : Setoid (Fin n)) :
    blockMatrixGroup r ≤ blockScalarNormalizer r := by
  intro g hg M
  constructor
  · intro hM
    have he := slMatrixConjugation_eq_self_of_mem_blockMatrixGroup r g⁻¹
      ((blockMatrixGroup r).inv_mem hg) _ hM
    rw [← slMatrixConjugation_mul, mul_inv_cancel, slMatrixConjugation_one] at he
    exact he.symm ▸ hM
  · intro hM
    rw [slMatrixConjugation_eq_self_of_mem_blockMatrixGroup r g hg M hM]
    exact hM

lemma mem_blockMatrixGroup_of_fixes_blockProjection {n : ℕ}
    (r : Setoid (Fin n)) (g : G n)
    (hfix : ∀ k, slMatrixConjugation g (blockProjection r k) = blockProjection r k) :
    g ∈ blockMatrixGroup r := by
  have hzero : ∀ i j, ¬ r i j → g.val i j = 0 := by
    intro i j hij
    have he := ((slMatrixConjugation_eq_self_iff _ _).mp (hfix i)).eq
    have hc := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he
    have hq : Quotient.mk r j ≠ Quotient.mk r i := by
      intro heq
      exact hij (r.symm (Quotient.exact heq))
    simpa [blockProjection, Matrix.diagonal_mul, Matrix.mul_diagonal, hq] using hc
  have hcomm := (commute_blockScalars_iff r g.val).mpr hzero
  intro c hc
  apply slMatrixConjugation_eq_self
  apply Commute.symm
  apply hcomm
  refine (mem_blockScalarAlgebra_iff r _).mpr ⟨by simp, ?_⟩
  intro i j hij
  simpa only [Matrix.diagonal_apply_eq] using hc i j hij

def blockIdempotentConjugate {n : ℕ} (r : Setoid (Fin n))
    (g : blockScalarNormalizer r) (e : BlockIdempotent r) : BlockIdempotent r :=
  ⟨slMatrixConjugation g.val⁻¹ e.val,
    ((g⁻¹).property _).mpr e.property.1, by
      change slMatrixConjugationHom g.val⁻¹ e.val *
        slMatrixConjugationHom g.val⁻¹ e.val = _
      rw [← map_mul, e.property.2]
      rfl⟩

instance blockIdempotentMulAction {n : ℕ} (r : Setoid (Fin n)) :
    MulAction (blockScalarNormalizer r) (BlockIdempotent r) where
  smul := blockIdempotentConjugate r
  one_smul e := by
    apply Subtype.ext
    change slMatrixConjugation (1 : G n)⁻¹ e.val = e.val
    rw [inv_one, slMatrixConjugation_one]
  mul_smul g h e := by
    apply Subtype.ext
    change slMatrixConjugation (g.val * h.val)⁻¹ e.val =
      slMatrixConjugation g.val⁻¹ (slMatrixConjugation h.val⁻¹ e.val)
    rw [_root_.mul_inv_rev, slMatrixConjugation_mul]

def blockNormalizerPermutation {n : ℕ} (r : Setoid (Fin n)) :
    blockScalarNormalizer r →* Equiv.Perm (BlockIdempotent r) :=
  MulAction.toPermHom _ _

lemma blockNormalizerPermutation_ker {n : ℕ} (r : Setoid (Fin n)) :
    (blockNormalizerPermutation r).ker =
      (blockMatrixGroup r).comap (blockScalarNormalizer r).subtype := by
  ext g
  change blockNormalizerPermutation r g = 1 ↔ g.val ∈ blockMatrixGroup r
  constructor
  · intro hg
    have hfix (k : Fin n) : slMatrixConjugation g.val⁻¹ (blockProjection r k) =
        blockProjection r k := by
      let e : BlockIdempotent r := ⟨blockProjection r k,
        blockProjection_mem r k, blockProjection_mul_self r k⟩
      have he := congrArg (fun p : Equiv.Perm (BlockIdempotent r) => (p e).val) hg
      exact he
    have hi := mem_blockMatrixGroup_of_fixes_blockProjection r g.val⁻¹ hfix
    simpa only [inv_inv] using (blockMatrixGroup r).inv_mem hi
  · intro hg
    apply Equiv.ext
    intro e
    apply Subtype.ext
    exact slMatrixConjugation_eq_self_of_mem_blockMatrixGroup r g.val⁻¹
      ((blockMatrixGroup r).inv_mem hg) e.val e.property.1

/-- Only finitely many block-group cosets occur in the full algebra normalizer. -/
theorem blockMatrixGroup_finiteIndex_in_scalarNormalizer {n : ℕ} (r : Setoid (Fin n)) :
    ((blockMatrixGroup r).comap (blockScalarNormalizer r).subtype).FiniteIndex := by
  rw [← blockNormalizerPermutation_ker r]
  infer_instance

theorem finite_blockNormalizer_quotient {n : ℕ} (r : Setoid (Fin n)) :
    Finite (blockScalarNormalizer r ⧸
      (blockMatrixGroup r).comap (blockScalarNormalizer r).subtype) := by
  let := blockMatrixGroup_finiteIndex_in_scalarNormalizer r
  infer_instance

end DukePrimeDegree

end

end OAI
