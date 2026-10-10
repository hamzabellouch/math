import OAI.NumberTheory.DukePrimeDegree.Dynamics.ActiveBlockProjection
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SingleBlockNormalization

namespace OAI

/-!
# Local preservation of one nontrivial root block

The other root blocks need not preserve the component measure. Only
the roots in the selected block and the vanishing of velocity entries
crossing its boundary are used. This is the local stabilizer statement
needed on a single-block ergodic component.
-/

noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Operator Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma blockProjection_singleBlock_eq {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S) :
    blockProjection (singleBlockSetoid S) k =
      Matrix.diagonal (fun i => if i ∈ S then (1 : ℝ) else 0) := by
  rw [blockProjection_eq_diagonal]
  congr 1
  funext i
  have he : singleBlockSetoid S i k ↔ i ∈ S := by
    change (i = k ∨ i ∈ S ∧ k ∈ S) ↔ i ∈ S
    constructor
    · rintro (rfl | hi)
      · exact hk
      · exact hi.1
    · exact fun hi => Or.inr ⟨hi, hk⟩
  simp only [he]

lemma commute_singleBlockProjection_of_cross_zero {n : ℕ}
    (S : Set (Fin n)) (k : Fin n) (hk : k ∈ S)
    (V : Matrix (Fin n) (Fin n) ℝ)
    (hV : ∀ i j, ¬(i ∈ S ↔ j ∈ S) → V i j = 0) :
    Commute (blockProjection (singleBlockSetoid S) k) V := by
  change _ * V = V * _
  rw [blockProjection_singleBlock_eq S k hk]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · simp only [hi, hj, ite_true, one_mul, mul_one]
  · have hz := hV i j (by simp only [hi, hj, true_iff, not_false_eq_true])
    simp only [hi, hj, ite_true, ite_false, hz, mul_zero]
  · have hz := hV i j (by simp only [hi, hj, iff_true, not_false_eq_true])
    simp only [hi, hj, ite_true, ite_false, hz, mul_zero, zero_mul]
  · simp only [hi, hj, ite_false, zero_mul, mul_zero]

theorem singleBlockProjection_fixed_near_identity {n : ℕ}
    (L : Subgroup (G n)) (S : Set (Fin n))
    (k l : Fin n) (hkl : k ≠ l) (hk : k ∈ S) (hl : l ∈ S)
    (hroot : ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j) (t : ℝ),
      Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hsupport : ∀ V ∈ matrixVelocitySpace L, ∀ i j,
      ¬(i ∈ S ↔ j ∈ S) → V i j = 0) :
    {g : L | slMatrixConjugation g.val (blockProjection (singleBlockSetoid S) k) =
      blockProjection (singleBlockSetoid S) k} ∈ 𝓝 (1 : L) := by
  let r := singleBlockSetoid S
  let P := blockProjection r k
  let M : L → Matrix (Fin n) (Fin n) ℝ := fun g => slMatrixConjugation g.val P
  have hcont : Continuous M := by unfold M slMatrixConjugation; fun_prop
  have hMone : M 1 = P := slMatrixConjugation_one P
  have hPkk : P k k = 1 := by
    dsimp only [P]
    rw [blockProjection_eq_diagonal, Matrix.diagonal_apply_eq]
    simp only [r.refl k, ite_true]
  have hsmall : {g : L | ‖M g - P‖ < 1} ∈ 𝓝 (1 : L) := by
    apply (isOpen_lt (hcont.sub continuous_const).norm continuous_const).mem_nhds
    change ‖M 1 - P‖ < 1
    simp only [hMone, sub_self, norm_zero, zero_lt_one]
  have hnz : {g : L | M g k k ≠ 0} ∈ 𝓝 (1 : L) := by
    apply (isOpen_ne_fun (hcont.matrix_elem k k) continuous_const).mem_nhds
    change M 1 k k ≠ 0
    rw [hMone, hPkk]
    exact one_ne_zero
  filter_upwards [hsmall, hnz] with g hg hkg
  apply commutant_idempotent_eq_blockProjection r k ⟨l, hkl, Or.inr ⟨hk, hl⟩⟩
    (M g) ?_ ?_ hkg hg
  · change slMatrixConjugationHom g.val P * slMatrixConjugationHom g.val P = _
    rw [← map_mul, blockProjection_mul_self]
    rfl
  · intro i j hij hr
    obtain ⟨hi, hj⟩ := (singleBlockSetoid_off_diagonal S hij).mp hr
    have hE : Matrix.single i j (1 : ℝ) ∈ matrixVelocitySpace L :=
      ⟨fun t => Matrix.SpecialLinearGroup.transvection hij t,
        hroot i hi j hj hij,
        by simpa only [mul_one] using hasIdentityMatrixDerivative_rootCurve hij 1⟩
    have hback := slMatrixConjugation_mem_velocitySpace L (L.inv_mem g.property) hE
    have hcomm := commute_singleBlockProjection_of_cross_zero S k hk _ (hsupport _ hback)
    have he := hcomm.map (slMatrixConjugationHom g.val)
    change Commute (M g)
      (slMatrixConjugation g.val (slMatrixConjugation g.val⁻¹ (Matrix.single i j (1 : ℝ)))) at he
    simpa only [slMatrixConjugation_inverse] using he

end DukePrimeDegree

end

end OAI
