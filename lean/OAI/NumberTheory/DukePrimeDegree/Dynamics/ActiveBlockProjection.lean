import OAI.NumberTheory.DukePrimeDegree.Dynamics.VelocityCommutant

namespace OAI

/-!
# Local fixation of a nontrivial block projection

The commutant of the root directions can have a large part on singleton
coordinates. That part does not obstruct local fixation of a nontrivial
block projection: after subtracting the original projection it is an
idempotent tending to zero. A nonzero idempotent has norm at least one.
Thus this local step needs no hypothesis excluding singleton blocks.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Topology Matrix.Norms.Operator Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma matrix_idempotent_eq_zero_of_norm_lt_one {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M * M = M) (hn : ‖M‖ < 1) : M = 0 := by
  by_contra hne
  have hp : 0 < ‖M‖ := norm_pos_iff.mpr hne
  have hm : ‖M‖ ≤ ‖M‖ * ‖M‖ := by
    calc
      ‖M‖ = ‖M * M‖ := congrArg norm hM.symm
      _ ≤ ‖M‖ * ‖M‖ := norm_mul_le _ _
  nlinarith

lemma matrix_idempotent_eq_of_absorbs {n : ℕ}
    (M P : Matrix (Fin n) (Fin n) ℝ)
    (hM : M * M = M) (hP : P * P = P)
    (hMP : M * P = P) (hPM : P * M = P) (hn : ‖M - P‖ < 1) : M = P := by
  apply sub_eq_zero.mp
  apply matrix_idempotent_eq_zero_of_norm_lt_one _ ?_ hn
  calc
    (M - P) * (M - P) = M * M - M * P - P * M + P * P := by noncomm_ring
    _ = M - P := by rw [hM, hP, hMP, hPM]; abel

lemma commute_single_root_entries {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hM : Commute M (Matrix.single i j (1 : ℝ))) :
    (∀ a, a ≠ i → M a i = 0) ∧
      (∀ b, b ≠ j → M j b = 0) ∧ M i i = M j j := by
  refine ⟨?_, ?_, ?_⟩
  · intro a hai
    have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N a j) hM.eq
    simpa only [Matrix.mul_single_apply_same,
      Matrix.single_mul_apply_of_ne 1 i j a j hai M, mul_one] using he
  · intro b hbj
    have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i b) hM.eq
    simpa only [Matrix.mul_single_apply_of_ne 1 i j i b hbj M,
      Matrix.single_mul_apply_same, one_mul] using he.symm
  · have he := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N i j) hM.eq
    simpa only [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same,
      mul_one, one_mul] using he

lemma blockProjection_eq_diagonal {n : ℕ} (r : Setoid (Fin n)) (k : Fin n) :
    blockProjection r k = Matrix.diagonal (fun i => if r i k then (1 : ℝ) else 0) := by
  simp only [blockProjection, blockScalarAlgHom_apply, Quotient.eq]

/-- Commutation with the within-block root directions makes the action
on a nontrivial block scalar, even if singleton blocks are present. -/
theorem commutant_mul_nontrivial_blockProjection {n : ℕ}
    (r : Setoid (Fin n)) (k : Fin n) (hk : ∃ l, k ≠ l ∧ r k l)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, i ≠ j → r i j → Commute M (Matrix.single i j (1 : ℝ))) :
    M * blockProjection r k = M k k • blockProjection r k ∧
      blockProjection r k * M = M k k • blockProjection r k := by
  have hpartner (i : Fin n) (hi : r i k) : ∃ j, i ≠ j ∧ r i j := by
    obtain ⟨l, hkl, hrl⟩ := hk
    by_cases hik : i = k
    · subst i; exact ⟨l, hkl, hrl⟩
    · exact ⟨k, hik, hi⟩
  have hrow (i j : Fin n) (hi : r i k) (hij : i ≠ j) : M i j = 0 := by
    obtain ⟨l, hil, hrl⟩ := hpartner i hi
    exact (commute_single_root_entries M l i (hM l i hil.symm (r.symm hrl))).2.1 j hij.symm
  have hcol (i j : Fin n) (hj : r j k) (hij : i ≠ j) : M i j = 0 := by
    obtain ⟨l, hjl, hrl⟩ := hpartner j hj
    exact (commute_single_root_entries M j l (hM j l hjl hrl)).1 i hij
  have hdiag (i : Fin n) (hi : r i k) : M i i = M k k := by
    by_cases hik : i = k
    · subst i; rfl
    · exact (commute_single_root_entries M i k (hM i k hik hi)).2.2
  constructor
  · ext i j
    rw [blockProjection_eq_diagonal, Matrix.mul_diagonal, Matrix.smul_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : r i k
      · simp only [hi, ite_true, Matrix.diagonal_apply_eq, smul_eq_mul, mul_one, hdiag i hi]
      · simp only [hi, ite_false, Matrix.diagonal_apply_eq, smul_eq_mul, mul_zero]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hj : r j k
      · simp only [hj, ite_true, hcol i j hj hij, mul_one, smul_zero]
      · simp only [hj, ite_false, mul_zero, smul_zero]
  · ext i j
    rw [blockProjection_eq_diagonal, Matrix.diagonal_mul, Matrix.smul_apply]
    by_cases hij : i = j
    · subst j
      by_cases hi : r i k
      · simp only [hi, ite_true, Matrix.diagonal_apply_eq, smul_eq_mul, mul_one,
          one_mul, hdiag i hi]
      · simp only [hi, ite_false, Matrix.diagonal_apply_eq, smul_eq_mul, mul_zero, zero_mul]
    · rw [Matrix.diagonal_apply_ne _ hij]
      by_cases hi : r i k
      · simp only [hi, ite_true, hrow i j hi hij, one_mul, smul_zero]
      · simp only [hi, ite_false, zero_mul, smul_zero]

theorem commutant_idempotent_eq_blockProjection {n : ℕ}
    (r : Setoid (Fin n)) (k : Fin n) (hk : ∃ l, k ≠ l ∧ r k l)
    (M : Matrix (Fin n) (Fin n) ℝ) (hidem : M * M = M)
    (hcomm : ∀ i j, i ≠ j → r i j → Commute M (Matrix.single i j (1 : ℝ)))
    (hkne : M k k ≠ 0) (hn : ‖M - blockProjection r k‖ < 1) :
    M = blockProjection r k := by
  obtain ⟨hMP, hPM⟩ := commutant_mul_nontrivial_blockProjection r k hk M hcomm
  have hPkk : blockProjection r k k k = 1 := by
    rw [blockProjection_eq_diagonal, Matrix.diagonal_apply_eq]
    simp only [r.refl k, ite_true]
  have hsquare : M k k * M k k = M k k := by
    have he : M * (M * blockProjection r k) = M * blockProjection r k := by
      rw [← Matrix.mul_assoc, hidem]
    rw [hMP, Matrix.mul_smul, hMP, smul_smul] at he
    have hc := congrArg (fun N : Matrix (Fin n) (Fin n) ℝ => N k k) he
    simpa only [Matrix.smul_apply, smul_eq_mul, hPkk, mul_one] using hc
  have hone : M k k = 1 := by
    apply mul_left_cancel₀ hkne
    simpa only [mul_one] using hsquare
  apply matrix_idempotent_eq_of_absorbs M (blockProjection r k) hidem
    (blockProjection_mul_self r k) ?_ ?_ hn
  · simpa only [hone, one_smul] using hMP
  · simpa only [hone, one_smul] using hPM

/-- Every element sufficiently near the identity in the actual subgroup
fixes each specified nontrivial block projection. Singleton blocks are
allowed throughout this statement. -/
theorem nontrivial_blockProjection_fixed_near_identity {n : ℕ}
    (L : Subgroup (G n)) (r : Setoid (Fin n))
    (hroot : ∀ i j (hij : i ≠ j), r i j →
      ∀ t : ℝ, Matrix.SpecialLinearGroup.transvection hij t ∈ L)
    (hsupport : ∀ V ∈ matrixVelocitySpace L, ∀ i j, ¬r i j → V i j = 0)
    (k : Fin n) (hk : ∃ l, k ≠ l ∧ r k l) :
    {g : L | slMatrixConjugation g.val (blockProjection r k) = blockProjection r k} ∈
      𝓝 (1 : L) := by
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
  apply commutant_idempotent_eq_blockProjection r k hk (M g) ?_ ?_ hkg hg
  · change slMatrixConjugationHom g.val P * slMatrixConjugationHom g.val P = _
    rw [← map_mul, blockProjection_mul_self]
    rfl
  · intro i j hij hr
    have hE : Matrix.single i j (1 : ℝ) ∈ matrixVelocitySpace L :=
      ⟨fun t => Matrix.SpecialLinearGroup.transvection hij t,
        hroot i j hij hr,
        by simpa only [mul_one] using hasIdentityMatrixDerivative_rootCurve hij 1⟩
    have hback := slMatrixConjugation_mem_velocitySpace L (L.inv_mem g.property) hE
    have hcomm : Commute P (slMatrixConjugation g.val⁻¹ (Matrix.single i j (1 : ℝ))) :=
      ((commute_blockScalars_iff r _).mpr (hsupport _ hback) P (blockProjection_mem r k)).symm
    have he := hcomm.map (slMatrixConjugationHom g.val)
    change Commute (M g)
      (slMatrixConjugation g.val (slMatrixConjugation g.val⁻¹ (Matrix.single i j (1 : ℝ)))) at he
    simpa only [slMatrixConjugation_inverse] using he

end DukePrimeDegree

end

end OAI
