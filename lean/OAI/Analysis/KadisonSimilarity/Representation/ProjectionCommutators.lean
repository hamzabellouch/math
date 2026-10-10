import OAI.Analysis.KadisonSimilarity.Representation.Amplification

namespace OAI

/-! The orthogonal block estimate used before the spectral step approximation. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open ContinuousLinearMap

/-- For a projection, the two off-diagonal blocks control its commutator by
their maximum. The proof uses orthogonal input and output decompositions. -/
theorem norm_commutator_projection_le (T e : H →L[ℂ] H)
    (hstar : star e = e) (hsq : e * e = e) {a : ℝ}
    (hleft : ‖(1 - e) * T * e‖ ≤ a) (hright : ‖e * T * (1 - e)‖ ≤ a) :
    ‖commutator T e‖ ≤ a := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hleft
  have he (ξ : H) : e (e ξ) = e ξ :=
    congrArg (fun R : H →L[ℂ] H => R ξ) hsq
  have hsym (ξ η : H) : inner ℂ (e ξ) η = inner ℂ ξ (e η) := by
    have hself : e.adjoint = e := hstar
    exact (ContinuousLinearMap.eq_adjoint_iff e e).mp hself.symm ξ η
  apply ContinuousLinearMap.opNorm_le_bound _ ha
  intro ξ
  let p : H := e ξ
  let q : H := ξ - e ξ
  let u : H := (1 - e) (T p)
  let v : H := e (T q)
  have heq : e q = 0 := by simp [q, he]
  have hep : e p = p := he ξ
  have heu : e u = 0 := by simp [u, he]
  have hpq : inner ℂ p q = 0 := by
    rw [show p = e ξ from rfl, hsym, heq, inner_zero_right]
  have huv : inner ℂ u v = 0 := by
    rw [show v = e (T q) from rfl, ← hsym, heu, inner_zero_left]
  have hpqnorm : ‖ξ‖ ^ 2 = ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p q hpq
    have hpqsum : p + q = ξ := by dsimp [p, q]; abel
    simpa only [hpqsum, ← pow_two] using h
  have huvnorm : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (-v) (by
      simpa using huv)
    simpa only [sub_eq_add_neg, norm_neg, ← pow_two] using h
  have hcomm : (commutator T e) ξ = u - v := by
    simp only [commutator, sub_apply, u, v, q, p, map_sub]
    abel
  have hu : ‖u‖ ≤ a * ‖p‖ := by
    calc
      ‖u‖ = ‖((1 - e) * T * e) p‖ := by simp [u, hep]
      _ ≤ ‖(1 - e) * T * e‖ * ‖p‖ := le_opNorm _ _
      _ ≤ a * ‖p‖ := mul_le_mul_of_nonneg_right hleft (norm_nonneg p)
  have hv : ‖v‖ ≤ a * ‖q‖ := by
    calc
      ‖v‖ = ‖(e * T * (1 - e)) q‖ := by simp [v, heq]
      _ ≤ ‖e * T * (1 - e)‖ * ‖q‖ := le_opNorm _ _
      _ ≤ a * ‖q‖ := mul_le_mul_of_nonneg_right hright (norm_nonneg q)
  have hsqbound : ‖(commutator T e) ξ‖ ^ 2 ≤ (a * ‖ξ‖) ^ 2 := by
    calc
      ‖(commutator T e) ξ‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by rw [hcomm, huvnorm]
      _ ≤ (a * ‖p‖) ^ 2 + (a * ‖q‖) ^ 2 :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg u) hu 2)
          (pow_le_pow_left₀ (norm_nonneg v) hv 2)
      _ = a ^ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by ring
      _ = (a * ‖ξ‖) ^ 2 := by rw [← hpqnorm]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg ξ))).mp hsqbound

/-- Complement of a commutant projection, as a commutant projection. -/
def complementProjection {M : VonNeumannAlgebra H} (e : CommutantProjection M) :
    CommutantProjection M :=
  ⟨1 - e.val, M.commutant.sub_mem M.commutant.one_mem e.property.1,
    by simp [e.property.2.1], by
      calc
        (1 - e.val) * (1 - e.val) = 1 - e.val - e.val + e.val * e.val := by noncomm_ring
        _ = 1 - e.val := by rw [e.property.2.2]; abel⟩

private theorem offDiagonalValue_le_norm (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (e : CommutantProjection M) :
    ‖(1 - e.val) * T * e.val‖ ≤ ‖T‖ := by
  have he := norm_projection_le_one e.val e.property.2.1 e.property.2.2
  have he' := norm_one_sub_projection_le_one e.val e.property.2.1 e.property.2.2
  calc
    ‖(1 - e.val) * T * e.val‖ ≤ (‖1 - e.val‖ * ‖T‖) * ‖e.val‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg e.val))
    _ ≤ (1 * ‖T‖) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right he' (norm_nonneg T)) he
        (norm_nonneg e.val) (by positivity)
    _ = ‖T‖ := by ring

/-- Each defining off-diagonal block is bounded by the distance seminorm. -/
theorem norm_offDiagonal_le (M : VonNeumannAlgebra H) (T : H →L[ℂ] H)
    (e : CommutantProjection M) :
    ‖(1 - e.val) * T * e.val‖ ≤ offDiagonalSeminorm M T := by
  apply le_csSup
  · refine ⟨‖T‖, ?_⟩
    rintro r ⟨f, rfl⟩
    exact offDiagonalValue_le_norm M T f
  · exact ⟨e, rfl⟩

/-- The off-diagonal distance seminorm is nonnegative. -/
theorem offDiagonalSeminorm_nonneg (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) :
    0 ≤ offDiagonalSeminorm M T := by
  let e₀ : CommutantProjection M := ⟨0, by simp⟩
  exact (norm_nonneg _).trans (norm_offDiagonal_le M T e₀)

/-- The first estimate in the manuscript's hyperreflexivity proof. -/
theorem norm_commutator_projection_le_offDiagonal (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H) (e : CommutantProjection M) :
    ‖commutator T e.val‖ ≤ offDiagonalSeminorm M T := by
  apply norm_commutator_projection_le T e.val e.property.2.1 e.property.2.2
  · exact norm_offDiagonal_le M T e
  · have h := norm_offDiagonal_le M T (complementProjection e)
    simpa only [complementProjection, sub_sub_cancel] using h

/-- Real/imaginary decomposition reduces the scalar estimate to a bound on
selfadjoint elements. -/
theorem scalarCommutatorNorm_le_four_of_selfAdjoint (M : VonNeumannAlgebra H)
    (T : H →L[ℂ] H)
    (selfAdjointBound : ∀ A : H →L[ℂ] H, A ∈ M.commutant → star A = A →
      ‖commutator T A‖ ≤ 2 * offDiagonalSeminorm M T * ‖A‖) :
    scalarCommutatorNorm M.commutant T ≤ 4 * offDiagonalSeminorm M T := by
  have hα := offDiagonalSeminorm_nonneg M T
  apply (scalarCommutatorNorm_le_iff M.commutant T (by positivity)).mpr
  intro A hA
  have hAstar : star A ∈ M.commutant := star_mem hA
  let b : H →L[ℂ] H := realPart A
  let c : H →L[ℂ] H := imaginaryPart A
  have hb : b ∈ M.commutant := by
    dsimp [b]
    rw [realPart_apply_coe, ← Complex.coe_smul]
    exact M.commutant.toStarSubalgebra.smul_mem
      (M.commutant.add_mem hA hAstar) _
  have hc : c ∈ M.commutant := by
    dsimp [c]
    rw [imaginaryPart_apply_coe, ← Complex.coe_smul]
    exact M.commutant.toStarSubalgebra.smul_mem
      (M.commutant.toStarSubalgebra.smul_mem
        (M.commutant.sub_mem hA hAstar) _) _
  have hbself : star b = b := (realPart A).property
  have hcself : star c = c := (imaginaryPart A).property
  have hsplit : commutator T A = commutator T b + Complex.I • commutator T c := by
    change innerDerivation T A = innerDerivation T b + Complex.I • innerDerivation T c
    rw [← realPart_add_I_smul_imaginaryPart A]
    simp only [map_add, map_smul, b, c]
  calc
    ‖commutator T A‖ ≤ ‖commutator T b‖ + ‖commutator T c‖ := by
      rw [hsplit]
      simpa only [norm_smul, Complex.norm_I, one_mul] using
        norm_add_le (commutator T b) (Complex.I • commutator T c)
    _ ≤ 2 * offDiagonalSeminorm M T * ‖b‖ + 2 * offDiagonalSeminorm M T * ‖c‖ :=
      add_le_add (selfAdjointBound b hb hbself) (selfAdjointBound c hc hcself)
    _ ≤ 2 * offDiagonalSeminorm M T * ‖A‖ + 2 * offDiagonalSeminorm M T * ‖A‖ := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (realPart.norm_le A) (by positivity)
      · exact mul_le_mul_of_nonneg_left (imaginaryPart.norm_le A) (by positivity)
    _ = 4 * offDiagonalSeminorm M T * ‖A‖ := by ring

end KadisonSimilarity

end

end OAI
