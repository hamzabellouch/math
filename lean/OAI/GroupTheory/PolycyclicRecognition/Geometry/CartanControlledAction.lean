import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualConjugation

namespace OAI

/-! # Cartan actions whose heights stay in a template

The normalized width of a root controls every exponential whose exponent is
below that width. Consequently a Cartan action with height in the scaled
template sends a fixed coordinate box into the template box with polynomial
loss in its Cartan logarithm. This is the increment estimate for controlled
paths.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped BigOperators Manifold

private theorem norm_map_between_bases_le
    {V I J : Type*} [AddCommGroup V] [Module ℝ V] [Fintype I] [Fintype J]
    (a : Basis I ℝ V) (b : Basis J ℝ V) (F : V →ₗ[ℝ] V) {K : ℝ}
    (hF : ∀ i, ‖b.equivFun (F (a i))‖ ≤ K) (v : V) :
    ‖b.equivFun (F v)‖ ≤ (Fintype.card I : ℝ) * K * ‖a.equivFun v‖ := by
  conv_lhs => rw [← a.sum_repr v]
  rw [map_sum, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    (∑ i, ‖b.equivFun (F (a.repr v i • a i))‖) ≤
        ∑ _i : I, ‖a.equivFun v‖ * K := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (norm_le_pi_norm (a.equivFun v) i) (hF i)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {n : ℕ} (T : TriangularAdjoint L n)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- Any smaller root exponent satisfies the normalized width estimate. -/
theorem norm_scaled_root_le_of_exponent_le
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (i : Fin M.letterCount) (v : cartanRootIdeal H) (hv : (v : L) ∈ rootSpace H (M.weight i))
    {r t : ℝ} (hr : 0 ≤ r)
    (ht : t ≤ r * (M.supportIn T hunimod eW).weightSupport E i) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun (Real.exp t • v)‖ ≤
      ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun v‖ := by
  let s := r * (M.supportIn T hunimod eW).weightSupport E i
  have he : Real.exp t • v = Real.exp (t - s) • (Real.exp s • v) := by
    rw [smul_smul, ← Real.exp_add, sub_add_cancel]
  rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (t - s) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr ht)
  exact (mul_le_of_le_one_left (norm_nonneg _) hexp).trans
    (M.norm_scaled_root_le T hunimod eW hE hne β i v hv hr)

/-- Height containment absorbs the entire scalar part of each letter image. -/
theorem norm_adjoint_letter_le
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    {r : ℝ} (hr : 0 ≤ r) (h : H) (w : W) (hw : w ∈ E)
    (hh : eW (heightProjection T.character (h : L)) = r • w) (i : Fin M.letterCount) :
    ‖(M.boxBasis T hunimod eW E β r).equivFun
      (cartanIdealAdjointAutomorphism T H h (M.letter i))‖ ≤
    ‖(WordBasisSelections.basis M.letter M.wordList β).equivFun
      (cartanIdealResidualAutomorphism T H h (M.letter i))‖ := by
  have hv := cartanIdealResidualAutomorphism_root_mem T H h (M.weight i)
    (M.letter i) (M.letter_root i)
  have he : cartanIdealAdjointAutomorphism T H h (M.letter i) =
      Real.exp (M.weight i h) • cartanIdealResidualAutomorphism T H h (M.letter i) := by
    apply Subtype.ext
    exact cartanWeightScale_apply_root T H h (M.weight i) hv
  rw [he]
  apply M.norm_scaled_root_le_of_exponent_le T hunimod eW hE hne β i _ hv hr
  have hweight : M.weight i h = r * (M.supportIn T hunimod eW).weight i w := by
    have heq := congrArg ((M.supportIn T hunimod eW).weight i) hh
    simpa only [supportIn, SupportDatum.transport, supportDatum_weight,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      cartanHeightWeight_projection, map_smul, smul_eq_mul] using heq
  rw [hweight]
  exact mul_le_mul_of_nonneg_left
    ((M.supportIn T hunimod eW).weight_le_weightSupport hE hw i) hr

omit T hunimod eW [FiniteDimensional ℝ L]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- A bound on generator images controls the map from any word basis to a
basis with bounded structure constants. -/
theorem norm_wordBasis_lieMap_le
    (γ : M.Bases)
    (b : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (F : cartanRootIdeal H →ₗ⁅ℝ⁆ cartanRootIdeal H) {K A : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hbracket : ∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ K)
    (hletter : ∀ i, ‖b.equivFun (F (M.letter i))‖ ≤ A) (v : cartanRootIdeal H) :
    ‖b.equivFun (F v)‖ ≤
      (finrank ℝ (cartanRootIdeal H) : ℝ) *
        (1 + (finrank ℝ (cartanRootIdeal H) : ℝ) ^ 2 * K) ^ M.wordDegreeBound *
        (1 + A) ^ M.wordDegreeBound *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * K
  have hword (w : M.wordList) :
      ‖b.equivFun (F (evalBracketWord M.letter w))‖ ≤
        Q ^ M.wordDegreeBound * (1 + A) ^ M.wordDegreeBound := by
    rw [evalBracketWord_map]
    apply (norm_basis_evalBracketWord_le b (fun i => F (M.letter i)) hK hA hbracket hletter w).trans
    simp only [Fintype.card_fin]
    have hd := M.word_degrees_le w
    apply mul_le_mul
    · exact (pow_le_pow_left₀ (by positivity)
        (show (d : ℝ) ^ 2 * K ≤ Q by dsimp [Q]; linarith) _).trans
        (pow_le_pow_right₀ (by
          dsimp [Q]
          exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hK)) hd.1)
    · exact (pow_le_pow_left₀ hA (by linarith : A ≤ 1 + A) _).trans
        (pow_le_pow_right₀ (by linarith) hd.2)
    · positivity
    · positivity
  have hb (i : Fin d) :
      ‖b.equivFun (F (WordBasisSelections.basis M.letter M.wordList γ i))‖ ≤
        Q ^ M.wordDegreeBound * (1 + A) ^ M.wordDegreeBound := by
    have he := WordBasisSelections.eval_words M.letter M.wordList γ i
    change evalBracketWord M.letter (γ.val i) = _ at he
    rw [← he]
    exact hword (γ.val i)
  have hs := norm_map_between_bases_le (WordBasisSelections.basis M.letter M.wordList γ) b
    F.toLinearMap hb v
  simp only [Fintype.card_fin] at hs
  change ‖b.equivFun (F v)‖ ≤ (d : ℝ) *
    (Q ^ M.wordDegreeBound * (1 + A) ^ M.wordDegreeBound) *
      ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ at hs
  simpa only [Q, d, mul_assoc] using hs

/-- Uniform polynomial coordinate control for Cartan actions with height
inside a scaled template. The input basis is unscaled and need not maximize. -/
theorem exists_controlled_adjoint_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ (A : ℝ) (p : ℕ), 0 ≤ A ∧ ∀ {E : Set W}, IsCompact E → E.Nonempty →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (M.boxCost T hunimod eW E) β.val →
      ∀ (γ : M.Bases) (r : ℝ), 0 ≤ r → ∀ (h : H) (w : W), w ∈ E →
      eW (heightProjection T.character (h : L)) = r • w → ∀ v : cartanRootIdeal H,
      ‖(M.boxBasis T hunimod eW E β r).equivFun (cartanIdealAdjointAutomorphism T H h v)‖ ≤
        A * (1 + ‖(Module.finBasis ℝ H).equivFun h‖) ^ p *
          ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
  obtain ⟨C, p, hC, hletters⟩ := M.exists_residual_letters_bound T
  obtain ⟨K, hK, hbracket⟩ := exists_uniform_rescaled_structureConstant_bound
    M.letter M.bound_zero b₀
  let d := finrank ℝ (cartanRootIdeal H)
  let Q := 1 + (d : ℝ) ^ 2 * K
  refine ⟨(d : ℝ) * Q ^ M.wordDegreeBound * (1 + C) ^ M.wordDegreeBound,
    p * M.wordDegreeBound, by dsimp [Q]; positivity, ?_⟩
  intro E hE hne β hβ γ r hr h w hw hh v
  let q := 1 + ‖(Module.finBasis ℝ H).equivFun h‖
  have hq : 1 ≤ q := le_add_of_nonneg_right (norm_nonneg _)
  have hqp : 1 ≤ q ^ p := one_le_pow₀ hq
  have hF (i : Fin M.letterCount) :
      ‖(M.boxBasis T hunimod eW E β r).equivFun
        (cartanIdealAdjointAutomorphism T H h (M.letter i))‖ ≤ C * q ^ p :=
    (M.norm_adjoint_letter_le T hunimod eW hE hne β hr h w hw hh i).trans (hletters β h i)
  have hb := M.norm_wordBasis_lieMap_le γ (M.boxBasis T hunimod eW E β r)
    (cartanIdealAdjointAutomorphism T H h).toLieHom hK (by positivity : 0 ≤ C * q ^ p)
    (hbracket ((M.supportIn T hunimod eW).weightSupport E) β hβ r hr) hF v
  apply hb.trans
  have hs : 1 + C * q ^ p ≤ (1 + C) * q ^ p := by nlinarith
  calc
    _ ≤ (d : ℝ) * Q ^ M.wordDegreeBound * ((1 + C) * q ^ p) ^ M.wordDegreeBound *
        ‖(WordBasisSelections.basis M.letter M.wordList γ).equivFun v‖ := by
      dsimp only [Q, d]
      gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end CartanWordModel
end PolycyclicRecognition

end

end OAI
