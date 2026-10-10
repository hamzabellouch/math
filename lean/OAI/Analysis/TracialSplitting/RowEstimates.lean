import OAI.Analysis.TracialSplitting.MatrixNormalization

namespace OAI

universe uD uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma entry_norm_le (i : I) : ‖U.entry i‖ ≤ 1 := by
  have h : ‖U.entry i‖ * ‖U.entry i‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, U.gram_diag]
    exact U.projection.norm_le
  nlinarith [norm_nonneg (U.entry i)]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma range_eq_sum : U.sample q = ∑ i, U.entry i * star (U.entry i) := by
  simp only [sample, coeff, U.right_support]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma compression_expand (x : D) :
    U.sample q * x * U.sample q =
      ∑ i, ∑ j, U.entry i * rowPair U.entry x i j * star (U.entry j) := by
  rw [U.range_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, rowPair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [mul_assoc]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma compression_norm_le (x : D) (H : Matrix I I ℂ) {δ : ℝ}
    (h : ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤ δ) :
    ‖U.sample q * x * U.sample q - U.matrix q H‖ ≤ (Fintype.card I : ℝ) ^ 2 * δ := by
  have hmat : U.matrix q H = ∑ i, ∑ j, U.entry i * (H i j • q) * star (U.entry j) := by
    simp only [matrix, coeff, mul_smul_comm, smul_mul_assoc]
  rw [U.compression_expand, hmat, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ∑ j, ‖U.entry i * rowPair U.entry x i j * star (U.entry j) -
        U.entry i * (H i j • q) * star (U.entry j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : I, ∑ _j : I, δ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      rw [← sub_mul, ← mul_sub]
      calc
        _ ≤ ‖U.entry i‖ * ‖rowPair U.entry x i j - H i j • q‖ * ‖star (U.entry j)‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ 1 * ‖rowPair U.entry x i j - H i j • q‖ * 1 := by
          gcongr
          · exact U.entry_norm_le i
          · simpa only [norm_star] using U.entry_norm_le j
        _ ≤ δ := by simpa only [one_mul, mul_one] using h i j
    _ = _ := by simp [pow_two]; ring

end ProjectionRow

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma selfAdjoint_covariance (a : D) : IsSelfAdjoint (a * star a) :=
  IsSelfAdjoint.mul_star_self a

omit [DecidableEq I] [Fintype I] in
lemma traceOneNorm_covariance_difference (τ : Pureness.TracialState D) {q a b : D}
    (hq : IsStarProjection q) (ha : a * q = a) (hb : b * q = b) :
    traceOneNorm τ (b * star b - a * star a) ≤
      (‖a‖ + ‖b‖) * ‖b - a‖ * (τ.functional q).re := by
  apply traceOneNorm_le_of_pairing τ ((selfAdjoint_covariance b).sub
    (selfAdjoint_covariance a))
  intro s _ hs
  have he : b * star b - a * star a =
      (b - a) * q * star b + a * q * (star b - star a) := by
    rw [sub_mul, hb, ha]
    noncomm_ring
  rw [he, mul_add, map_add, Complex.add_re]
  have hq0 : 0 ≤ (τ.functional q).re := (τ.functional.map_nonneg hq.nonneg).1
  have h1 : ‖τ.functional (s * ((b - a) * q * star b))‖ ≤
      ‖s‖ * (τ.functional q).re * (‖b - a‖ * ‖star b‖) := by
    simpa only [mul_assoc] using trace_sandwich_pairing_le τ hq s (b - a) (star b)
  have h2 : ‖τ.functional (s * (a * q * (star b - star a)))‖ ≤
      ‖s‖ * (τ.functional q).re * (‖a‖ * ‖star b - star a‖) := by
    simpa only [mul_assoc] using trace_sandwich_pairing_le τ hq s a (star b - star a)
  have hs1 : ‖s‖ * (τ.functional q).re ≤ (τ.functional q).re := by
    nlinarith [norm_nonneg s]
  have hb0 := norm_nonneg b
  have ha0 := norm_nonneg a
  have hd0 := norm_nonneg (b - a)
  have he1 := (Complex.re_le_norm (τ.functional (s * ((b - a) * q * star b)))).trans h1
  have he2 := (Complex.re_le_norm (τ.functional (s * (a * q * (star b - star a))))).trans h2
  rw [norm_star] at he1
  rw [← star_sub, norm_star] at he2
  simp only [star_sub] at he2
  nlinarith [mul_le_mul_of_nonneg_right hs1 (mul_nonneg hd0 hb0),
    mul_le_mul_of_nonneg_right hs1 (mul_nonneg ha0 hd0)]

omit [DecidableEq I] in
lemma traceOneNorm_sum_le (τ : Pureness.TracialState D) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) :
    traceOneNorm τ (∑ i, a i) ≤ ∑ i, traceOneNorm τ (a i) := by
  apply traceOneNorm_le_of_pairing τ (isSelfAdjoint_sum _ fun i _ => ha i)
  intro s hs hsn
  simp only [Finset.mul_sum, map_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun i _ => trace_selfAdjoint_contraction_mul_le τ hs (ha i) hsn

omit [DecidableEq I] in
lemma row_covariance_trace_error (τ : Pureness.TracialState D) {q : D}
    (hq : IsStarProjection q) (a b : I → D)
    (ha : ∀ i, a i * q = a i) (hb : ∀ i, b i * q = b i) {M N δ : ℝ}
    (hM : ∀ i, ‖a i‖ ≤ M) (hN : ∀ i, ‖b i‖ ≤ N)
    (hδ : ∀ i, ‖b i - a i‖ ≤ δ) :
    traceOneNorm τ ((∑ i, b i * star (b i)) - ∑ i, a i * star (a i)) ≤
      (Fintype.card I : ℝ) * (M + N) * δ * (τ.functional q).re := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, traceOneNorm τ (b i * star (b i) - a i * star (a i)) :=
      traceOneNorm_sum_le τ _ fun i => (selfAdjoint_covariance _).sub (selfAdjoint_covariance _)
    _ ≤ ∑ _i : I, (M + N) * δ * (τ.functional q).re := Finset.sum_le_sum fun i _ => by
      apply (traceOneNorm_covariance_difference τ hq (ha i) (hb i)).trans
      have hMN : 0 ≤ M + N := add_nonneg ((norm_nonneg _).trans (hM i)) ((norm_nonneg _).trans (hN i))
      gcongr
      · exact (τ.functional.map_nonneg hq.nonneg).1
      · exact hM i
      · exact hN i
      · exact hδ i
    _ = _ := by simp; ring

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma rowPair_perturb (a b c d x : D) {E F M N : ℝ}
    (hab : ‖a - b‖ ≤ E) (hcd : ‖c - d‖ ≤ F) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ N)
    (hx : ‖x‖ ≤ 1) :
    ‖star a * x * c - star b * x * d‖ ≤ E * N + M * F := by
  have hE : 0 ≤ E := (norm_nonneg _).trans hab
  have hM : 0 ≤ M := (norm_nonneg _).trans hb
  have he : star a * x * c - star b * x * d =
      star (a - b) * x * c + star b * x * (c - d) := by
    rw [star_sub]; noncomm_ring
  rw [he]
  calc
    _ ≤ ‖star (a - b) * x * c‖ + ‖star b * x * (c - d)‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ * ‖x‖ * ‖c‖ + ‖b‖ * ‖x‖ * ‖c - d‖ := by
      gcongr
      · exact (norm_mul_le _ _).trans (by gcongr; simpa only [norm_star] using norm_mul_le (star (a - b)) x)
      · exact (norm_mul_le _ _).trans (by gcongr; simpa only [norm_star] using norm_mul_le (star b) x)
    _ ≤ E * 1 * N + M * 1 * F := by gcongr
    _ = _ := by ring

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma rowPair_real_scale (a : I → D) (r : I → ℝ) (x : D) (i j : I) :
    rowPair (fun k => r k • a k) x i j = (r i * r j) • rowPair a x i j := by
  simp only [rowPair, star_smul, star_trivial, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [mul_comm (r j) (r i)]

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] [Fintype I] in
lemma rowPair_scale_error {q : D} (a : I → D) (r : I → ℝ) (x : D)
    (H : Matrix I I ℂ) {L δ : ℝ} (hr : ∀ i, 0 ≤ r i) (hL : ∀ i, r i ≤ L)
    (h : ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ δ) (i j : I) :
    ‖rowPair (fun k => r k • a k) x i j - ((r i * r j) • H i j) • q‖ ≤ L ^ 2 * δ := by
  rw [rowPair_real_scale, smul_assoc, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hr i) (hr j))]
  have hL0 : 0 ≤ L := (hr i).trans (hL i)
  calc
    _ ≤ (L * L) * ‖rowPair a x i j - H i j • q‖ := by
      gcongr
      · exact hr j
      · exact hL i
      · exact hL j
    _ ≤ (L * L) * δ := mul_le_mul_of_nonneg_left (h i j) (mul_self_nonneg L)
    _ = _ := by ring

theorem normalize_weighted_row {q : D} (hq : IsStarProjection q)
    (b : I → D) (ρ : I → ℝ) (hρ : ∀ i, 0 < ρ i) (hρ1 : ∀ i, ρ i ≤ 1)
    (hb : ∀ i, b i * q = b i) {L M δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hinv : ∀ i, (ρ i)⁻¹ ≤ L) (hbn : ∀ i, ‖b i‖ ≤ M)
    (hg : ∀ i j, ‖star (b i) * b j - (if i = j then (ρ i) ^ 2 • q else 0)‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * (L ^ 2 * δ) ≤ 1 / 2) :
    ∃ U : ProjectionRow I q,
      (∀ i, ‖U.entry i - (ρ i)⁻¹ • b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * L ^ 3 * M * δ) ∧
      (∀ i, ‖ρ i • U.entry i - b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * L ^ 3 * M * δ) := by
  let a : I → D := fun i => (ρ i)⁻¹ • b i
  have hasupp (i : I) : a i * q = a i := by simp only [a, smul_mul_assoc, hb]
  have han (i : I) : ‖a i‖ ≤ L * M := by
    rw [show a i = (ρ i)⁻¹ • b i from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (inv_pos.mpr (hρ i)))]
    exact mul_le_mul (hinv i) (hbn i) (norm_nonneg _) hL
  have hag (i j : I) : ‖star (a i) * a j - (if i = j then q else 0)‖ ≤ L ^ 2 * δ := by
    have he : star (a i) * a j - (if i = j then q else 0) =
        ((ρ i)⁻¹ * (ρ j)⁻¹) •
          (star (b i) * b j - (if i = j then (ρ i) ^ 2 • q else 0)) := by
      simp only [a, star_smul, star_trivial, smul_mul_smul_comm, smul_sub]
      congr 1
      by_cases hij : i = j
      · subst j
        simp only [ite_true, smul_smul]
        rw [show (ρ i)⁻¹ * (ρ i)⁻¹ * (ρ i) ^ 2 = 1 by field_simp [ne_of_gt (hρ i)]]
        rw [one_smul]
      · simp only [ite_eq_right hij, smul_zero]
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (inv_pos.mpr (hρ i)))
      (le_of_lt (inv_pos.mpr (hρ j))))]
    calc
      _ ≤ (L * L) * ‖star (b i) * b j - (if i = j then (ρ i) ^ 2 • q else 0)‖ := by
        gcongr
        · exact le_of_lt (inv_pos.mpr (hρ j))
        · exact hinv i
        · exact hinv j
      _ ≤ (L * L) * δ := mul_le_mul_of_nonneg_left (hg i j) (mul_self_nonneg L)
      _ = _ := by ring
  obtain ⟨U, hU⟩ := normalize_almost_row hq a hasupp hag hsmall
  have hsum : (∑ j, ‖a j‖) ≤ (Fintype.card I : ℝ) * (L * M) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) fun j _ => han j
  have hU' (i : I) : ‖U.entry i - a i‖ ≤
      2 * (Fintype.card I : ℝ) ^ 3 * L ^ 3 * M * δ := by
    apply (hU i).trans
    calc
      _ ≤ 2 * ((Fintype.card I : ℝ) * (L * M)) * (Fintype.card I : ℝ) ^ 2 * (L ^ 2 * δ) := by
        gcongr
      _ = _ := by ring
  refine ⟨U, hU', fun i => ?_⟩
  have he : ρ i • U.entry i - b i = ρ i • (U.entry i - a i) := by
    rw [smul_sub]
    simp only [a, smul_smul, mul_inv_cancel₀ (ne_of_gt (hρ i)), one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (hρ i)]
  exact (mul_le_mul_of_nonneg_right (hρ1 i) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hU' i)

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma normalized_rowPair_error {q : D} (U : ProjectionRow I q)
    (b : I → D) (r : I → ℝ) (x : D) (hx : ‖x‖ ≤ 1) (H : Matrix I I ℂ)
    {L M E δ : ℝ} (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L) (hri : ∀ i, r i ≤ L)
    (hbn : ∀ i, ‖b i‖ ≤ M)
    (hU : ∀ i, ‖U.entry i - r i • b i‖ ≤ E)
    (h : ∀ i j, ‖rowPair b x i j - H i j • q‖ ≤ δ) (i j : I) :
    ‖rowPair U.entry x i j - ((r i * r j) • H i j) • q‖ ≤
      E * (1 + L * M) + L ^ 2 * δ := by
  have han : ‖r i • b i‖ ≤ L * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr i)]
    exact mul_le_mul (hri i) (hbn i) (norm_nonneg _) hL
  have hp := rowPair_perturb (U.entry i) (r i • b i) (U.entry j) (r j • b j) x
    (hU i) (hU j) han (U.entry_norm_le j) hx
  have hscale := rowPair_scale_error b r x H hr hri h i j
  calc
    _ ≤ ‖rowPair U.entry x i j - rowPair (fun k => r k • b k) x i j‖ +
        ‖rowPair (fun k => r k • b k) x i j - ((r i * r j) • H i j) • q‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (E * 1 + (L * M) * E) + L ^ 2 * δ := add_le_add hp hscale
    _ = _ := by ring

end

section

open scoped ComplexOrder

section RowSubmatrix

variable {I : Type uI} {J : Type uJ} {D : Type uD} [Fintype I] [Fintype J] [CStarAlgebra D]

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

def subrow (f : J ↪ I) : ProjectionRow J q where
  projection := U.projection
  entry := U.entry ∘ f
  gram_diag i := U.gram_diag (f i)
  gram_offdiag i j hij := U.gram_offdiag (f i) (f j) (f.injective.ne hij)

omit [Fintype J] in
def atom (i : I) : D := U.entry i * star (U.entry i)

omit [Fintype J] in
lemma atom_eq_coeff (i : I) : U.atom i = U.coeff q i i := by
  simp only [atom, coeff, U.right_support]

omit [Fintype J] in
lemma atom_projection (i : I) : IsStarProjection (U.atom i) := by
  classical
  rw [U.atom_eq_coeff]
  constructor
  · change U.coeff q i i * U.coeff q i i = U.coeff q i i
    rw [U.coeff_mul q q U.projection.isIdempotentElem, ite_eq_left rfl,
      U.projection.isIdempotentElem]
  · change star (U.coeff q i i) = U.coeff q i i
    rw [U.coeff_star, U.projection.isSelfAdjoint.star_eq]

omit [Fintype J] in
lemma atom_orthogonal : Pairwise (fun i j => U.atom i * U.atom j = 0) := by
  classical
  intro i j hij
  rw [U.atom_eq_coeff, U.atom_eq_coeff, U.coeff_mul q q U.projection.isIdempotentElem,
    ite_eq_right hij]

omit [Fintype J] in
lemma atom_sum : ∑ i, U.atom i = U.sample q := U.range_eq_sum.symm

lemma subrow_range (f : J ↪ I) : (U.subrow f).sample q = ∑ i, U.atom (f i) :=
  (U.subrow f).range_eq_sum

omit [Fintype J] in
lemma upper_cut_subrow [LinearOrder I] (j : I) :
    upperLayerCut U.atom j =
      (U.subrow (Function.Embedding.subtype (j ≤ ·))).sample q := by
  classical
  rw [U.subrow_range, upperLayerCut]
  simp only [cutCoefficient, ite_smul, one_smul, zero_smul]
  exact by simpa only [Finset.subtype_univ, Finset.sum_filter, Function.Embedding.subtype_apply] using
    (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := (j ≤ ·)) U.atom).symm

variable [PartialOrder D] [StarOrderedRing D]

omit [Fintype J] [StarOrderedRing D] in
lemma atom_trace (τ : Pureness.TracialState D) (i : I) :
    τ.functional (U.atom i) = τ.functional q := by
  dsimp [atom]
  rw [τ.tracial, U.gram_diag]

omit [Fintype J] [PartialOrder D] [StarOrderedRing D] in
lemma atom_nonzero (hq : q ≠ 0) (i : I) : U.atom i ≠ 0 := by
  intro h
  have hn : ‖U.entry i‖ ^ 2 = 0 := by
    simpa only [atom, CStarRing.norm_self_mul_star, norm_zero, pow_two] using
      congrArg norm h
  have he : U.entry i = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  apply hq
  rw [← U.gram_diag i, he, star_zero, zero_mul]

end ProjectionRow

end RowSubmatrix

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma rowPair_spectral_rotation {q : D} (f : D →ₚ[ℂ] ℂ) (a : I → D) {δ : ℝ}
    (h : ∀ i j, ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ δ) (i j : I) :
    ‖star (rotateRow a (scalarRowGram_posSemidef f a).isHermitian.eigenvectorUnitary i) *
        rotateRow a (scalarRowGram_posSemidef f a).isHermitian.eigenvectorUnitary j -
      (if i = j then
        (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i • q else 0)‖ ≤
      (Fintype.card I : ℝ) ^ 2 * δ := by
  let hG := (scalarRowGram_posSemidef f a).isHermitian
  have he := hG.conjStarAlgAut_star_eigenvectorUnitary
  simp only [Unitary.conjStarAlgAut_star_apply] at he
  have hr := rowPair_rotate_error a hG.eigenvectorUnitary 1 (scalarRowGram f a) h i j
  rw [he] at hr
  simpa only [rowPair, mul_one, Matrix.diagonal_apply, Function.comp_apply, ite_smul,
    zero_smul, RCLike.ofReal_eq_complex_ofReal, Complex.coe_smul] using hr

end

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [Fintype I] in
lemma traceOneNorm_of_nonneg (τ : Pureness.TracialState D) {a : D} (ha : 0 ≤ a) :
    traceOneNorm τ a = (τ.functional a).re := by
  rw [traceOneNorm, CFC.abs_of_nonneg a ha]

omit [Fintype I] in
lemma covariance_trace_le_of_gram {q b : D} (hq : IsStarProjection q)
    (hb : b * q = b) {c δ : ℝ} (hg : ‖star b * b - c • q‖ ≤ δ)
    (τ : Pureness.TracialState D) :
    (τ.functional (b * star b)).re ≤ (c + δ) * (τ.functional q).re := by
  have hqs : q * star b = star b := by
    simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hb
  have hsup : q * (star b * b - c • q) = star b * b - c • q := by
    rw [mul_sub, ← mul_assoc, hqs, mul_smul_comm, hq.isIdempotentElem]
  have hv := (Complex.re_le_norm (τ.functional (star b * b - c • q))).trans
    ((trace_supported_norm_le τ hq hsup).trans
      (mul_le_mul_of_nonneg_right hg (τ.functional.map_nonneg hq.nonneg).1))
  simp only [map_sub, τ.functional.map_smul_of_tower, Complex.sub_re,
    Complex.smul_re, smul_eq_mul] at hv
  rw [τ.tracial b (star b)]
  linarith

lemma covariance_nonneg (a : I → D) : 0 ≤ ∑ i, a i * star (a i) :=
  Finset.sum_nonneg fun i _ => mul_star_self_nonneg (a i)

lemma covariance_selfAdjoint (a : I → D) : IsSelfAdjoint (∑ i, a i * star (a i)) :=
  .of_nonneg (covariance_nonneg a)

lemma dropped_covariance_trace {q : D} (hq : IsStarProjection q) (b : I → D)
    (hb : ∀ i, b i * q = b i) (c : I → ℝ) {σ δ : ℝ}
    (hc : ∀ i, c i ≤ σ) (hg : ∀ i, ‖star (b i) * b i - c i • q‖ ≤ δ)
    (τ : Pureness.TracialState D) :
    traceOneNorm τ (∑ i, b i * star (b i)) ≤
      (Fintype.card I : ℝ) * (σ + δ) * (τ.functional q).re := by
  rw [traceOneNorm_of_nonneg τ (covariance_nonneg b), map_sum, Complex.re_sum]
  calc
    _ ≤ ∑ _i : I, (σ + δ) * (τ.functional q).re := Finset.sum_le_sum fun i _ => by
      apply (covariance_trace_le_of_gram hq (hb i) (hg i) τ).trans
      exact mul_le_mul_of_nonneg_right (by linarith [hc i])
        (τ.functional.map_nonneg hq.nonneg).1
    _ = _ := by simp; ring

lemma covariance_retain_error (τ : Pureness.TracialState D) {q : D}
    (hq : IsStarProjection q) (a : I → D) (p : I → Prop) [DecidablePred p]
    (b : {i // p i} → D) (ha : ∀ i, a i * q = a i)
    (hb : ∀ i, b i * q = b i) {M N E σ δ : ℝ}
    (hM : ∀ i, ‖a i‖ ≤ M) (hN : ∀ i, ‖b i‖ ≤ N)
    (hdist : ∀ i, ‖b i - a i‖ ≤ E) (c : I → ℝ)
    (hdrop : ∀ i, ¬p i → c i ≤ σ)
    (hgram : ∀ i, ‖star (a i) * a i - c i • q‖ ≤ δ) :
    traceOneNorm τ ((∑ i, b i * star (b i)) - ∑ i, a i * star (a i)) ≤
      ((Fintype.card {i // p i} : ℝ) * (M + N) * E +
        (Fintype.card {i // ¬p i} : ℝ) * (σ + δ)) * (τ.functional q).re := by
  have he := Fintype.sum_subtype_add_sum_subtype p (fun i => a i * star (a i))
  have hmain := row_covariance_trace_error τ hq (fun i : {i // p i} => a i) b
    (fun i => ha i) hb (fun i => hM i) hN hdist
  have htail := dropped_covariance_trace hq (fun i : {i // ¬p i} => a i)
    (fun i => ha i) (fun i => c i) (fun i => hdrop i i.property)
    (fun i => hgram i) τ
  rw [← he]
  have hsplit : (∑ i, b i * star (b i)) -
      ((∑ i : {i // p i}, a i * star (a i)) + ∑ i : {i // ¬p i}, a i * star (a i)) =
      ((∑ i, b i * star (b i)) - ∑ i : {i // p i}, a i * star (a i)) +
        -(∑ i : {i // ¬p i}, a i * star (a i)) := by abel
  rw [hsplit]
  apply (traceOneNorm_add_le τ ((covariance_selfAdjoint b).sub
    (covariance_selfAdjoint _)) (covariance_selfAdjoint _).neg).trans
  rw [traceOneNorm_neg]
  nlinarith

end

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem normalize_retained_spectrum {q : D} (hq : IsStarProjection q)
    (b : I → D) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hb : ∀ i, b i * q = b i) {σ M δ : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hbn : ∀ i, ‖b i‖ ≤ M)
    (hg : ∀ i j, ‖star (b i) * b j - (if i = j then c i • q else 0)‖ ≤ δ)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 * δ) ≤ 1 / 2) :
    ∃ U : ProjectionRow {i : I // σ ≤ c i} q,
      (∀ i, ‖U.entry i - (Real.sqrt (c i))⁻¹ • b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ) ∧
      (∀ i : {i : I // σ ≤ c i}, ‖Real.sqrt (c i) • U.entry i - b i‖ ≤
        2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ) := by
  classical
  let J := {i : I // σ ≤ c i}
  have hcard : (Fintype.card J : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i => σ ≤ c i)
  have hL : 0 ≤ (Real.sqrt σ)⁻¹ := le_of_lt (inv_pos.mpr (Real.sqrt_pos.mpr hσ))
  have hρ (i : J) : 0 < Real.sqrt (c i) := Real.sqrt_pos.mpr (hσ.trans_le i.property)
  have hρ1 (i : J) : Real.sqrt (c i) ≤ 1 := Real.sqrt_le_one.mpr (hc1 i)
  have hinv (i : J) : (Real.sqrt (c i))⁻¹ ≤ (Real.sqrt σ)⁻¹ :=
    inv_le_inv₀ (hρ i) (Real.sqrt_pos.mpr hσ) |>.mpr (Real.sqrt_le_sqrt i.property)
  have hgs (i j : J) :
      ‖star (b i) * b j - (if i = j then (Real.sqrt (c i)) ^ 2 • q else 0)‖ ≤ δ := by
    have he : (i = j) ↔ (i.val = j.val) := Subtype.ext_iff
    simpa only [Real.sq_sqrt (hc i), he] using hg i j
  have hsmallJ : (Fintype.card J : ℝ) ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 * δ) ≤ 1 / 2 := by
    apply le_trans ?_ hsmall
    gcongr
  obtain ⟨U, hU, hW⟩ := normalize_weighted_row hq (fun i : J => b i)
    (fun i => Real.sqrt (c i)) hρ hρ1 (fun i => hb i) hL hδ hinv (fun i => hbn i) hgs hsmallJ
  have hE : 2 * (Fintype.card J : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ ≤
      2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * δ := by gcongr
  exact ⟨U, fun i => (hU i).trans hE, fun i => (hW i).trans hE⟩

omit [PartialOrder D] [StarOrderedRing D] [DecidableEq I] in
lemma covariance_scaled_row {q : D} (U : ProjectionRow I q) (c : I → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    (∑ i, (Real.sqrt (c i) • U.entry i) * star (Real.sqrt (c i) • U.entry i)) =
      ∑ i, c i • U.atom i := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_smul, star_trivial, smul_mul_smul_comm, ProjectionRow.atom]
  rw [← pow_two, Real.sq_sqrt (hc i)]

omit [DecidableEq I] in
lemma retained_spectrum_trace_error {q : D} (hq : IsStarProjection q)
    (b : I → D) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hb : ∀ i, b i * q = b i) {σ M E δ : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (hσδ : 0 ≤ σ + δ) (hbn : ∀ i, ‖b i‖ ≤ M)
    (hg : ∀ i, ‖star (b i) * b i - c i • q‖ ≤ δ)
    (U : ProjectionRow {i : I // σ ≤ c i} q)
    (hU : ∀ i : {i : I // σ ≤ c i}, ‖Real.sqrt (c i) • U.entry i - b i‖ ≤ E)
    (τ : Pureness.TracialState D) :
    traceOneNorm τ ((∑ i : {i : I // σ ≤ c i}, c i • U.atom i) - ∑ i, b i * star (b i)) ≤
      ((Fintype.card I : ℝ) * ((M + 1) * E + (σ + δ))) * (τ.functional q).re := by
  classical
  have hnorm (i : {i : I // σ ≤ c i}) : ‖Real.sqrt (c i) • U.entry i‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul (Real.sqrt_le_one.mpr (hc1 i)) (U.entry_norm_le i)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hsupp (i : {i : I // σ ≤ c i}) : (Real.sqrt (c i) • U.entry i) * q =
      Real.sqrt (c i) • U.entry i := by rw [smul_mul_assoc, U.right_support]
  have he := covariance_retain_error τ hq b (fun i => σ ≤ c i)
    (fun i => Real.sqrt (c i) • U.entry i) hb hsupp hbn hnorm hU c
    (fun i hi => (lt_of_not_ge hi).le) hg
  rw [covariance_scaled_row U (fun i => c i) (fun i => hc i)] at he
  apply he.trans
  have hk : (Fintype.card {i : I // σ ≤ c i} : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i => σ ≤ c i)
  have hd : (Fintype.card {i : I // ¬σ ≤ c i} : ℝ) ≤ Fintype.card I := by
    exact_mod_cast Fintype.card_subtype_le (fun i => ¬σ ≤ c i)
  apply mul_le_mul_of_nonneg_right ?_ (τ.functional.map_nonneg hq.nonneg).1
  nlinarith [mul_le_mul_of_nonneg_right hk (mul_nonneg (by linarith : 0 ≤ M + 1) hE),
    mul_le_mul_of_nonneg_right hd hσδ]

end

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [CStarAlgebra D]

def rawRow (w : I → ℝ) (v : I → D) (q : D) (i : I) : D :=
  Real.sqrt (w i) • (v i * q)

omit [Fintype I] in
lemma rawRow_support (w : I → ℝ) (v : I → D) {q : D} (hq : IsStarProjection q) (i : I) :
    rawRow w v q i * q = rawRow w v q i := by
  simp only [rawRow, smul_mul_assoc, mul_assoc, hq.isIdempotentElem.eq]

omit [Fintype I] in
lemma rawRow_pair (w : I → ℝ) (v : I → D) {q : D} (hq : IsStarProjection q)
    (x : D) (i j : I) :
    rowPair (rawRow w v q) x i j = (Real.sqrt (w i) * Real.sqrt (w j)) •
      (q * (star (v i) * x * v j) * q) := by
  simp only [rowPair, rawRow, star_smul, star_trivial, star_mul, hq.isSelfAdjoint.star_eq,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  rw [mul_comm (Real.sqrt (w j)) (Real.sqrt (w i))]

lemma rawRow_covariance (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (v : I → D)
    {q : D} (hq : IsStarProjection q) :
    ∑ i, rawRow w v q i * star (rawRow w v q i) = weightedAverage w v q := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [rawRow, star_smul, star_trivial, star_mul, hq.isSelfAdjoint.star_eq,
    smul_mul_smul_comm]
  rw [← pow_two, Real.sq_sqrt (hw i)]
  congr 1
  simp only [mul_assoc, ← mul_assoc q q, hq.isIdempotentElem.eq]

omit [Fintype I] in
lemma rawRow_norm_le_sqrt (w : I → ℝ) (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1)
    {q : D} (hq : IsStarProjection q) (i : I) :
    ‖rawRow w v q i‖ ≤ Real.sqrt (w i) := by
  rw [rawRow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖v i * q‖ ≤ 1 := (norm_mul_le _ _).trans
    ((mul_le_mul (hv i) hq.norm_le (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  exact (mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)).trans_eq (mul_one _)

lemma rawRow_norm_squares (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1) {q : D} (hq : IsStarProjection q) :
    ∑ i, ‖rawRow w v q i‖ ^ 2 ≤ 1 := by
  rw [← hw1]
  apply Finset.sum_le_sum
  intro i _
  have h := rawRow_norm_le_sqrt w v hv hq i
  nlinarith [Real.sq_sqrt (hw i), norm_nonneg (rawRow w v q i), Real.sqrt_nonneg (w i)]

lemma rawRow_norm_le_one (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1) {q : D} (hq : IsStarProjection q) (i : I) :
    ‖rawRow w v q i‖ ≤ 1 := by
  apply (rawRow_norm_le_sqrt w v hv hq i).trans
  apply Real.sqrt_le_one.mpr
  rw [← hw1]
  exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)

lemma rawRow_norm_sum (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1) {q : D} (hq : IsStarProjection q) :
    ∑ i, ‖rawRow w v q i‖ ≤ Fintype.card I := by
  simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ => rawRow_norm_le_one w hw hw1 v hv hq i

variable [PartialOrder D] [StarOrderedRing D]

lemma rawRow_pair_scalar_error (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (v : I → D) {q : D} (hq : IsStarProjection q)
    (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) (hfq : f q = 1)
    (x : D) (i j : I) {ε : ℝ}
    (h : ∃ α : ℂ, ‖q * (star (v i) * x * v j) * q - α • q‖ < ε) :
    ‖rowPair (rawRow w v q) x i j - f (rowPair (rawRow w v q) x i j) • q‖ < 2 * ε := by
  obtain ⟨α, hα⟩ := h
  have hscalar := state_scalar_error f hf hq hfq (q * (star (v i) * x * v j) * q) α
  have hwi (k : I) : Real.sqrt (w k) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    rw [← hw1]
    exact Finset.single_le_sum (fun l _ => hw l) (Finset.mem_univ k)
  have hcoeff : Real.sqrt (w i) * Real.sqrt (w j) ≤ 1 :=
    (mul_le_mul (hwi i) (hwi j) (Real.sqrt_nonneg _) (by norm_num)).trans_eq (one_mul _)
  rw [rawRow_pair w v hq, f.map_smul_of_tower, smul_assoc, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  calc
    _ ≤ 1 * ‖q * (star (v i) * x * v j) * q - f (q * (star (v i) * x * v j) * q) • q‖ :=
      mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    _ ≤ 2 * ‖q * (star (v i) * x * v j) * q - α • q‖ := by simpa only [one_mul] using hscalar
    _ < 2 * ε := by linarith

end CurrentMain

end

end OAI
