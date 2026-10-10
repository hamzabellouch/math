import OAI.Analysis.TracialSplitting.RowEstimates

namespace OAI

universe uD uE uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem spectral_row_block {q : D} (hq : IsStarProjection q)
    (f : D →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : I → D)
    (haq : ∀ i, a i * q = a i) (ha2 : ∑ i, ‖a i‖ ^ 2 ≤ 1)
    {M σ δ : ℝ} (hM : 0 ≤ M) (hasum : ∑ i, ‖a i‖ ≤ M)
    (hσ : 0 < σ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ δ)
    (K : Finset D)
    (htest : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ δ)
    (hKn : ∀ x ∈ K, ‖x‖ ≤ 1)
    (hsmall : (Fintype.card I : ℝ) ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 *
      ((Fintype.card I : ℝ) ^ 2 * δ)) ≤ 1 / 2) :
    let c := (scalarRowGram_posSemidef f a).isHermitian.eigenvalues
    let E := 2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M *
      ((Fintype.card I : ℝ) ^ 2 * δ)
    ∃ U : ProjectionRow {i : I // σ ≤ c i} q,
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ ((∑ i : {i : I // σ ≤ c i}, c i • U.atom i) -
          ∑ i, a i * star (a i)) ≤
          ((Fintype.card I : ℝ) * ((M + 1) * E + (σ + (Fintype.card I : ℝ) ^ 2 * δ))) *
            (τ.functional q).re) ∧
      (∀ x ∈ K, ∃ H : Matrix {i : I // σ ≤ c i} {i : I // σ ≤ c i} ℂ,
        ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤
          E * (1 + (Real.sqrt σ)⁻¹ * M) + (Real.sqrt σ)⁻¹ ^ 2 *
            ((Fintype.card I : ℝ) ^ 2 * δ)) := by
  classical
  dsimp only
  let c := (scalarRowGram_posSemidef f a).isHermitian.eigenvalues
  let Z := (scalarRowGram_posSemidef f a).isHermitian.eigenvectorUnitary
  let b := rotateRow a Z
  let Δ := (Fintype.card I : ℝ) ^ 2 * δ
  let E := 2 * (Fintype.card I : ℝ) ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * M * Δ
  have hc (i : I) : 0 ≤ c i := (scalarRowGram_posSemidef f a).eigenvalues_nonneg i
  have hc1 (i : I) : c i ≤ 1 := scalarRowGram_eigenvalue_le_one f hf a ha2 i
  have hbsupp (i : I) : b i * q = b i := rotateRow_right_support a haq Z i
  have hbn (i : I) : ‖b i‖ ≤ M := (rotateRow_norm_le a Z i).trans hasum
  have hΔ : 0 ≤ Δ := mul_nonneg (sq_nonneg _) hδ
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbg (i j : I) : ‖star (b i) * b j - (if i = j then c i • q else 0)‖ ≤ Δ :=
    rowPair_spectral_rotation f a hgram i j
  obtain ⟨U, hU, hU'⟩ := normalize_retained_spectrum hq b c hc hc1 hbsupp
    hσ hM hΔ hbn hbg hsmall
  refine ⟨U, ?_, ?_⟩
  · intro τ
    have he := retained_spectrum_trace_error hq b c hc hc1 hbsupp hM hE
      (add_nonneg hσ.le hΔ) hbn (fun i => by simpa using hbg i i) U hU' τ
    rw [rotateRow_covariance a Z] at he
    exact he
  · intro x hx
    obtain ⟨H, hH⟩ := htest x hx
    let H' : Matrix I I ℂ := star (Z : Matrix I I ℂ) * H * Z
    let r : {i : I // σ ≤ c i} → ℝ := fun i => (Real.sqrt (c i))⁻¹
    have hr (i : {i : I // σ ≤ c i}) : 0 ≤ r i := by dsimp [r]; positivity
    have hrL (i : {i : I // σ ≤ c i}) : r i ≤ (Real.sqrt σ)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hσ) (Real.sqrt_le_sqrt i.property)
    refine ⟨fun i j => (r i * r j) • H' i j, fun i j => ?_⟩
    apply normalized_rowPair_error U (fun i => b i) r x (hKn x hx)
      (fun i j => H' i j) hr (by positivity) hrL (fun i => hbn i) hU
    exact fun i j => rowPair_rotate_error a Z x H hH i j

end

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [CStarAlgebra D]

def sortedIndex (c : I → ℝ) : Fin (Fintype.card I) ≃ I :=
  (Tuple.sort (c ∘ (Fintype.equivFin I).symm)).trans (Fintype.equivFin I).symm

lemma sortedIndex_monotone (c : I → ℝ) : Monotone (c ∘ sortedIndex c) :=
  Tuple.monotone_sort (c ∘ (Fintype.equivFin I).symm)

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

def sorted (c : I → ℝ) : ProjectionRow (Fin (Fintype.card I)) q :=
  U.subrow (sortedIndex c).toEmbedding

lemma sorted_weighted_sum (c : I → ℝ) :
    ∑ i, c (sortedIndex c i) • (U.sorted c).atom i = ∑ i, c i • U.atom i := by
  exact (sortedIndex c).sum_comp (fun i => c i • U.atom i)

lemma layer_sum {n : ℕ} (U : ProjectionRow (Fin n) q) (c : Fin n → ℝ) :
    ∑ j, orderedLayerWeights c j • upperLayerCut U.atom j = ∑ i, c i • U.atom i := by
  rw [layer_decomposition]
  simp only [layerCoefficient_orderedLayerWeights]

lemma subrow_entry_error {J : Type uJ} [Fintype J] (e : J ↪ I) (x : D)
    (H : Matrix I I ℂ) {δ : ℝ}
    (h : ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤ δ) :
    ∀ i j, ‖rowPair (U.subrow e).entry x i j - H (e i) (e j) • q‖ ≤ δ :=
  fun i j => h (e i) (e j)

lemma subrow_compression {J : Type uJ} [Fintype J] (e : J ↪ I) (x : D)
    (H : Matrix I I ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i j, ‖rowPair U.entry x i j - H i j • q‖ ≤ δ) :
    ‖(U.subrow e).sample q * x * (U.subrow e).sample q -
      (U.subrow e).matrix q (H.submatrix e e)‖ ≤ (Fintype.card I : ℝ) ^ 2 * δ := by
  classical
  apply ((U.subrow e).compression_norm_le x (H.submatrix e e)
    (U.subrow_entry_error e x H h)).trans
  have hcard : (Fintype.card J : ℝ) ≤ (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_le_of_injective e e.injective
  gcongr

end ProjectionRow

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceOneNorm_unitary_conjugate (τ : Pureness.TracialState D) (x : unitary D) (a : D) :
    traceOneNorm τ ((x : D) * a * star (x : D)) = traceOneNorm τ a := by
  have he : star ((x : D) * a * star (x : D)) * ((x : D) * a * star (x : D)) =
      (x : D) * (star a * a) * star (x : D) := by
    simp only [star_mul, star_star, mul_assoc, ← mul_assoc (star (x : D)) (x : D),
      x.property.1, one_mul]
  dsimp only [traceOneNorm, CFC.abs]
  rw [he, sqrt_unitary_conjugate (star_mul_self_nonneg a), trace_unitary_conjugate]

lemma trace_re_le_oneNorm (τ : Pureness.TracialState D) {a : D} (ha : IsSelfAdjoint a) :
    (τ.functional a).re ≤ traceOneNorm τ a := by
  simpa only [one_mul] using
    trace_selfAdjoint_contraction_mul_le τ (IsSelfAdjoint.one D) ha (IsStarProjection.one D).norm_le

lemma trace_mass_perturb (τ : Pureness.TracialState D) {b h : D}
    (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) {ε t : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε) (hmass : (τ.functional h).re ≤ t) :
    (τ.functional b).re ≤ t + ε := by
  have ht := (trace_re_le_oneNorm τ (hb.sub hh)).trans hclose
  simp only [map_sub, Complex.sub_re] at ht
  linarith

lemma trace_central_perturb (τ : Pureness.TracialState D) {b h : D}
    (hb : IsSelfAdjoint b) (hh : IsSelfAdjoint h) (x : unitary D) {ε μ : ℝ}
    (hclose : traceOneNorm τ (b - h) ≤ ε)
    (hcentral : traceOneNorm τ (h - (x : D) * h * star (x : D)) ≤ μ) :
    traceOneNorm τ (b - (x : D) * b * star (x : D)) ≤ 2 * ε + μ := by
  have he : b - (x : D) * b * star (x : D) =
      ((b - h) + (h - (x : D) * h * star (x : D))) +
        (x : D) * (h - b) * star (x : D) := by noncomm_ring
  rw [he]
  have htriangle := traceOneNorm_add_le τ ((hb.sub hh).add (hh.sub (hh.conjugate (x : D))))
    ((hh.sub hb).conjugate (x : D))
  have htriangle' := traceOneNorm_add_le τ (hb.sub hh) (hh.sub (hh.conjugate (x : D)))
  have hrev : traceOneNorm τ (h - b) = traceOneNorm τ (b - h) := by
    rw [← neg_sub b h, traceOneNorm_neg]
  rw [traceOneNorm_unitary_conjugate, hrev] at htriangle
  linarith

lemma layer_energy_perturb {n : ℕ} (τ : Pureness.TracialState D)
    (e : Fin n → D) (he : ∀ i, IsStarProjection (e i))
    (ho : Pairwise (fun i j => e i * e j = 0))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (hm : Monotone c)
    (x : unitary D) {h : D} (hh : 0 ≤ h) {η t : ℝ}
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (ht : 0 ≤ t)
    (hclose : traceOneNorm τ ((∑ i, c i • e i) - h) ≤ η ^ 2 * t)
    (hmass : (τ.functional h).re ≤ t)
    (hcentral : traceOneNorm τ (h - (x : D) * h * star (x : D)) ≤ η ^ 2 * t) :
    ∑ j, orderedLayerWeights c j * traceTwoNorm τ
      ((x : D) * upperLayerCut e j - upperLayerCut e j * (x : D)) ^ 2 ≤ 6 * η * t := by
  let b := ∑ i, c i • e i
  have hb : 0 ≤ b := projection_combination_nonneg e he c hc
  have hbmass := trace_mass_perturb τ hb.isSelfAdjoint hh.isSelfAdjoint hclose hmass
  have hbcentral := trace_central_perturb τ hb.isSelfAdjoint hh.isSelfAdjoint x hclose hcentral
  have hlayers : ∑ j, orderedLayerWeights c j • upperLayerCut e j = b := by
    rw [layer_decomposition]
    simp only [layerCoefficient_orderedLayerWeights]
    rfl
  have henergy := layer_energy_le_of_orthogonal τ e he ho (orderedLayerWeights c)
    (orderedLayerWeights_nonneg c hc hm) x
  rw [hlayers] at henergy
  apply henergy.trans
  have hprod : (τ.functional b).re * traceOneNorm τ (b - (x : D) * b * star (x : D)) ≤
      (3 * η * t) ^ 2 := by
    have hbound := mul_le_mul hbmass hbcentral
      (traceOneNorm_nonneg τ _) (by positivity : 0 ≤ t + η ^ 2 * t)
    apply hbound.trans
    have hηsq : η ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg t),
      mul_le_mul_of_nonneg_right hηsq (by positivity : 0 ≤ η ^ 2 * t ^ 2)]
  have hsqrt : Real.sqrt ((τ.functional b).re *
      traceOneNorm τ (b - (x : D) * b * star (x : D))) ≤ 3 * η * t :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, hprod⟩
  linarith

end

section

lemma block_tolerances (m : ℝ) (hm : 0 ≤ m) {η : ℝ} (hη : 0 < η) :
    ∃ σ δ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < δ ∧
      m ^ 2 * ((Real.sqrt σ)⁻¹ ^ 2 * (m ^ 2 * δ)) ≤ 1 / 2 ∧
      m * ((m + 1) * (2 * m ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * m * (m ^ 2 * δ)) +
        (σ + m ^ 2 * δ)) ≤ η ^ 2 ∧
      m ^ 2 * ((2 * m ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * m * (m ^ 2 * δ)) *
        (1 + (Real.sqrt σ)⁻¹ * m) + (Real.sqrt σ)⁻¹ ^ 2 * (m ^ 2 * δ)) < η := by
  obtain ⟨σ₀, hσ₀, hσm⟩ := exists_pos_mul_lt (half_pos (sq_pos_of_pos hη)) m
  let σ := min σ₀ (1 / 2)
  have hσ : 0 < σ := lt_min hσ₀ (by norm_num)
  have hσ1 : σ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hσm' : m * σ < η ^ 2 / 2 :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) hm).trans_lt hσm
  let L := (Real.sqrt σ)⁻¹
  let E := 2 * m ^ 3 * L ^ 3 * m * m ^ 2
  let A := m ^ 2 * (L ^ 2 * m ^ 2)
  let B := m * ((m + 1) * E + m ^ 2)
  let C := m ^ 2 * (E * (1 + L * m) + L ^ 2 * m ^ 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨δ₁, hδ₁, he₁⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 2) A
  obtain ⟨δ₂, hδ₂, he₂⟩ := exists_pos_mul_lt (half_pos (sq_pos_of_pos hη)) B
  obtain ⟨δ₃, hδ₃, he₃⟩ := exists_pos_mul_lt hη C
  let δ := min δ₁ (min δ₂ δ₃)
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hd3 : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hhA : A * δ < 1 / 2 := (mul_le_mul_of_nonneg_left hd1 hA).trans_lt he₁
  have hhB : B * δ < η ^ 2 / 2 := (mul_le_mul_of_nonneg_left hd2 hB).trans_lt he₂
  have hhC : C * δ < η := (mul_le_mul_of_nonneg_left hd3 hC).trans_lt he₃
  refine ⟨σ, δ, hσ, hσ1, lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_, ?_, ?_⟩
  · calc
      _ = A * δ := by dsimp [A, L]; ring
      _ ≤ 1 / 2 := hhA.le
  · have hh : B * δ + m * σ ≤ η ^ 2 := by linarith
    calc
      _ = B * δ + m * σ := by dsimp [B, E, L]; ring
      _ ≤ η ^ 2 := hh
  · calc
      _ = C * δ := by dsimp [C, E, L]; ring
      _ < η := hhC

open scoped ComplexOrder

def rowCorrectionError (m σ δ : ℝ) : ℝ :=
  2 * m ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * m * (m ^ 2 * δ)

def rowCompressionError (m σ δ : ℝ) : ℝ :=
  rowCorrectionError m σ δ * (1 + (Real.sqrt σ)⁻¹ * m) +
    (Real.sqrt σ)⁻¹ ^ 2 * (m ^ 2 * δ)

structure BlockControl (m η : ℝ) where
  cutoff : ℝ
  tolerance : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_lt_one : cutoff < 1
  tolerance_pos : 0 < tolerance
  inverse_control : m ^ 2 * ((Real.sqrt cutoff)⁻¹ ^ 2 * (m ^ 2 * tolerance)) ≤ 1 / 2
  trace_control : m * ((m + 1) * rowCorrectionError m cutoff tolerance +
    (cutoff + m ^ 2 * tolerance)) ≤ η ^ 2
  compression_control : m ^ 2 * rowCompressionError m cutoff tolerance < η

lemma exists_blockControl (m : ℝ) (hm : 0 ≤ m) {η : ℝ} (hη : 0 < η) :
    Nonempty (BlockControl m η) := by
  obtain ⟨σ, δ, hσ, hσ1, hδ, hInv, htr, hcomp⟩ := block_tolerances m hm hη
  exact ⟨⟨σ, δ, hσ, hσ1, hδ, hInv, htr, hcomp⟩⟩

lemma rowCompressionError_nonneg {m σ δ : ℝ} (hm : 0 ≤ m) (hδ : 0 ≤ δ) :
    0 ≤ rowCompressionError m σ δ := by
  dsimp [rowCompressionError, rowCorrectionError]
  positivity

variable {I : Type} {D : Type uD} [Fintype I] [CStarAlgebra D] [DecidableEq D]
  [PartialOrder D] [StarOrderedRing D]

theorem raw_spectral_block (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1)
    (K : Finset D) (hK : ∀ x ∈ K, ‖x‖ ≤ 1) {η : ℝ}
    (T : BlockControl (Fintype.card I) η)
    {q : D} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hcomp : ∀ i j, ∀ x ∈ insert 1 K, ∃ α : ℂ,
      ‖q * (star (v i) * x * v j) * q - α • q‖ < T.tolerance / 2) :
    ∃ n : ℕ, n ≤ Fintype.card I ∧ ∃ U : ProjectionRow (Fin n) q, ∃ c : Fin n → ℝ,
      (∀ i, 0 ≤ c i) ∧ (∀ i, c i ≤ 1) ∧ Monotone c ∧
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ ((∑ i, c i • U.atom i) - weightedAverage w v q) ≤
          η ^ 2 * (τ.functional q).re) ∧
      (∀ k : ℕ, ∀ e : Fin k ↪ Fin n, ∀ x ∈ K, ∃ H : Matrix (Fin k) (Fin k) ℂ,
        ‖(U.subrow e).sample q * x * (U.subrow e).sample q - (U.subrow e).matrix q H‖ < η) := by
  classical
  obtain ⟨f, hf, hfq⟩ := exists_state_at_projection hq hq0
  let a := rawRow w v q
  have hscalar (i j : I) (x : D) (hx : x ∈ insert 1 K) :
      ‖rowPair a x i j - f (rowPair a x i j) • q‖ ≤ T.tolerance := by
    have he := rawRow_pair_scalar_error w hw hw1 v hq f hf hfq x i j (hcomp i j x hx)
    linarith
  have hgram (i j : I) : ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ T.tolerance := by
    simpa only [scalarRowGram, rowPair, mul_one] using hscalar i j 1 (Finset.mem_insert_self _ _)
  have htests : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ T.tolerance := by
    intro x hx
    exact ⟨fun i j => f (rowPair a x i j), fun i j => hscalar i j x (Finset.mem_insert_of_mem hx)⟩
  obtain ⟨U, htr, hpair⟩ := spectral_row_block hq f hf a
    (rawRow_support w v hq) (rawRow_norm_squares w hw hw1 v hv hq)
    (Nat.cast_nonneg _) (rawRow_norm_sum w hw hw1 v hv hq) T.cutoff_pos T.tolerance_pos.le
    hgram K htests hK T.inverse_control
  let c := (scalarRowGram_posSemidef f a).isHermitian.eigenvalues
  let J := {i : I // T.cutoff ≤ c i}
  let c' : J → ℝ := fun i => c i
  let e := sortedIndex c'
  let U' := U.sorted c'
  have hn : Fintype.card J ≤ Fintype.card I := Fintype.card_subtype_le _
  have hnR : (Fintype.card J : ℝ) ≤ Fintype.card I := by exact_mod_cast hn
  have heq : ∑ i, c' (e i) • U'.atom i = ∑ i : J, c i • U.atom i :=
    U.sorted_weighted_sum c'
  refine ⟨Fintype.card J, hn, U', c' ∘ e, ?_, ?_, sortedIndex_monotone c', ?_, ?_⟩
  · intro i
    exact (scalarRowGram_posSemidef f a).eigenvalues_nonneg (e i)
  · intro i
    exact scalarRowGram_eigenvalue_le_one f hf a (rawRow_norm_squares w hw hw1 v hv hq) (e i)
  · intro τ
    simp only [Function.comp_apply]
    rw [heq, ← rawRow_covariance w hw v hq]
    exact (htr τ).trans (mul_le_mul_of_nonneg_right T.trace_control
      (τ.functional.map_nonneg hq.nonneg).1)
  · intro k g x hx
    obtain ⟨H, hH⟩ := hpair x hx
    let H' : Matrix (Fin (Fintype.card J)) (Fin (Fintype.card J)) ℂ := H.submatrix e e
    have hp (i j : Fin (Fintype.card J)) :
        ‖rowPair U'.entry x i j - H' i j • q‖ ≤
          rowCompressionError (Fintype.card I) T.cutoff T.tolerance := hH (e i) (e j)
    refine ⟨H'.submatrix g g, ?_⟩
    apply (U'.subrow_compression g x H'
      (rowCompressionError_nonneg (Nat.cast_nonneg _) T.tolerance_pos.le) hp).trans_lt
    apply lt_of_le_of_lt ?_ T.compression_control
    simp only [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (by gcongr)
      (rowCompressionError_nonneg (Nat.cast_nonneg _) T.tolerance_pos.le)

end

variable {D : Type uD} [CStarAlgebra D] {q : D} {n : ℕ}

def upperEmbedding (j : Fin n) :
    Fin (Fintype.card {i : Fin n // j ≤ i}) ↪ Fin n :=
  (Fintype.equivFin {i : Fin n // j ≤ i}).symm.toEmbedding.trans
    (Function.Embedding.subtype (j ≤ ·))

lemma upperColumn_nonempty (j : Fin n) : 0 < Fintype.card {i : Fin n // j ≤ i} := by
  let : Nonempty {i : Fin n // j ≤ i} := ⟨⟨j, le_rfl⟩⟩
  exact Fintype.card_pos

namespace ProjectionRow

omit [CStarAlgebra D] in
lemma sum_pos_weights {I : Type uI} [Fintype I] {E : Type uE}
    [AddCommMonoid E] [Module ℝ E] (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (a : I → E) :
    ∑ i : {i : I // 0 < w i}, w i • a i = ∑ i, w i • a i := by
  classical
  rw [Fintype.sum_subtype_add_sum_subtype (p := fun i => 0 < w i) (fun i => w i • a i) |>.symm]
  have hz : (∑ i : {i : I // ¬0 < w i}, w i • a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [le_antisymm (le_of_not_gt i.property) (hw i), zero_smul]
  rw [hz, add_zero]

variable (U : ProjectionRow (Fin n) q)

lemma upperEmbedding_range (j : Fin n) :
    (U.subrow (upperEmbedding j)).sample q = upperLayerCut U.atom j := by
  rw [U.subrow_range, U.upper_cut_subrow, U.subrow_range]
  exact (Fintype.equivFin {i : Fin n // j ≤ i}).symm.sum_comp
    (fun i => U.atom i.val)

lemma positive_layer_sum (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (hm : Monotone c) :
    ∑ j : {j : Fin n // 0 < orderedLayerWeights c j},
      orderedLayerWeights c j • (U.subrow (upperEmbedding j)).sample q =
        ∑ i, c i • U.atom i := by
  simp_rw [U.upperEmbedding_range]
  rw [sum_pos_weights (orderedLayerWeights c) (orderedLayerWeights_nonneg c hc hm)]
  exact U.layer_sum c

variable [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing D] in
lemma positive_layer_energy (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (hm : Monotone c)
    (τ : Pureness.TracialState D) (x : D) :
    ∑ j : {j : Fin n // 0 < orderedLayerWeights c j}, orderedLayerWeights c j *
      traceTwoNorm τ (x * (U.subrow (upperEmbedding j)).sample q -
        (U.subrow (upperEmbedding j)).sample q * x) ^ 2 =
      ∑ j, orderedLayerWeights c j * traceTwoNorm τ
        (x * upperLayerCut U.atom j - upperLayerCut U.atom j * x) ^ 2 := by
  simp_rw [U.upperEmbedding_range]
  simpa only [smul_eq_mul] using
    sum_pos_weights (orderedLayerWeights c) (orderedLayerWeights_nonneg c hc hm)
      (fun j => traceTwoNorm τ (x * upperLayerCut U.atom j - upperLayerCut U.atom j * x) ^ 2)

end ProjectionRow

end CurrentMain

end

end OAI
