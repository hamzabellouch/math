import OAI.Analysis.TracialSplitting.PartitionAveraging

namespace OAI

universe uD uI uJ


section

noncomputable section

namespace CurrentMain

open scoped ComplexOrder

section Bistochastic

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [DecidableEq I] in
lemma kraus_coefficient_norm (v : I → D) (hv : ∑ i, star (v i)*v i = 1) (i : I) :
    ‖v i‖ ≤ 1 := by
  have hle : star (v i)*v i ≤ 1 := by
    rw [← hv]
    exact Finset.single_le_sum (fun j _ => star_mul_self_nonneg (v j)) (Finset.mem_univ i)
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg (v i))).mpr hle
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (v i)]

lemma scalarRowGram_eigenvalue_le_of_trace (f : D →ₚ[ℂ] ℂ) (a : I → D)
    (ha : ((scalarRowGram f a).trace).re ≤ 1) (i : I) :
    (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1 := by
  let hG := scalarRowGram_posSemidef f a
  have he : ∑ j, hG.isHermitian.eigenvalues j = ((scalarRowGram f a).trace).re := by
    rw [hG.isHermitian.trace_eq_sum_eigenvalues,Complex.re_sum]
    exact Finset.sum_congr rfl (fun j _ => rfl)
  exact (Finset.single_le_sum (fun j _ => hG.eigenvalues_nonneg j)
    (Finset.mem_univ i)).trans (he ▸ ha)

omit [DecidableEq I] [StarOrderedRing D] in
lemma scalarRowGram_kraus_trace (f : D →ₚ[ℂ] ℂ) (v : I → D)
    (hv : ∑ i, star (v i)*v i = 1) {q : D} (hq : IsStarProjection q)
    (hfq : f q = 1) :
    ((scalarRowGram f (fun i => v i*q)).trace).re = 1 := by
  have hs : ∑ i, star (v i*q)*(v i*q) = q := by
    simp only [star_mul,hq.isSelfAdjoint.star_eq,mul_assoc]
    simp only [← mul_assoc (star _) _ _,← Finset.sum_mul,← Finset.mul_sum,hv,
      one_mul,hq.isIdempotentElem.eq]
  simp only [Matrix.trace,Matrix.diag,scalarRowGram,← map_sum,hs,hfq,Complex.one_re]

theorem spectral_row_block_of_spectral_bound {q : D} (hq : IsStarProjection q)
    (f : D →ₚ[ℂ] ℂ) (a : I → D)
    (haq : ∀ i, a i * q = a i)
    (hcs : ∀ i, (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1)
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
  have hc1 (i : I) : c i ≤ 1 := hcs i
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
      (inv_le_inv₀ (Real.sqrt_pos.mpr (hσ.trans_le i.property))
        (Real.sqrt_pos.mpr hσ)).mpr (Real.sqrt_le_sqrt i.property)
    refine ⟨fun i j => (r i * r j) • H' i j, fun i j => ?_⟩
    apply normalized_rowPair_error U (fun i => b i) r x (hKn x hx)
      (fun i j => H' i j) hr (by positivity) hrL (fun i => hbn i) hU
    exact fun i j => rowPair_rotate_error a Z x H hH i j

end Bistochastic

section RawKraus

variable {I : Type} {D : Type uD} [Fintype I] [CStarAlgebra D] [DecidableEq D]
  [PartialOrder D] [StarOrderedRing D]

theorem raw_kraus_spectral_block (v : I → D) (hv : ∑ i, star (v i)*v i = 1)
    (K : Finset D) (hK : ∀ x ∈ K, ‖x‖ ≤ 1) {η : ℝ}
    (T : BlockControl (Fintype.card I) η)
    {q : D} (hq : IsStarProjection q) (hq0 : q ≠ 0)
    (hcomp : ∀ i j, ∀ x ∈ insert 1 K, ∃ α : ℂ,
      ‖q * (star (v i) * x * v j) * q - α • q‖ < T.tolerance / 2) :
    ∃ n : ℕ, n ≤ Fintype.card I ∧ ∃ U : ProjectionRow (Fin n) q, ∃ c : Fin n → ℝ,
      (∀ i, 0 ≤ c i) ∧ (∀ i, c i ≤ 1) ∧ Monotone c ∧
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ ((∑ i, c i • U.atom i) - weightedAverage (fun _ => 1) v q) ≤
          η ^ 2 * (τ.functional q).re) ∧
      (∀ k : ℕ, ∀ e : Fin k ↪ Fin n, ∀ x ∈ K, ∃ H : Matrix (Fin k) (Fin k) ℂ,
        ‖(U.subrow e).sample q * x * (U.subrow e).sample q - (U.subrow e).matrix q H‖ < η) := by
  classical
  obtain ⟨f, hf, hfq⟩ := exists_state_at_projection hq hq0
  let a : I → D := fun i => v i*q
  have hcs (i : I) : (scalarRowGram_posSemidef f a).isHermitian.eigenvalues i ≤ 1 :=
    scalarRowGram_eigenvalue_le_of_trace f a
      (scalarRowGram_kraus_trace f v hv hq hfq).le i
  have ha (i : I) : ‖a i‖ ≤ 1 := by
    exact (norm_mul_le _ _).trans
      ((mul_le_mul (kraus_coefficient_norm v hv i) hq.norm_le
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hasum : ∑ i, ‖a i‖ ≤ Fintype.card I := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ha i)
  have hscalar (i j : I) (x : D) (hx : x ∈ insert 1 K) :
      ‖rowPair a x i j - f (rowPair a x i j) • q‖ ≤ T.tolerance := by
    obtain ⟨c,hc⟩ := hcomp i j x hx
    have he := state_scalar_error f hf hq hfq (q * (star (v i)*x*v j)*q) c
    have hrow : rowPair a x i j = q * (star (v i)*x*v j)*q := by
      simp only [rowPair,a,star_mul,hq.isSelfAdjoint.star_eq,mul_assoc]
    rw [hrow]
    linarith
  have hgram (i j : I) : ‖rowPair a 1 i j - scalarRowGram f a i j • q‖ ≤ T.tolerance := by
    simpa only [scalarRowGram, rowPair, mul_one] using hscalar i j 1 (Finset.mem_insert_self _ _)
  have htests : ∀ x ∈ K, ∃ H : Matrix I I ℂ,
      ∀ i j, ‖rowPair a x i j - H i j • q‖ ≤ T.tolerance := by
    intro x hx
    exact ⟨fun i j => f (rowPair a x i j), fun i j => hscalar i j x (Finset.mem_insert_of_mem hx)⟩
  obtain ⟨U, htr, hpair⟩ := spectral_row_block_of_spectral_bound hq f a
    (fun i => by simp only [a,mul_assoc,hq.isIdempotentElem.eq]) hcs
    (Nat.cast_nonneg _) hasum T.cutoff_pos T.tolerance_pos.le
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
    exact hcs (e i)
  · intro τ
    simp only [Function.comp_apply]
    have hav : weightedAverage (fun _ : I => (1 : ℝ)) v q = ∑ i, a i*star (a i) := by
      simp only [weightedAverage,one_smul,a,star_mul,hq.isSelfAdjoint.star_eq,
        mul_assoc,← mul_assoc q q,hq.isIdempotentElem.eq]
    rw [heq,hav]
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

end RawKraus

section GlobalEnergy

variable {D : Type uD} {J : Type uJ} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Fintype J]

theorem layer_energy_global (τ : Pureness.TracialState D)
    (n : J → ℕ) (e : (j : J) → Fin (n j) → D)
    (he : ∀ j i, IsStarProjection (e j i))
    (ho : ∀ j, Pairwise (fun i k => e j i * e j k = 0))
    (c : (j : J) → Fin (n j) → ℝ) (hc : ∀ j i, 0 ≤ c j i)
    (hm : ∀ j, Monotone (c j)) (x : unitary D)
    (h : J → D) (hh : ∀ j, 0 ≤ h j) {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hclose : ∑ j, traceOneNorm τ ((∑ i, c j i • e j i) - h j) ≤ η^2)
    (hmass : ∑ j, (τ.functional (h j)).re ≤ 1)
    (hcentral : ∑ j, traceOneNorm τ (h j - (x : D)*h j*star (x : D)) ≤ η^2) :
    ∑ j, ∑ i, orderedLayerWeights (c j) i * traceTwoNorm τ
      ((x : D)*upperLayerCut (e j) i - upperLayerCut (e j) i*(x : D))^2 ≤ 6*η := by
  classical
  let b : J → D := fun j => ∑ i, c j i • e j i
  let E : J → ℝ := fun j => ∑ i, orderedLayerWeights (c j) i * traceTwoNorm τ
    ((x : D)*upperLayerCut (e j) i - upperLayerCut (e j) i*(x : D))^2
  let m : J → ℝ := fun j => (τ.functional (b j)).re
  let d : J → ℝ := fun j => traceOneNorm τ (b j - (x : D)*b j*star (x : D))
  have hb (j) : 0 ≤ b j := projection_combination_nonneg (e j) (he j) (c j) (hc j)
  have hmn (j) : 0 ≤ m j := (τ.functional.map_nonneg (hb j)).1
  have hdn (j) : 0 ≤ d j := traceOneNorm_nonneg τ _
  have hEn (j) : 0 ≤ E j := Finset.sum_nonneg fun i _ =>
    mul_nonneg (orderedLayerWeights_nonneg (c j) (hc j) (hm j) i) (sq_nonneg _)
  have hmb : ∑ j, m j ≤ 1+η^2 := by
    have hz := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      trace_mass_perturb τ (hb j).isSelfAdjoint (hh j).isSelfAdjoint
        (le_refl (traceOneNorm τ (b j-h j))) (le_refl (τ.functional (h j)).re)
    dsimp only [m]
    simp only [Finset.sum_add_distrib] at hz
    exact hz.trans (add_le_add hmass hclose)
  have hdb : ∑ j, d j ≤ 3*η^2 := by
    have hz := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      trace_central_perturb τ (hb j).isSelfAdjoint (hh j).isSelfAdjoint x
        (le_refl (traceOneNorm τ (b j-h j)))
        (le_refl (traceOneNorm τ (h j-(x : D)*h j*star (x : D))))
    change (∑ j, d j) ≤ _ at hz
    simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hz
    linarith
  have hEsq (j) : (E j)^2 ≤ (4*m j)*d j := by
    have hl := layer_energy_le_of_orthogonal τ (e j) (he j) (ho j)
      (orderedLayerWeights (c j)) (orderedLayerWeights_nonneg (c j) (hc j) (hm j)) x
    have hs : ∑ i, orderedLayerWeights (c j) i • upperLayerCut (e j) i = b j := by
      rw [layer_decomposition]
      simp only [layerCoefficient_orderedLayerWeights]
      rfl
    rw [hs] at hl
    change E j ≤ 2*Real.sqrt (m j*d j) at hl
    have hsq := Real.sq_sqrt (mul_nonneg (hmn j) (hdn j))
    nlinarith [hEn j, Real.sqrt_nonneg (m j*d j)]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hmn j))
    (fun j _ => hdn j) (fun j _ => hEsq j)
  rw [← Finset.mul_sum] at hCS
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hmb (by norm_num : (0 : ℝ) ≤ 4))
    hdb (Finset.sum_nonneg (fun j _ => hdn j)) (by positivity : 0 ≤ 4*(1+η^2))
  have hηsq : η^2 ≤ 1 := by nlinarith
  have hbound : 4*(1+η^2)*(3*η^2) ≤ (6*η)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hηsq (sq_nonneg η)]
  have ht := hCS.trans (hprod.trans hbound)
  change (∑ j, E j) ≤ 6*η
  nlinarith

end GlobalEnergy

section KrausFamily

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [StarOrderedRing D] in
lemma kraus_average_trace {I : Type uI} [Fintype I] (τ : Pureness.TracialState D)
    (v : I → D) (hv : ∑ i, star (v i)*v i = 1) (q : D) :
    τ.functional (weightedAverage (fun _ : I => (1 : ℝ)) v q) = τ.functional q := by
  simp only [weightedAverage,one_smul,map_sum]
  calc
    _ = ∑ i, τ.functional ((star (v i)*v i)*q) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [τ.tracial (v i*q),← mul_assoc]
    _ = τ.functional q := by rw [← map_sum,← Finset.sum_mul,hv,one_mul]

theorem weighted_family_of_kraus_average {I : Type} [Fintype I]
    (hRR : RealRankZero D) (v : I → D) (hv : ∑ i, star (v i)*v i = 1)
    (K : Finset (unitary D)) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    {r : D} (hr : IsStarProjection r)
    (hcentral : ∀ P : ProjectionPartition r, ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
      ∑ s, traceOneNorm τ (weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) -
        (x : D) * weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) * star (x : D)) ≤ η^2) :
    ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j * (x : D) * F.range j - (F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage (fun _ : I => (1 : ℝ)) v r) ≤ η ^ 2) ∧
      (∀ x ∈ K, ∀ τ : Pureness.TracialState D,
        ∑ j, F.weight j * traceTwoNorm τ ((x : D) * F.range j - F.range j * (x : D)) ^ 2 ≤
          6 * η) := by
  classical
  obtain ⟨T⟩ := exists_blockControl (Fintype.card I) (Nat.cast_nonneg _) hη
  let K' : Finset D := K.image (fun x : unitary D => (x : D))
  let tests : Finset D := Finset.univ.biUnion fun i : I =>
    Finset.univ.biUnion fun j : I => (insert 1 K').image (fun x => star (v i) * x * v j)
  obtain ⟨P, hP⟩ := scalar_compressions hRR hr tests (half_pos T.tolerance_pos)
  have hcompression (s : P.Index) (i j : I) (x : D) (hx : x ∈ insert 1 K') :
      ∃ α : ℂ, ‖P.piece s * (star (v i) * x * v j) * P.piece s - α • P.piece s‖ <
        T.tolerance / 2 := by
    apply hP _ _ s
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩⟩
  have hK' (x : D) (hx : x ∈ K') : ‖x‖ ≤ 1 := by
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have hu := CStarRing.norm_coe_unitary_mul u (1 : D)
    rw [mul_one] at hu
    exact hu.le.trans (IsStarProjection.one D).norm_le
  choose n hn U c hc hc1 hmono htr hpair using fun s =>
    raw_kraus_spectral_block v hv K' hK' T (P.isProjection s) (P.nonzero s) (hcompression s)
  let J := Σ s : P.Index, {j : Fin (n s) // 0 < orderedLayerWeights (c s) j}
  let F : WeightedBlockFamily r := {
    Index := J
    weight := fun a => orderedLayerWeights (c a.1) a.2
    weight_pos := fun a => a.2.property
    weight_le_one := fun a => (orderedLayerWeights_le (c a.1) (hc a.1) a.2).trans (hc1 a.1 a.2)
    base := fun a => P.piece a.1
    baseProjection := fun a => P.isProjection a.1
    base_nonzero := fun a => P.nonzero a.1
    base_le := fun a => P.piece_le hr a.1
    columns := fun a => Fintype.card {i : Fin (n a.1) // a.2.val ≤ i}
    columns_pos := fun a => upperColumn_nonempty a.2.val
    row := fun a => (U a.1).subrow (upperEmbedding a.2.val) }
  have hFsum : F.weightedSum = ∑ s, ∑ i, c s i • (U s).atom i := by
    change (∑ a : J, orderedLayerWeights (c a.1) a.2 •
      ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1)) = _
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun s _ => (U s).positive_layer_sum (c s) (hc s) (hmono s)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro j x hx
    exact hpair j.1 _ (upperEmbedding j.2.val) (x : D) (Finset.mem_image_of_mem _ hx)
  · intro τ
    have hav : weightedAverage (fun _ : I => (1 : ℝ)) v r = ∑ s, weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s) := by
      calc
        _ = weightedAverage (fun _ : I => (1 : ℝ)) v (∑ s, P.piece s) := congrArg (weightedAverage (fun _ : I => (1 : ℝ)) v) P.sum_eq.symm
        _ = _ := weightedAverage_sum (fun _ : I => (1 : ℝ)) v P.piece
    rw [hFsum, hav, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s, traceOneNorm τ ((∑ i, c s i • (U s).atom i) - weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s)) :=
        traceOneNorm_sum_le τ _ fun s =>
          (projection_combination_nonneg (U s).atom (U s).atom_projection (c s) (hc s)).isSelfAdjoint.sub
            (weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one) (P.isProjection s).nonneg).isSelfAdjoint
      _ ≤ ∑ s, η ^ 2 * (τ.functional (P.piece s)).re := Finset.sum_le_sum fun s _ => htr s τ
      _ = η ^ 2 * (τ.functional r).re := by rw [← Finset.mul_sum, ← Complex.re_sum, ← map_sum, P.sum_eq]
      _ ≤ η ^ 2 := by
        have ht := trace_projection_le_one τ hr
        nlinarith [sq_nonneg η]
  · intro x hx τ
    change (∑ a : J, orderedLayerWeights (c a.1) a.2 * traceTwoNorm τ
      ((x : D) * ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1) -
        ((U a.1).subrow (upperEmbedding a.2.val)).sample (P.piece a.1) * (x : D)) ^ 2) ≤ _
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ s, ∑ j, orderedLayerWeights (c s) j * traceTwoNorm τ
          ((x : D) * upperLayerCut (U s).atom j - upperLayerCut (U s).atom j * (x : D)) ^ 2 :=
        Finset.sum_congr rfl fun s _ => (U s).positive_layer_energy (c s) (hc s) (hmono s) τ x
      _ ≤ 6*η := by
        apply layer_energy_global τ n (fun s => (U s).atom)
          (fun s => (U s).atom_projection) (fun s => (U s).atom_orthogonal)
          c hc hmono x (fun s => weightedAverage (fun _ : I => (1 : ℝ)) v (P.piece s))
          (fun s => weightedAverage_nonneg (fun _ : I => (1 : ℝ)) v (fun _ => zero_le_one)
            (P.isProjection s).nonneg) hη.le hη1.le
        · calc
            _ ≤ ∑ s, η^2*(τ.functional (P.piece s)).re := Finset.sum_le_sum fun s _ => htr s τ
            _ = η^2*(τ.functional r).re := by
              rw [← Finset.mul_sum,← Complex.re_sum,← map_sum,P.sum_eq]
            _ ≤ η^2 := by
              have ht := trace_projection_le_one τ hr
              nlinarith [sq_nonneg η]
        · simp only [kraus_average_trace τ v hv]
          rw [← Complex.re_sum,← map_sum,P.sum_eq]
          exact trace_projection_le_one τ hr
        · exact hcentral P x hx τ

end KrausFamily

end CurrentMain

end

end

end OAI
