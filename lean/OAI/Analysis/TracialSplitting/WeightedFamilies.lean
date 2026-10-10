import OAI.Analysis.TracialSplitting.SpectralBlocks

namespace OAI

universe uD uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure WeightedBlockFamily (r : D) where
  Index : Type
  [indexFintype : Fintype Index]
  weight : Index → ℝ
  weight_pos : ∀ j, 0 < weight j
  weight_le_one : ∀ j, weight j ≤ 1
  base : Index → D
  baseProjection : ∀ j, IsStarProjection (base j)
  base_nonzero : ∀ j, base j ≠ 0
  base_le : ∀ j, base j ≤ r
  columns : Index → ℕ
  columns_pos : ∀ j, 0 < columns j
  row : ∀ j, ProjectionRow (Fin (columns j)) (base j)

attribute [instance] WeightedBlockFamily.indexFintype

namespace WeightedBlockFamily

variable {r : D} (F : WeightedBlockFamily r)

def range (j : F.Index) : D := (F.row j).sample (F.base j)

def weightedSum : D := ∑ j, F.weight j • F.range j

omit [StarOrderedRing D] in
lemma range_projection (j : F.Index) : IsStarProjection (F.range j) :=
  (F.row j).range_projection

lemma weightedSum_nonneg : 0 ≤ F.weightedSum :=
  projection_combination_nonneg F.range F.range_projection F.weight
    (fun j => (F.weight_pos j).le)

end WeightedBlockFamily

omit [PartialOrder D] [StarOrderedRing D] in
lemma weightedAverage_sum {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (w : I → ℝ) (v : I → D) (a : J → D) :
    weightedAverage w v (∑ j, a j) = ∑ j, weightedAverage w v (a j) := by
  simp only [weightedAverage, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  exact Finset.sum_comm

lemma weightedAverage_mass_upper {I : Type uI} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1) {q : D} (hq : IsStarProjection q)
    (τ : Pureness.TracialState D) :
    (τ.functional (weightedAverage w v q)).re ≤ (τ.functional q).re :=
  (weightedAverage_mass τ w v hw hw1 hv hq
    (lt_add_one ‖1 - weightedAverage w v 1‖)).2

theorem weighted_family_of_average {I : Type} [Fintype I]
    (hRR : RealRankZero D) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1)
    (K : Finset (unitary D)) {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hcentral : ∀ q : D, IsStarProjection q → ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
      traceOneNorm τ (weightedAverage w v q - (x : D) * weightedAverage w v q * star (x : D)) ≤
        η ^ 2 * (τ.functional q).re)
    {r : D} (hr : IsStarProjection r) :
    ∃ F : WeightedBlockFamily r,
      (∀ j, ∀ x ∈ K, ∃ H : Matrix (Fin (F.columns j)) (Fin (F.columns j)) ℂ,
        ‖F.range j * (x : D) * F.range j - (F.row j).matrix (F.base j) H‖ < η) ∧
      (∀ τ : Pureness.TracialState D,
        traceOneNorm τ (F.weightedSum - weightedAverage w v r) ≤ η ^ 2) ∧
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
    raw_spectral_block w hw hw1 v hv K' hK' T (P.isProjection s) (P.nonzero s) (hcompression s)
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
    have hav : weightedAverage w v r = ∑ s, weightedAverage w v (P.piece s) := by
      calc
        _ = weightedAverage w v (∑ s, P.piece s) := congrArg (weightedAverage w v) P.sum_eq.symm
        _ = _ := weightedAverage_sum w v P.piece
    rw [hFsum, hav, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ s, traceOneNorm τ ((∑ i, c s i • (U s).atom i) - weightedAverage w v (P.piece s)) :=
        traceOneNorm_sum_le τ _ fun s =>
          (projection_combination_nonneg (U s).atom (U s).atom_projection (c s) (hc s)).isSelfAdjoint.sub
            (weightedAverage_nonneg w v hw (P.isProjection s).nonneg).isSelfAdjoint
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
      _ ≤ ∑ s, 6 * η * (τ.functional (P.piece s)).re := by
        apply Finset.sum_le_sum
        intro s _
        exact layer_energy_perturb τ (U s).atom (U s).atom_projection (U s).atom_orthogonal
          (c s) (hc s) (hmono s) x (weightedAverage_nonneg w v hw (P.isProjection s).nonneg)
          hη.le hη1.le (τ.functional.map_nonneg (P.isProjection s).nonneg).1 (htr s τ)
          (weightedAverage_mass_upper w hw hw1 v hv (P.isProjection s) τ)
          (hcentral _ (P.isProjection s) x hx τ)
      _ = 6 * η * (τ.functional r).re := by rw [← Finset.mul_sum, ← Complex.re_sum, ← map_sum, P.sum_eq]
      _ ≤ 6 * η := by
        have ht := trace_projection_le_one τ hr
        nlinarith

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I] {q : D}

namespace ProjectionRow

variable (U : ProjectionRow I q)

def overlapTest (z : D) : D := ∑ i, star (U.entry i) * z * U.entry i

omit [StarOrderedRing D] in
lemma trace_overlap_sample (τ : Pureness.TracialState D) (z a : D) :
    τ.functional (z * U.sample a) = τ.functional (a * U.overlapTest z) := by
  simp only [sample, coeff, overlapTest, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show z * (U.entry i * a * star (U.entry i)) =
    (z * U.entry i) * (a * star (U.entry i)) by noncomm_ring, τ.tracial]
  congr 1
  noncomm_ring

theorem sample_mass_overlap (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    (z : D) {c ε : ℝ} (hc : c ∈ Set.Icc 0 1) (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ τ : Pureness.TracialState D,
      ‖τ.functional (U.sample e) - (c : ℂ) * τ.functional (U.sample q)‖ < ε ∧
      ‖τ.functional (z * U.sample e) - (c : ℂ) * τ.functional (z * U.sample q)‖ < ε := by
  classical
  let k : ℝ := Fintype.card I
  let δ := ε / (k + 1)
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδeq : δ * (k + 1) = ε := div_mul_cancel₀ _ (ne_of_gt (by positivity))
  have hkδ : k * δ < ε := by nlinarith
  have hδε : δ ≤ ε := by nlinarith
  obtain ⟨e, he, heq, htest⟩ := split_finite_linear_tests hRR hsmall U.projection hc
    {1, U.overlapTest z} hδ
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  refine ⟨e, he, heq, ?_⟩
  intro τ
  constructor
  · have hmass := htest 1 (Finset.mem_insert_self _ _) τ
    simp only [mul_one] at hmass
    rw [U.trace_sample τ e heq', U.trace_sample τ q U.projection.isIdempotentElem]
    rw [show (Fintype.card I : ℂ) * τ.functional e -
      (c : ℂ) * ((Fintype.card I : ℂ) * τ.functional q) =
      (Fintype.card I : ℂ) * (τ.functional e - (c : ℂ) * τ.functional q) by ring,
      norm_mul, Complex.norm_natCast]
    exact (mul_le_mul_of_nonneg_left hmass.le hk).trans_lt hkδ
  · rw [U.trace_overlap_sample, U.trace_overlap_sample]
    exact (htest _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) τ).trans_le hδε

end ProjectionRow

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sub_le (τ : Pureness.TracialState D) (a b : D) :
    traceTwoNorm τ (a - b) ≤ traceTwoNorm τ a + traceTwoNorm τ b := by
  simpa only [sub_eq_add_neg, traceTwoNorm_neg] using traceTwoNorm_add_le τ a (-b)

lemma traceTwoNorm_sum_le {I : Type uI} (s : Finset I) (τ : Pureness.TracialState D) (a : I → D) :
    traceTwoNorm τ (∑ i ∈ s, a i) ≤ ∑ i ∈ s, traceTwoNorm τ (a i) := by
  simpa only [traceTwoNorm_eq_gns, map_sum] using norm_sum_le s (fun i => τ.functional.toPreGNS (a i))

lemma traceTwoNorm_commutator_le (τ : Pureness.TracialState D) {x : D} (hx : ‖x‖ ≤ 1) (a : D) :
    traceTwoNorm τ (x * a - a * x) ≤ 2 * traceTwoNorm τ a := by
  have h0 := traceTwoNorm_nonneg τ a
  calc
    _ ≤ traceTwoNorm τ (x * a) + traceTwoNorm τ (a * x) := traceTwoNorm_sub_le τ _ _
    _ ≤ ‖x‖ * traceTwoNorm τ a + ‖x‖ * traceTwoNorm τ a :=
      add_le_add (traceTwoNorm_mul_left τ _ _) (traceTwoNorm_mul_right τ _ _)
    _ ≤ _ := by nlinarith

lemma commutator_perturb_sq (τ : Pureness.TracialState D) {x : D} (hx : ‖x‖ ≤ 1) (t y : D) :
    traceTwoNorm τ (x * t - t * x) ^ 2 ≤
      2 * traceTwoNorm τ (x * y - y * x) ^ 2 + 8 * traceTwoNorm τ (t - y) ^ 2 := by
  have he : x * t - t * x = (x * y - y * x) + (x * (t - y) - (t - y) * x) := by noncomm_ring
  have hb : traceTwoNorm τ (x * t - t * x) ≤
      traceTwoNorm τ (x * y - y * x) + 2 * traceTwoNorm τ (t - y) := by
    rw [he]
    exact (traceTwoNorm_add_le τ _ _).trans
      (add_le_add le_rfl (traceTwoNorm_commutator_le τ hx _))
  have h0 := traceTwoNorm_nonneg τ (x * t - t * x)
  have h1 := traceTwoNorm_nonneg τ (x * y - y * x)
  have h2 := traceTwoNorm_nonneg τ (t - y)
  nlinarith [sq_nonneg (traceTwoNorm τ (x * y - y * x) - 2 * traceTwoNorm τ (t - y))]

lemma projection_overlap_identity (τ : Pureness.TracialState D) {z r : D}
    (hz : IsStarProjection z) (hr : IsStarProjection r) (v : D) :
    (τ.functional (z * (v * r * star v))).re = traceTwoNorm τ (z * v * r) ^ 2 := by
  rw [traceTwoNorm_sq]
  simp only [star_mul, hz.isSelfAdjoint.star_eq, hr.isSelfAdjoint.star_eq,
    mul_assoc, ← mul_assoc z z, hz.isIdempotentElem.eq]
  have he : τ.functional (r * (star v * (z * (v * r)))) =
      τ.functional (z * (v * r * star v)) := by
    calc
      _ = τ.functional ((star v * (z * v)) * (r * r)) := by
        rw [τ.tracial r]
        congr 1
        noncomm_ring
      _ = τ.functional (star v * (z * (v * r))) := by
        rw [hr.isIdempotentElem.eq]
        congr 1
        noncomm_ring
      _ = _ := by
        rw [τ.tracial (star v)]
        congr 1
        noncomm_ring
  simpa only [mul_assoc] using congrArg Complex.re he.symm

lemma weightedAverage_overlap {I : Type uI} [Fintype I]
    (τ : Pureness.TracialState D) (w : I → ℝ) (v : I → D)
    {z r : D} (hz : IsStarProjection z) (hr : IsStarProjection r) :
    (τ.functional (z * weightedAverage w v r)).re =
      ∑ i, w i * traceTwoNorm τ (z * v i * r) ^ 2 := by
  simp only [weightedAverage, Finset.mul_sum, mul_smul_comm, map_sum,
    τ.functional.map_smul_of_tower, Complex.re_sum, Complex.smul_re, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => congrArg (w i * ·) (projection_overlap_identity τ hz hr (v i))

lemma weightedAverage_overlap_le {I : Type uI} [Fintype I]
    (τ : Pureness.TracialState D) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (v : I → D) {z : D} (hz : IsStarProjection z) {E : ℝ}
    (henergy : ∀ i, traceTwoNorm τ (z * v i - v i * z) ^ 2 ≤ E) :
    (τ.functional (z * weightedAverage w v (1 - z))).re ≤ E := by
  rw [weightedAverage_overlap τ w v hz hz.one_sub]
  have hb (i : I) : traceTwoNorm τ (z * v i * (1 - z)) ^ 2 ≤ E := by
    have he : z * v i * (1 - z) = (z * v i - v i * z) * (1 - z) := by
      noncomm_ring [hz.isIdempotentElem.eq]
    have hn : traceTwoNorm τ (z * v i * (1 - z)) ≤ traceTwoNorm τ (z * v i - v i * z) := by
      rw [he]
      apply (traceTwoNorm_mul_right τ _ _).trans
      exact (mul_le_mul_of_nonneg_right hz.one_sub.norm_le (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _)
    exact (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _) |>.mpr hn).trans (henergy i)
  calc
    _ ≤ ∑ i, w i * E := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i)
    _ = E := by rw [← Finset.sum_mul, hw1, one_mul]

lemma unitary_coefficient_tests {I : Type uI} [Fintype I] (v : I → D) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ L : Finset (unitary D), ∀ z : D, ∀ τ : Pureness.TracialState D, ∀ E : ℝ, 0 ≤ E →
      (∀ x ∈ L, traceTwoNorm τ (z * (x : D) - (x : D) * z) ^ 2 ≤ E) →
      ∀ i, traceTwoNorm τ (z * v i - v i * z) ^ 2 ≤ 4 * E := by
  classical
  choose u c he hc using fun i => CStarAlgebra.exists_sum_four_unitary (v i)
  let L := Finset.univ.biUnion fun i : I => Finset.univ.image (u i)
  refine ⟨L, ?_⟩
  intro z τ E hE ht i
  have hub (j : Fin 4) : traceTwoNorm τ (z * (u i j : D) - (u i j : D) * z) ≤ Real.sqrt E :=
    (Real.le_sqrt (traceTwoNorm_nonneg τ _) hE).mpr
      (ht _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩))
  have hdecomp : z * v i - v i * z =
      ∑ j, c i j • (z * (u i j : D) - (u i j : D) * z) := by
    rw [he i, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [mul_smul_comm, smul_mul_assoc, smul_sub]
  have hn : traceTwoNorm τ (z * v i - v i * z) ≤ 2 * Real.sqrt E := by
    rw [hdecomp]
    apply (traceTwoNorm_sum_le _ τ _).trans
    simp_rw [traceTwoNorm_smul]
    calc
      _ ≤ ∑ j : Fin 4, (1 / 2 : ℝ) * Real.sqrt E := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul ((hc i j).trans (by linarith [hv i])) (hub j)
          (traceTwoNorm_nonneg τ _) (by norm_num)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hsq := (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (by positivity : 0 ≤ 2 * Real.sqrt E)).mpr hn
  rw [mul_pow, Real.sq_sqrt hE] at hsq
  norm_num at hsq ⊢
  exact hsq

end CurrentMain

end

end OAI
