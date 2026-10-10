import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.PinnedEntropy

namespace OAI

/-! Compact spectral coordinates, attained maxima and positive output norms. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator
open Spectral

section CompactSpectralCoordinates
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma compact_unitary_coordinates : CompactSpace (unitary (Matrix n n ℂ)) := by
  have hc : IsCompact (unitary (Matrix n n ℂ) : Set (Matrix n n ℂ)) := by
    apply Metric.isCompact_iff_isClosed_bounded.mpr
    refine ⟨isClosed_unitary, ?_⟩
    apply (Metric.isBounded_closedBall (x := (0 : Matrix n n ℂ)) (r := 1)).subset
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (CStarRing.norm_coe_unitary ⟨u, hu⟩)
  exact isCompact_iff_compactSpace.mp hc

abbrev SpectralCoordinate (n : Type*) [Fintype n] [DecidableEq n] :=
  unitary (Matrix n n ℂ) ×
    {weights : n → ℝ // (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

omit [Nonempty n] [DecidableEq n] in
lemma compact_weight_coordinates :
    CompactSpace {weights : n → ℝ //
      (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} := by
  apply (isCompact_iff_compactSpace (s :=
    {weights : n → ℝ | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1})).mp
  have hset : {weights : n → ℝ | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} =
      Set.range (fun point : Convexity.StdSimplex ℝ n => (point.weights : n → ℝ)) := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext weights
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact isCompact_range (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ n).continuous

def coordinateMatrix (a : ℝ) (p : SpectralCoordinate n) : Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ p.1 (Matrix.diagonal (fun i => ((p.2.val i) ^ (a/2) : ℝ)))

omit [Nonempty n] in
lemma coordinateMatrix_positive (a : ℝ) (p : SpectralCoordinate n) :
    (coordinateMatrix a p).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact_mod_cast Real.rpow_nonneg (p.2.property.1 i) (a/2)

omit [Nonempty n] in
lemma coordinateMatrix_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (coordinateMatrix (n := n) a) := by
  unfold coordinateMatrix Unitary.conjStarAlgAut
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_subtype_val.comp continuous_fst
    · apply continuous_matrix
      intro i k
      by_cases h : i = k
      · subst k
        simp only [Matrix.diagonal_apply_eq]
        exact Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by linarith : 0 ≤ a/2)).comp
          ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
      · simp only [Matrix.diagonal_apply_ne _ h]
        exact continuous_const
  · exact (continuous_subtype_val.comp continuous_fst).star

omit [Nonempty n] in
lemma diagonal_eigenvalue_sum (x : n → ℝ)
    (h : (Matrix.diagonal (fun i => (x i : ℂ))).IsHermitian) (f : ℝ → ℝ) :
    (∑ i, f (h.eigenvalues i)) = ∑ i, f (x i) := by
  have hr := h.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod] at hr
  · simp only [Polynomial.roots_X_sub_C] at hr
    have he := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum) hr
    simpa only [Multiset.map_bind, Multiset.bind_map, Multiset.map_singleton,
      Multiset.bind_singleton, Multiset.map_map, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re, Finset.sum_eq_multiset_sum] using he.symm
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

omit [Nonempty n] in
lemma coordinateMatrix_tracePower (a : ℝ) (ha : 0 < a) (p : SpectralCoordinate n) :
    (∑ i, Real.rpow ((coordinateMatrix_positive a p).isHermitian.eigenvalues i) (2/a)) = 1 := by
  let D : Matrix n n ℂ := Matrix.diagonal (fun i => (((p.2.val i) ^ (a/2) : ℝ) : ℂ))
  have hD : D.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    exact_mod_cast Real.rpow_nonneg (p.2.property.1 i) (a/2)
  change (∑ i, Real.rpow
    ((hD.mul_mul_conjTranspose_same (p.1 : Matrix n n ℂ)).isHermitian.eigenvalues i) (2/a)) = 1
  rw [eigenvalues_conjugate hD p.1]
  rw [diagonal_eigenvalue_sum (fun i => (p.2.val i) ^ (a/2)) hD.isHermitian (fun x => x.rpow (2/a))]
  convert p.2.property.2 using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.rpow_eq_pow, ← Real.rpow_mul (p.2.property.1 i)]
  have he : a / 2 * (2/a) = 1 := by field_simp [ha.ne']
  rw [he, Real.rpow_one]

omit [Nonempty n] in
lemma coordinateMatrix_surjective {A : Matrix n n ℂ} (hA : A.PosSemidef)
    {a : ℝ} (ha : 0 < a)
    (htr : (∑ i, Real.rpow (hA.isHermitian.eigenvalues i) (2/a)) = 1) :
    ∃ p : SpectralCoordinate n, coordinateMatrix a p = A := by
  let r (i : n) := (hA.isHermitian.eigenvalues i).rpow (2/a)
  have hr : (∀ i, 0 ≤ r i) ∧ ∑ i, r i = 1 :=
    ⟨fun i => Real.rpow_nonneg (hA.eigenvalues_nonneg i) _, htr⟩
  refine ⟨⟨hA.isHermitian.eigenvectorUnitary, ⟨r, hr⟩⟩, ?_⟩
  have he : (fun i => ((r i) ^ (a/2) : ℝ)) = hA.isHermitian.eigenvalues := by
    funext i
    dsimp only [r]
    rw [Real.rpow_eq_pow, ← Real.rpow_mul (hA.eigenvalues_nonneg i)]
    have hh : 2 / a * (a/2) = 1 := by field_simp [ha.ne']
    rw [hh, Real.rpow_one]
  change Unitary.conjStarAlgAut ℂ _ hA.isHermitian.eigenvectorUnitary
    (Matrix.diagonal fun i => ((r i) ^ (a/2) : ℝ)) = A
  simp_rw [congrFun he]
  exact hA.isHermitian.spectral_theorem.symm

end CompactSpectralCoordinates

open Analytic
variable {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}

abbrev CoordinateFamily (q : ℕ) {L m : ℕ} (X : Fin m → Finset (Vertex L)) :=
  (j : Fin m) → SpectralCoordinate (RegionConfiguration q (X j))

def coordinateFilters (a : Fin m → ℝ) (p : CoordinateFamily q X) : FilterFamily q m X :=
  fun j => ⟨coordinateMatrix (a j) (p j), coordinateMatrix_positive (a j) (p j)⟩

omit [NeZero q] in
lemma coordinateFilters_admissible {a : Fin m → ℝ} (ha : ∀ j, 0 < a j)
    (p : CoordinateFamily q X) : Admissible a (coordinateFilters a p) := by
  intro j
  exact coordinateMatrix_tracePower (a j) (ha j) (p j)

lemma continuous_chain {Y : Type*} [TopologicalSpace Y]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (T : Fin m → Y → E →L[ℂ] E) (hT : ∀ j, Continuous (T j))
    {v : Y → E} (hv : Continuous v) : Continuous (fun p => chain (fun j => T j p) (v p)) := by
  induction m generalizing v with
  | zero => simpa only [chain_zero] using hv
  | succ m ih =>
    simp only [chain_succ]
    exact ih (fun j => T j.succ) (fun j => hT j.succ) ((hT 0).clm_apply hv)

omit [NeZero q] in
lemma coordinate_output_continuous (Ω : State L q) {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    Continuous (fun p : CoordinateFamily q X => output (coordinateFilters a p) Ω) := by
  apply continuous_chain
  · intro j
    have hc : Continuous (fun p : CoordinateFamily q X => coordinateMatrix (a j) (p j)) :=
      (coordinateMatrix_continuous (a j) (ha j)).comp (continuous_apply j)
    have hl : Continuous (liftLocal (q := q) (X j)) :=
      (liftLocalHom (q := q) (X j)).toLinearMap.continuous_of_finiteDimensional
    have hm : Continuous (asMap (L := L) (q := q)) :=
      by
        change Continuous (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ))
        exact (Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
    exact hm.comp (hl.comp hc)
  · exact continuous_const

theorem exists_maximizer (Ω : State L q) {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    ∃ F : FilterFamily q m X, IsMaximizer Ω a F := by
  classical
  let (j : Fin m) : CompactSpace (SpectralCoordinate (RegionConfiguration q (X j))) := by
    let := compact_unitary_coordinates (n := RegionConfiguration q (X j))
    let := compact_weight_coordinates (n := RegionConfiguration q (X j))
    infer_instance
  let p₀ : CoordinateFamily q X := fun j =>
    (1, ⟨Pi.single (Classical.arbitrary (RegionConfiguration q (X j))) 1,
      by
        constructor
        · intro index
          simp only [Pi.single_apply]
          split_ifs <;> norm_num
        · simp⟩)
  have hne : (Set.univ : Set (CoordinateFamily q X)).Nonempty := ⟨p₀, Set.mem_univ _⟩
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn hne
    (coordinate_output_continuous (X := X) Ω ha).norm.continuousOn
  refine ⟨coordinateFilters a p, coordinateFilters_admissible ha p, ?_⟩
  intro G hG
  have hc (j : Fin m) : ∃ s : SpectralCoordinate (RegionConfiguration q (X j)),
      coordinateMatrix (a j) s = (G j).matrix :=
    coordinateMatrix_surjective (G j).positive (ha j) (hG j)
  choose s hs using hc
  have heT : (fun j : Fin m => asMap (liftLocal (X j) (coordinateMatrix (a j) (s j)))) =
      (fun j : Fin m => asMap (liftLocal (X j) (G j).matrix)) := by
    funext j
    rw [hs j]
  have he : output (coordinateFilters a s) Ω = output G Ω := by
    change chain (fun j => asMap (liftLocal (X j) (coordinateMatrix (a j) (s j)))) Ω = _
    rw [heT]
    rfl
  rw [← he]
  exact hp (Set.mem_univ s)

end PolynomialPEPS.PinnedEntropy.NestedFilter

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open scoped BigOperators Matrix.Norms.L2Operator
open Analytic

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def uniformCoordinate (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    SpectralCoordinate n :=
  ⟨1, ⟨fun _ => (Fintype.card n : ℝ)⁻¹, by
    constructor
    · intro i; positivity
    · simp [Fintype.card_ne_zero]⟩⟩

lemma coordinateMatrix_uniform (a : ℝ) :
    coordinateMatrix a (uniformCoordinate n) =
      ((((Fintype.card n : ℝ)⁻¹) ^ (a/2) : ℝ) : ℂ) • (1 : Matrix n n ℂ) := by
  unfold coordinateMatrix uniformCoordinate Unitary.conjStarAlgAut
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [h]

lemma chain_scalar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {m : ℕ} (c : Fin m → ℂ) (v : E) :
    chain (fun j => c j • ContinuousLinearMap.id ℂ E) v = (∏ j, c j) • v := by
  induction m generalizing v with
  | zero => simp [chain]
  | succ m ih =>
    rw [chain_succ, ih]
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_smul,
      Fin.prod_univ_succ, mul_comm]

lemma output_uniform {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (Ω : State L q) :
    output (coordinateFilters a (fun j => uniformCoordinate (RegionConfiguration q (X j)))) Ω =
      (∏ j, (((Fintype.card (RegionConfiguration q (X j)) : ℝ)⁻¹ ^ (a j / 2) : ℝ) : ℂ)) • Ω := by
  have ht (j : Fin m) :
      asMap (liftLocal (X j) (coordinateMatrix (a j)
        (uniformCoordinate (RegionConfiguration q (X j))))) =
      (((Fintype.card (RegionConfiguration q (X j)) : ℝ)⁻¹ ^ (a j / 2) : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ (State L q) := by
    rw [coordinateMatrix_uniform]
    change Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) (liftLocalHom (X j) (_ • 1)) = _
    rw [map_smul, map_one, map_smul, map_one]
    rfl
  change chain (fun j => asMap (liftLocal (X j) (coordinateMatrix (a j)
    (uniformCoordinate (RegionConfiguration q (X j)))))) Ω = _
  simp_rw [ht]
  exact chain_scalar _ _

theorem maximizer_norm_pos {L q m : ℕ} [NeZero q] {X : Fin m → Finset (Vertex L)}
    {Ω : State L q} (hΩ : Ω ≠ 0) {a : Fin m → ℝ} (ha : ∀ j, 0 < a j)
    {F : FilterFamily q m X} (hF : IsMaximizer Ω a F) : 0 < ‖output F Ω‖ := by
  let p : CoordinateFamily q X := fun j => uniformCoordinate (RegionConfiguration q (X j))
  have hu : output (coordinateFilters a p) Ω ≠ 0 := by
    rw [output_uniform]
    apply smul_ne_zero _ hΩ
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply Real.rpow_pos_of_pos
    positivity
  exact (norm_pos_iff.mpr hu).trans_le (hF.2 _ (coordinateFilters_admissible ha p))

theorem exists_maximizer_upper {L q m : ℕ} [NeZero q]
    {S : Finset (Vertex L)} {X : Fin (m+1) → Finset (Vertex L)}
    (hST : ∀ j, S ⊆ X j) (hX : Monotone X)
    {Ω : State L q} (hΩ : ‖Ω‖ = 1)
    {a : Fin (m+1) → ℝ} (ha : ∀ j, 0 < a j) (r : ℝ) :
    ∃ F : FilterFamily q (m+1) X, IsMaximizer Ω a F ∧ 0 < ‖output F Ω‖ ∧
      UpperComparison S Ω a F 0 r := by
  obtain ⟨F, hF⟩ := exists_maximizer (X := X) Ω ha
  refine ⟨F, hF, maximizer_norm_pos ?_ ha hF, upperComparison_zero hST hX hΩ ha hF r⟩
  intro hz
  rw [hz, norm_zero] at hΩ
  exact zero_ne_one hΩ

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
