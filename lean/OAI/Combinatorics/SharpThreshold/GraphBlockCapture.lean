import OAI.Combinatorics.SharpThreshold.SupportDegreeGraph
import OAI.Combinatorics.SharpThreshold.BlockIncidence
import OAI.Combinatorics.SharpThreshold.BlockCapture
import OAI.Combinatorics.SharpThreshold.BlockSize
import OAI.Combinatorics.SharpThreshold.BlockCounting

namespace OAI

/-! The graph-combinatorial input to capture of low Fourier levels. -/

namespace Problem313

noncomputable section

/-- A block detects a support when the restricted Fourier degree is positive
and no larger than the specified real cutoff. -/
def BlockDetects {n : ℕ} (k : ℝ) (S : Finset (GraphEdge n))
    (B : Finset (Fin n)) : Prop :=
  1 ≤ (S.filter (fun e => ¬Disjoint e.val B)).card ∧
    ((S.filter (fun e => ¬Disjoint e.val B)).card : ℝ) ≤ k

instance blockDetects_decidable {n : ℕ} (k : ℝ) (S : Finset (GraphEdge n))
    (B : Finset (Fin n)) : Decidable (BlockDetects k S B) :=
  Classical.propDecidable _

/-- For a low-degree support, choose one positive-degree vertex whose isolation
by the random block guarantees detection. -/
theorem exists_vertex_singleton_implies_detection {n : ℕ}
    (S : Finset (GraphEdge n)) (hS : S.Nonempty) {k : ℝ}
    (hk : 0 ≤ k) (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) :
    ∃ u ∈ S.biUnion (fun e => e.val), ∀ B : Finset (Fin n),
      B ∩ S.biUnion (fun e => e.val) = {u} → BlockDetects k S B := by
  classical
  obtain ⟨u, hu, hpos, hdeg⟩ := support_exists_degree_le_cutoff S hS hk hcard
  refine ⟨u, hu, ?_⟩
  intro B hB
  unfold BlockDetects
  rw [block_not_disjoint_filter_eq_vertex_filter S B u hB]
  exact ⟨hpos, hdeg⟩

/-- Transfer any uniform singleton-intersection bound to a detection bound. -/
theorem block_detection_probability_of_singleton {n : ℕ}
    (blocks : Finset (Finset (Fin n))) (S : Finset (GraphEdge n))
    (hS : S.Nonempty) {k a : ℝ} (hk : 0 ≤ k)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2)
    (hsingle : ∀ u ∈ S.biUnion (fun e => e.val),
      a ≤ ((blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u})).card : ℝ) /
        blocks.card) :
    a ≤ ((blocks.filter (BlockDetects k S)).card : ℝ) / blocks.card := by
  classical
  obtain ⟨u, hu, hdetect⟩ := exists_vertex_singleton_implies_detection S hS hk hcard
  apply (hsingle u hu).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg blocks.card)
  exact_mod_cast Finset.card_le_card (show
    blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u}) ⊆
      blocks.filter (BlockDetects k S) from by
    intro B hB
    obtain ⟨hBmem, hBsingle⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨hBmem, hdetect B hBsingle⟩)

/-- The support-vertex bound turns the random-block union-bound error into a
uniform error at most one half. -/
theorem support_singleton_error_le_half {n : ℕ}
    (S : Finset (GraphEdge n)) (k r : ℝ)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2)
    (hr : 0 ≤ r) (hbudget : k ^ 2 * r ≤ 1 / 2) :
    (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r ≤ 1 / 2 := by
  have hv : ((S.biUnion (fun e => e.val)).card : ℝ) ≤ 2 * S.card := by
    exact_mod_cast support_vertices_card_le S
  have hvk : ((S.biUnion (fun e => e.val)).card : ℝ) - 1 ≤ k ^ 2 := by
    linarith
  exact (mul_le_mul_of_nonneg_right hvk hr).trans hbudget

/-- Quantitative detection from the singleton-intersection union bound. The
scalar `r` will be `(m-1)/(n-1)` for a uniformly chosen `m`-vertex block. -/
theorem block_detection_probability_lower {n : ℕ}
    (blocks : Finset (Finset (Fin n))) (S : Finset (GraphEdge n))
    (hS : S.Nonempty) (k q r : ℝ) (hk : 0 ≤ k) (hq : 0 ≤ q)
    (hcard : (S.card : ℝ) ≤ k ^ 2 / 2) (hr : 0 ≤ r)
    (hbudget : k ^ 2 * r ≤ 1 / 2)
    (hsingle : ∀ u ∈ S.biUnion (fun e => e.val),
      q * (1 - (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r) ≤
        ((blocks.filter (fun B => B ∩ S.biUnion (fun e => e.val) = {u})).card : ℝ) /
          blocks.card) :
    q / 2 ≤ ((blocks.filter (BlockDetects k S)).card : ℝ) / blocks.card := by
  apply block_detection_probability_of_singleton blocks S hS hk hcard
  intro u hu
  apply le_trans _ (hsingle u hu)
  have he := support_singleton_error_le_half S k r hcard hr hbudget
  have := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤
    1 - (((S.biUnion (fun e => e.val)).card : ℝ) - 1) * r by linarith) hq
  linarith

/-- The biased Fourier cutoff for a square-root block never exceeds `log n`. -/
theorem sqrt_block_cutoff_le_log (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    0 ≤ sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ∧
      sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64 ≤ Real.log (n : ℝ) := by
  have hm := sqrt_block_size_bounds n hn ht
  have hmreal : (1 : ℝ) ≤ (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega)
  have hlogm : 0 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := Real.log_nonneg hmreal
  have hlogmn : Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log (by linarith)
    exact_mod_cast hm.2.1
  have hprod := mul_le_mul_of_nonneg_right hsigma1 hlogm
  exact ⟨div_nonneg (mul_nonneg hsigma hlogm) (by norm_num), by linarith⟩

/-- Uniform numerical budget used in detecting supports of at most `k²/2` edges. -/
theorem sqrt_block_cutoff_budget (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2) :
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤ 1 / 2 := by
  have hk := sqrt_block_cutoff_le_log n sigma hn ht hsigma hsigma1
  have hsq := pow_le_pow_left₀ hk.1 hk.2 2
  calc
    (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) - 1) / ((n : ℝ) - 1)) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 *
        (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_block_pair_ratio n hn) (sq_nonneg _)
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (1 / Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = (Real.log (n : ℝ)) ^ 2 / Real.sqrt (n : ℝ) := by ring
    _ ≤ 1 / 2 := log_square_div_sqrt_le_half n hn ht

/-- Every nonempty support of degree at most `k²/2` is detected with probability
at least `m/(2*n)` by the square-root-sized random block. -/
theorem sqrt_block_detection_probability (n : ℕ) (sigma : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) (hsigma : 0 ≤ sigma) (hsigma1 : sigma ≤ 1 / 2)
    (S : Finset (GraphEdge n)) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤
      (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2) :
    (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 * n) ≤
      blockProbability (Finset.univ : Finset (Fin n)) ⌊Real.sqrt (n : ℝ)⌋₊
        (BlockDetects (sigma * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) S) := by
  classical
  let m := ⌊Real.sqrt (n : ℝ)⌋₊
  let k := sigma * Real.log (m : ℝ) / 64
  have hm := sqrt_block_size_bounds n hn ht
  have hk := sqrt_block_cutoff_le_log n sigma hn ht hsigma hsigma1
  obtain ⟨u, hu, hdetect⟩ := exists_vertex_singleton_implies_detection S hS hk.1 hcard
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmreal : (3 : ℝ) ≤ m := by exact_mod_cast hm.1
  have hr : 0 ≤ ((m : ℝ) - 1) / ((n : ℝ) - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hcollision := support_singleton_error_le_half S k
    (((m : ℝ) - 1) / ((n : ℝ) - 1)) hcard hr
    (sqrt_block_cutoff_budget n sigma hn ht hsigma hsigma1)
  have hsingle := blockProbability_singleton_inter_ge_half
    (Finset.univ : Finset (Fin n)) (S.biUnion (fun e => e.val))
    (Finset.subset_univ _) hu (show 2 ≤ m by omega)
    (show m ≤ (Finset.univ : Finset (Fin n)).card by
      simpa only [Finset.card_univ, Fintype.card_fin] using hm.2.1)
    (by simpa only [Finset.card_univ, Fintype.card_fin, mul_div_assoc] using hcollision)
  have hmono := blockProbability_mono (Finset.univ : Finset (Fin n)) m
    (fun B _ hB => hdetect B hB)
  simpa only [Finset.card_univ, Fintype.card_fin] using hsingle.trans hmono

/-- The graph-bias version, with the normalized cardinal ratio exposed for the
finite averaging lemma. No restriction on `p` is needed for this combinatorics. -/
theorem graph_block_detection_probability (n : ℕ) (p : ℝ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ))
    (S : Finset (GraphEdge n)) (hS : S.Nonempty)
    (hcard : (S.card : ℝ) ≤
      (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2) :
    (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / (2 * n) ≤
      ((((Finset.univ : Finset (Fin n)).powersetCard ⌊Real.sqrt (n : ℝ)⌋₊).filter
        (BlockDetects (Real.sqrt (p * (1 - p)) *
          Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) S)).card : ℝ) /
        ((Finset.univ : Finset (Fin n)).powersetCard ⌊Real.sqrt (n : ℝ)⌋₊).card := by
  have hsigma1 : Real.sqrt (p * (1 - p)) ≤ (1 / 2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (p - 1 / 2)]
  simpa only [blockProbability_eq] using sqrt_block_detection_probability n
    (Real.sqrt (p * (1 - p))) hn ht (Real.sqrt_nonneg _) hsigma1 S hS hcard

/-- An equivalent presentation using intersection with the finite free-edge set. -/
theorem blockDetects_iff_inter_free_edges {n : ℕ} (k : ℝ)
    (S : Finset (GraphEdge n)) (B : Finset (Fin n)) :
    BlockDetects k S B ↔
      1 ≤ (S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B)).card ∧
        ((S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B)).card : ℝ) ≤ k := by
  classical
  have h : S ∩ Finset.univ.filter (fun e : GraphEdge n => ¬Disjoint e.val B) =
      S.filter (fun e => ¬Disjoint e.val B) := by
    ext e
    simp
  rw [h]
  rfl

end

end Problem313

end OAI
