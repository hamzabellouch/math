import OAI.Combinatorics.SharpThreshold.BlockAverage
import OAI.Combinatorics.SharpThreshold.BlockCounting
import OAI.Combinatorics.SharpThreshold.BlockRestrictionSymmetry
import OAI.Combinatorics.SharpThreshold.FourierBasis
import OAI.Combinatorics.SharpThreshold.Probability
import OAI.Combinatorics.SharpThreshold.GraphBlockCapture
import OAI.Combinatorics.SharpThreshold.BlockLowDegree

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem313

/-- The fixed-block Fourier estimate and the pointwise support-capture estimate
combine into the global captured-mass bound. All graph sampling probabilities
are the canonical `blockProbability`; the edge-touch bound is discharged here.
The two hypotheses are precisely the analytic and combinatorial inputs, with
no requirement that a single block capture every support simultaneously. -/
theorem graph_fourier_capture_of_block_bounds
    {n m : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hmn : m ≤ n)
    (k a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ S : Finset (GraphEdge n), S.Nonempty →
      (S.card : ℝ) ≤ k ^ 2 / 2 →
      (m : ℝ) / (2 * n) ≤
        blockProbability (Finset.univ : Finset (Fin n)) m (fun B =>
          1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k))
    (hblock : ∀ B : Finset (Fin n), B.card = m →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * a * totalInfluence p f := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard m
  let low := (Finset.univ : Finset (Finset (GraphEdge n))).filter
    (fun S => S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2)
  let mass := fun S : Finset (GraphEdge n) =>
    BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2
  let detect := fun (B : Finset (Fin n)) (S : Finset (GraphEdge n)) =>
    1 ≤ (S.filter (EdgeTouches B)).card ∧
      ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
  have hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < (m : ℝ) / (2 * n) := by positivity
  have hcap : ∀ S ∈ low,
      (m : ℝ) / (2 * n) ≤
        ((Ω.filter (fun B => detect B S)).card : ℝ) / Ω.card := by
    intro S hS
    obtain ⟨_, hSne, hScard⟩ := Finset.mem_filter.mp hS
    simpa only [blockProbability_eq] using hcapture S hSne hScard
  have hb : ∀ B ∈ Ω,
      (∑ S, if detect B S then mass S else 0) ≤
        a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0 := by
    intro B hB
    exact hblock B (Finset.mem_powersetCard.mp hB).2
  have hi : ∀ e : GraphEdge n,
      ((Ω.filter (fun B => EdgeTouches B e)).card : ℝ) / Ω.card ≤
        4 * ((m : ℝ) / (2 * n)) := by
    intro e
    have htouch := blockProbability_edge_touch_le
      (Finset.univ : Finset (Fin n)) e.val (Finset.subset_univ _) e.property hm
      (by simpa using hmn)
    have hevent : blockProbability (Finset.univ : Finset (Fin n)) m
        (fun B => EdgeTouches B e) =
        blockProbability (Finset.univ : Finset (Fin n)) m
          (fun B => (B ∩ e.val).Nonempty) := by
      apply blockProbability_congr
      intro B hB
      simp only [EdgeTouches, Finset.Nonempty, Finset.mem_inter]
      exact exists_congr (fun _ => and_comm)
    change blockProbability (Finset.univ : Finset (Fin n)) m
      (fun B => EdgeTouches B e) ≤ _
    rw [hevent]
    calc
      _ ≤ (2 : ℝ) * m / (Finset.univ : Finset (Fin n)).card := htouch
      _ = 4 * ((m : ℝ) / (2 * n)) := by simp; ring
  have h := BlockAverage.captured_mass_le_four_uniform Ω mass
    (edgeInfluence p f) detect EdgeTouches low a ((m : ℝ) / (2 * n))
    (fun S => sq_nonneg _) (edgeInfluence_nonneg hp hp1 f) ha hc hcap hb hi
  simpa only [low, mass, Finset.sum_filter, totalInfluence] using h

/-- At the square-root block size all counting and numerical capture premises
are discharged. Only the fixed-block analytic estimate remains as input. -/
theorem graph_fourier_captured_mass_of_block_bound
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ))
    (hp : 0 < p) (hp1 : p < 1)
    (hblock : ∀ B : Finset (Fin n), B.card = ⌊Real.sqrt (n : ℝ)⌋₊ →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤
              Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by
  have hm := sqrt_block_size_bounds n hn ht
  apply graph_fourier_capture_of_block_bounds f hp.le hp1.le
    (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega) hm.2.1
    (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64)
    ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) (by positivity)
  · intro S hS hcard
    have hsigma1 : Real.sqrt (p * (1 - p)) ≤ (1 / 2 : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · nlinarith [sq_nonneg (p - 1 / 2)]
    have hdet := sqrt_block_detection_probability n (Real.sqrt (p * (1 - p)))
      hn ht (Real.sqrt_nonneg _) hsigma1 S hS hcard
    refine hdet.trans_eq ?_
    apply blockProbability_congr
    intro B hB
    simp only [BlockDetects, edgeTouches_iff_not_disjoint]
  · exact hblock

/-- The complete captured Fourier-mass bound for a vertex-invariant graph
property. The bias is unrestricted within `(0,1)` and no monotonicity is used. -/
theorem graph_fourier_captured_mass
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ)) (hf : VertexInvariant f)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by
  apply graph_fourier_captured_mass_of_block_bound f hn ht hp hp1
  intro B hB
  have hBm : 3 ≤ B.card := by
    rw [hB]
    exact (sqrt_block_size_bounds n hn ht).1
  simpa only [hB, Finset.sum_filter] using
    block_low_degree_bound_filter B hBm f hf hp hp1

end Problem313

end

end OAI
