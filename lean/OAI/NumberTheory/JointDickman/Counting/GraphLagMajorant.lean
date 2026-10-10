import OAI.NumberTheory.JointDickman.Amplification.GraphTripleSupport

namespace OAI

/-! # An actual lag mass is dominated by a finite sum of periodic means -/

namespace JointDickman
open Finset Filter
open scoped Topology

open Classical in
noncomputable def arithmeticLagMass (B L : ℕ) (τ C : ℝ) (T N : ℕ) (j : ℤ) : ℝ :=
  (∑ i ∈ arithmeticGraphTriples B T, if graphTripleLag i = j then
    ∑ n ∈ graphTripleEdges N i, graphTripleWeight B L τ C T i n else 0)/(N : ℝ)

noncomputable def graphLagMajorant (B T N : ℕ) (j : ℤ) : ℝ :=
  (∑ i ∈ coprimeGraphTriples B T j,
    (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
      coefficientWeight B (∏ p ∈ i.2.2, p)) *
    ∑ n ∈ range (2*T*N), graphEdgeEnvelope B (∏ p ∈ i.2.1, p)
      (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p) j n)/(N : ℝ)

theorem arithmeticLagMass_supported {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) (N : ℕ) (j : ℤ) :
    arithmeticLagMass B L τ C T N j =
      (∑ i ∈ coprimeGraphTriples B T j, ∑ n ∈ graphTripleEdges N i,
        graphTripleWeight B L τ C T i n)/(N : ℝ) := by
  classical
  unfold arithmeticLagMass
  congr 1
  have hsub : coprimeGraphTriples B T j ⊆ arithmeticGraphTriples B T :=
    (filter_subset _ _).trans (filter_subset _ _)
  calc
    _ = ∑ i ∈ coprimeGraphTriples B T j, if graphTripleLag i = j then
        ∑ n ∈ graphTripleEdges N i, graphTripleWeight B L τ C T i n else 0 := by
      symm
      apply sum_subset hsub
      intro i hi hni
      by_cases hj : graphTripleLag i = j
      · rw [ite_eq_left hj]
        apply sum_eq_zero
        intro n hn
        by_contra hw
        exact hni (mem_filter.mpr ⟨graphTripleWeight_nonzero_supported hB hT τ C hi hj hw,
          graphTriple_edge_coprime hi hn⟩)
      · exact ite_eq_right hj
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      exact ite_eq_left (mem_filter.mp (mem_filter.mp hi).1).2.1

theorem arithmeticLagMass_le_majorant {B L T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (τ C : ℝ) (N : ℕ) (j : ℤ) :
    arithmeticLagMass B L τ C T N j ≤ graphLagMajorant B T N j := by
  classical
  rw [arithmeticLagMass_supported hB hT]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply sum_le_sum
  intro i hi
  have hi' := (mem_filter.mp (mem_filter.mp hi).1).1
  have hlag := (mem_filter.mp (mem_filter.mp hi).1).2.1
  have hs := graphTriple_subsets hi'
  have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
  have hg := (mem_filter.mp hi').2
  have he := hg.2.2.2.1
  have hcop := hg.2.2.2.2
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  change (∏ p ∈ i.2.1, p).Coprime (graphTripleLag i).natAbs at hcop
  rw [hlag] at he hcop
  have h := graphPair_mass_le_prefix (B := B) (L := L) (T := T) τ C
    (amplificationOuterWeight B) (fun _ => amplificationBump_bounds _)
    (hp _ hs.2.1) (hp _ hs.2.2) (hp _ hs.1) he hcop N
  simpa only [graphTripleWeight, graphTripleEdges, hlag] using h

noncomputable def graphLagMean (B T : ℕ) (j : ℤ) : ℝ :=
  ∑ i ∈ coprimeGraphTriples B T j,
    (coefficientWeight B (∏ p ∈ i.1, p) * coefficientWeight B (∏ p ∈ i.2.1, p) *
      coefficientWeight B (∏ p ∈ i.2.2, p)) * (2*(T : ℝ)) *
    graphEdgeMean B (∏ p ∈ i.2.1, p) (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p)

theorem graphLagMajorant_tendsto {B T : ℕ} (hT : 0 < T) {j : ℤ}
    (hj : j ≠ 0) (hsmall : j.natAbs ≤ auxiliaryCutoff B) :
    Tendsto (fun N => graphLagMajorant B T N j) atTop (𝓝 (graphLagMean B T j)) := by
  classical
  simp only [graphLagMajorant, sum_div, graphLagMean]
  apply tendsto_finsetSum
  intro i hi
  have hi' := (mem_filter.mp (mem_filter.mp hi).1).1
  have hlag := (mem_filter.mp (mem_filter.mp hi).1).2.1
  have hs := graphTriple_subsets hi'
  have hp (D : Finset ℕ) (hD : D ⊆ auxiliaryPrimes B) : 0 < ∏ p ∈ D, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p (hD hp)).pos)
  let : NeZero (∏ p ∈ i.2.1, p) := ⟨(hp _ hs.2.1).ne'⟩
  let : NeZero (∏ p ∈ i.2.2, p) := ⟨(hp _ hs.2.2).ne'⟩
  have hg := (mem_filter.mp hi').2
  have he := hg.2.2.2.1
  have hcop := hg.2.2.2.2
  change ((∏ p ∈ i.2.1, p : ℕ) : ℤ)-(∏ p ∈ i.2.2, p : ℕ) =
    graphTripleLag i*(∏ p ∈ i.1, p : ℕ) at he
  change (∏ p ∈ i.2.1, p).Coprime (graphTripleLag i).natAbs at hcop
  rw [hlag] at he hcop
  have hab := divisor_edge_coprime (mem_filter.mp hi).2 hcop he
  have he' : ((∏ p ∈ i.2.1, p : ℕ) : ℤ) =
      (∏ p ∈ i.2.2, p : ℕ)+j*(∏ p ∈ i.1, p : ℕ) := by linarith
  exact graphPair_majorant_tendsto hT hab B _ j (graph_good_lag_ne_zero hj hsmall) he'

end JointDickman

end OAI
