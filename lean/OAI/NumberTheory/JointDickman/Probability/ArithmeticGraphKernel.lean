import OAI.NumberTheory.JointDickman.Amplification.FiniteGraphRegroup

namespace OAI

/-! # Grouping the actual arithmetic graph by lag and endpoint -/

namespace JointDickman
open Finset

abbrev GraphCoefficientTriple := Finset ℕ × (Finset ℕ × Finset ℕ)

open Classical in
noncomputable def arithmeticGraphTriples (B T : ℕ) : Finset GraphCoefficientTriple :=
  ((auxiliaryPrimes B).powerset ×ˢ
    ((auxiliaryPrimes B).powerset ×ˢ (auxiliaryPrimes B).powerset)).filter
      (fun i => GraphCoefficientAdmissible T i.1 i.2.1 i.2.2)

noncomputable def arithmeticGraphVertexCap (B N : ℕ) : ℕ :=
  (∏ p ∈ auxiliaryPrimes B, p)*N

noncomputable def graphTripleLag (i : GraphCoefficientTriple) : ℤ :=
  coefficientPairLag i.1 i.2.1 i.2.2

noncomputable def graphTripleEdges (N : ℕ) (i : GraphCoefficientTriple) : Finset ℕ :=
  divisorEdgeNew (∏ p ∈ i.2.1, p) (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p) N (graphTripleLag i)

noncomputable def graphTripleWeight (B L : ℕ) (τ C : ℝ) (T : ℕ)
    (i : GraphCoefficientTriple) (n : ℕ) : ℝ :=
  arithmeticGraphPairWeight B L τ C (amplificationOuterWeight B) (amplificationInnerWeight T)
    (∏ p ∈ i.2.1, p) (∏ p ∈ i.2.2, p) (∏ p ∈ i.1, p) (graphTripleLag i) n

open Classical in
noncomputable def rawArithmeticGraphKernel (B L : ℕ) (τ C : ℝ) (T N : ℕ)
    (j : ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ arithmeticGraphTriples B T,
    if graphTripleLag i = j ∧ n ∈ graphTripleEdges N i then graphTripleWeight B L τ C T i n else 0

theorem graphTriple_lag_mem {B T : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) : graphTripleLag i ∈ Icc (-(T : ℤ)) T := by
  classical
  have hg := (mem_filter.mp hi).2
  have hlt : |graphTripleLag i| < (T : ℤ) := by
    change |coefficientPairLag i.1 i.2.1 i.2.2| < (T : ℤ)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hg.2.2.1
  exact mem_Icc.mpr ⟨(abs_lt.mp hlt).1.le,(abs_lt.mp hlt).2.le⟩

theorem graphTriple_edges_subset {B T N : ℕ} {i : GraphCoefficientTriple}
    (hi : i ∈ arithmeticGraphTriples B T) :
    graphTripleEdges N i ⊆ Icc 1 (arithmeticGraphVertexCap B N) := by
  classical
  intro n hn
  have hE := mem_powerset.mp (mem_product.mp (mem_product.mp (mem_filter.mp hi).1).2).2
  have hb : (∏ p ∈ i.2.2, p) ∣ ∏ p ∈ auxiliaryPrimes B, p :=
    prod_dvd_prod_of_subset _ _ id hE
  have hp : 0 < ∏ p ∈ auxiliaryPrimes B, p :=
    prod_pos (fun p hp => (auxiliaryPrimes_prime B p hp).pos)
  have hb_le := Nat.le_of_dvd hp hb
  have hn' := mem_Icc.mp (mem_filter.mp hn).1
  exact mem_Icc.mpr ⟨hn'.1,hn'.2.trans (Nat.mul_le_mul_right N hb_le)⟩

theorem arithmeticOffDiagonalGraph_triples (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F =
      (∑ i ∈ arithmeticGraphTriples B T, ∑ n ∈ graphTripleEdges N i,
        graphTripleWeight B L τ C T i n * (star (F n)*F ((n : ℤ)+graphTripleLag i).toNat).re)/(N : ℝ) := by
  classical
  unfold arithmeticOffDiagonalGraph arithmeticGraphTriples
  rw [sum_filter,sum_product]
  congr 1
  apply sum_congr rfl
  intro D _
  rw [sum_product]
  apply sum_congr rfl
  intro A _
  apply sum_congr rfl
  intro E _
  rfl

/-- The graph form as a sum of one kernel per small additive lag. This
identity precedes all kernel estimates and contains no analytic premise. -/
theorem arithmeticOffDiagonalGraph_kernel (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F =
      (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N), ∑ j ∈ Icc (-(T : ℤ)) T,
        rawArithmeticGraphKernel B L τ C T N j n * (star (F n)*F ((n : ℤ)+j).toNat).re)/(N : ℝ) := by
  rw [arithmeticOffDiagonalGraph_triples]
  congr 1
  exact finite_graph_regroup (arithmeticGraphTriples B T) (Icc (-(T : ℤ)) T)
    (Icc 1 (arithmeticGraphVertexCap B N)) graphTripleLag (graphTripleEdges N)
    (graphTripleWeight B L τ C T) (fun j n => (star (F n)*F ((n : ℤ)+j).toNat).re)
    (fun _ hi => graphTriple_lag_mem hi) (fun _ hi => graphTriple_edges_subset hi)

end JointDickman

end OAI
