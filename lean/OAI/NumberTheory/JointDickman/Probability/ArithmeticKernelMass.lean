import OAI.NumberTheory.JointDickman.Counting.SignedLagMass

namespace OAI

/-! # The actual lag kernel inherits the uniform arithmetic mass bound -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticLagMass_eq_kernel (B L : ℕ) (τ C : ℝ) (T N : ℕ) (j : ℤ) :
    arithmeticLagMass B L τ C T N j =
      (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
        rawArithmeticGraphKernel B L τ C T N j n)/(N : ℝ) := by
  classical
  unfold arithmeticLagMass rawArithmeticGraphKernel
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  by_cases hj : graphTripleLag i = j
  · simp only [hj, true_and, ite_true]
    rw [← sum_filter]
    have hfilter : (Icc 1 (arithmeticGraphVertexCap B N)).filter
        (fun n => n ∈ graphTripleEdges N i) = graphTripleEdges N i := by
      ext n
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hn => graphTriple_edges_subset hi hn)
    rw [hfilter]
  · simp only [hj, false_and, ite_false, sum_const_zero]

/-- The normalized kernel has the manuscript's summable lag majorant.
The statement is simultaneous in every regularity parameter. -/
theorem arithmeticKernelMass_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ, ∀ j : ℤ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → j ≠ 0 →
      j.natAbs ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ,
        (∑ n ∈ Icc 1 (arithmeticGraphVertexCap B N),
          rawArithmeticGraphKernel B L τ C T N j n)/((B : ℝ)*T*N) ≤
          K*singularFactor 24 j.natAbs/(T : ℝ)+ε := by
  obtain ⟨K,hK,hbound⟩ := arithmeticLagMass_signed_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop 0] with B hB hB0
  intro T j hT hTs hj hjB ε hε
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB0
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  filter_upwards [hB T j hT hTs hj hjB (ε*((B : ℝ)*T)) (by positivity)] with N hN
  intro L τ C
  have h := hN L τ C
  rw [arithmeticLagMass_eq_kernel] at h
  have hh := div_le_div_of_nonneg_right h (mul_pos hBr hTr).le
  convert hh using 1
  · ring
  · field_simp

end JointDickman

end OAI
