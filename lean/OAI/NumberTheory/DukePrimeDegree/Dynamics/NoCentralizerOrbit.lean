import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralizerFlow

namespace OAI

/-!
# Excluding a probability measure on a root centralizer orbit

This is the consequence of EKL Theorem 5.1 and Proposition 5.2 needed in
the low-entropy argument. The neutral direction is explicit: its double
weight is negative and its complementary weights are distinct.
-/

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Classical Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem no_invariant_rootPair_orbit_of_weights {n m : ℕ}
    (e : Fin n ≃ Fin 2 ⊕ Fin m)
    (hij : e.symm (Sum.inl 0) ≠ e.symm (Sum.inl 1))
    (ell : Fin n → ℝ) (hell : ∑ r, ell r = 0)
    (hneut : ell (e.symm (Sum.inl 0)) = ell (e.symm (Sum.inl 1)))
    (hneg : ell (e.symm (Sum.inl 0)) < 0)
    (hdist : Function.Injective (fun r : Fin m => ell (e.symm (Sum.inr r))))
    (μ : Measure (X n)) [IsFiniteMeasure μ] [NeZero μ]
    (x : X n)
    (hfull : ∀ᵐ y ∂μ, ∃ h : rootPairCentralizer hij, rightAction x (h : G n) = y)
    (hinv : μ.map (fun y => rightAction y (diagonalOneParameter ell hell 1)) = μ) :
    False := by
  let U : Set (rootPairCentralizer hij) := {g |
    0 < g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) ∧
    g.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) < Real.exp 1 ∧
    ∀ r, ∑ s, ‖(complementaryMatrix e g.val - 1) r s‖ < spectralRelativeRadius}
  have hU : U ∈ 𝓝 1 := eventually_small_centralizer_blocks e hij
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((eventually_separated_scaled_weights _ hdist).and (eventually_scalar_between_zero_one hneg))
  obtain ⟨k, hk, h, hh, q, γ, hγ⟩ := exists_integral_return_of_closed_orbit
    (rootPairCentralizer hij) (rootPairCentralizer_isClosed hij)
    μ x hfull (diagonalOneParameter ell hell 1) hinv U hU N
  obtain ⟨hgap, hscalar⟩ := hN k hk.le
  obtain ⟨hc0, hc1, hBsmall⟩ := hh
  let R : G n := diagonalOneParameter ell hell (k : ℝ) * h.val
  have hR : R ∈ rootPairCentralizer hij :=
    (rootPairCentralizer hij).mul_mem
      (diagonal_mem_rootPairCentralizer hij ell hell hneut _) h.property
  have hγR : q⁻¹ * Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ * q = R := by
    simpa only [R, ← diagonalOneParameter_nat] using hγ
  have hBsep : (complementaryMatrix e R).charpoly.Separable := by
    obtain ⟨_, _, _, _, _, hs⟩ := real_spectrum_of_logarithmic_gaps
      (fun r => ell (e.symm (Sum.inr r)) * (k : ℝ)) hgap
      (complementaryMatrix e h.val) hBsmall
    dsimp [R]
    rw [complementaryMatrix_diagonal_mul, Matrix.charpoly_mul_comm]
    exact hs
  let c := R.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0))
  have hc : c = Real.exp (ell (e.symm (Sum.inl 0)) * (k : ℝ)) *
      h.val.val (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) := by
    change (Matrix.diagonal (fun i => Real.exp (ell i * (k : ℝ))) * h.val.val)
      (e.symm (Sum.inl 0)) (e.symm (Sum.inl 0)) = _
    rw [Matrix.diagonal_mul]
  have hcbounds : 0 < c ∧ c < 1 := by
    rw [hc]
    exact hscalar _ hc0 hc1
  have hunit : c = 1 ∨ c = -1 := by
    apply reindexed_integral_scalar_block e q γ c (complementaryMatrix e R) hBsep
    rw [hγR]
    exact rootPairCentralizer_block_explicit e hij R hR
  rcases hunit with hunit | hunit
  · linarith [hcbounds.2]
  · linarith [hcbounds.1]

end DukePrimeDegree

end

end OAI
