import OAI.NumberTheory.DukePrimeDegree.Dynamics.StrongReturns
import OAI.NumberTheory.DukePrimeDegree.Dynamics.CentralizerFlow

namespace OAI

/-!
# The exceptional-return strengthening

Outside one null set, every sufficiently small lift of a return along the
root-pair centralizer, if it centralizes the chosen root, centralizes both
roots. In particular this applies to every neutral diagonal return. This
is the implication from exceptional to strong exceptional returns in
EKL (2006), Lemma 4.2, on the actual arithmetic quotient.
-/

noncomputable section
open Filter Set Matrix MeasureTheory
open scoped Topology Classical BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootContractionWeights_swap {n : ℕ} (i j r : Fin n) :
    rootContractionWeights j i r = -rootContractionWeights i j r := by
  unfold rootContractionWeights
  ring

lemma rootPairCentralizer_commutes_contraction {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (g : G n) (hg : g ∈ rootPairCentralizer hij) (t : ℝ) :
    g * diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t =
      diagonalOneParameter (rootContractionWeights i j) (rootContractionWeights_sum i j) t * g := by
  obtain ⟨hijg, hjig⟩ := (mem_rootPairCentralizer hij g).mp hg
  have hw {r s : Fin n} (hentry : g.val r s ≠ 0) :
      rootContractionWeights i j r = rootContractionWeights i j s := by
    have h₁ := rootContractionWeights_entry_nonneg hij g hijg hentry
    have h₂ := rootContractionWeights_entry_nonneg hij.symm g hjig hentry
    rw [rootContractionWeights_swap i j r, rootContractionWeights_swap i j s] at h₂
    linarith
  ext r s
  change (g.val * Matrix.diagonal (fun a => Real.exp (rootContractionWeights i j a * t))) r s =
    (Matrix.diagonal (fun a => Real.exp (rootContractionWeights i j a * t)) * g.val) r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hzero : g.val r s = 0
  · simp [hzero]
  · rw [hw hzero]
    ring

/-- The null set is independent of the return parameter and of the local
chart. The radius may depend on the base point. -/
theorem ae_exceptional_returns_are_strong
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∃ r : ℝ, 0 < r ∧
      ∀ b : rootPairCentralizer hij, ∀ g ∈ matrixBall (d + 1) r,
        g ∈ singleRootCentralizer hij → rightAction x g = rightAction x b →
          g ∈ rootPairCentralizer hij := by
  choose U hUo hxU R hR hinj using (local_uniform_chart_injective (n := d + 1))
  obtain ⟨S, hSc, hcover⟩ := countable_cover_nhds (fun x => (hUo x).mem_nhds (hxU x))
  have hchart (a : X (d + 1)) : ∀ᵐ x ∂μ, x ∈ U a →
      ∀ b : rootPairCentralizer hij, ∀ g ∈ matrixBall (d + 1) (R a / 2),
        g ∈ singleRootCentralizer hij → rightAction x g = rightAction x b →
          g ∈ rootPairCentralizer hij := by
    apply ae_strong_returns_on_chart d hij μ hA (rootPairCentralizer hij)
      (fun b => (mem_singleRootCentralizer hij b.val).mpr ((mem_rootPairCentralizer hij b.val).mp b.property).1)
      (fun b t => rootPairCentralizer_commutes_contraction hij b.val b.property t)
      (R a / 2) (R a) (half_pos (hR a)).le (by linarith [hR a])
      (U a) (hUo a).measurableSet (hinj a)
  have hall : ∀ᵐ x ∂μ, ∀ a ∈ S, x ∈ U a →
      ∀ b : rootPairCentralizer hij, ∀ g ∈ matrixBall (d + 1) (R a / 2),
        g ∈ singleRootCentralizer hij → rightAction x g = rightAction x b →
          g ∈ rootPairCentralizer hij := (ae_ball_iff hSc).mpr fun a _ => hchart a
  filter_upwards [hall] with x hx
  have hxcover : x ∈ ⋃ a ∈ S, U a := by rw [hcover]; trivial
  obtain ⟨a, haS, hxa⟩ := mem_iUnion₂.mp hxcover
  exact ⟨R a / 2, half_pos (hR a), hx a haS hxa⟩

/-- Every neutral diagonal lies in the root-pair centralizer, so the
strengthening applies to precisely the return group used by EKL. -/
theorem ae_neutral_diagonal_returns_are_strong
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ x ∂μ, ∃ r : ℝ, 0 < r ∧
      ∀ (ell : Fin (d + 1) → ℝ) (hell : ∑ a, ell a = 0), ell i = ell j →
        ∀ t : ℝ, ∀ g ∈ matrixBall (d + 1) r,
          g ∈ singleRootCentralizer hij →
          rightAction x g = rightAction x (diagonalOneParameter ell hell t) →
            g ∈ rootPairCentralizer hij := by
  filter_upwards [ae_exceptional_returns_are_strong d hij μ hA] with x hx
  obtain ⟨r, hr, hret⟩ := hx
  refine ⟨r, hr, ?_⟩
  intro ell hell hneutral t g hgball hgroot heq
  exact hret ⟨diagonalOneParameter ell hell t,
    diagonal_mem_rootPairCentralizer hij ell hell hneutral t⟩ g hgball hgroot heq

end DukePrimeDegree

end

end OAI
