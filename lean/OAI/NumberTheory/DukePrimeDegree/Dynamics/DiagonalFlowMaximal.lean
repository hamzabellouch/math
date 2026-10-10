import OAI.NumberTheory.DukePrimeDegree.Dynamics.FlowMaximal

namespace OAI

/-!
# Uniform long-time returns for the diagonal flow

This specializes the proved maximal occupation bound to the actual
canonical diagonal flow on the arithmetic quotient.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma continuous_diagonalOneParameter {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i = 0) : Continuous (diagonalOneParameter ell hell) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun t : ℝ => Matrix.diagonal (fun k => Real.exp (ell k * t)) i j)
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq]
    fun_prop
  · simp only [Matrix.diagonal_apply_ne _ hij]
    exact continuous_const

theorem exists_diagonal_return_good_set
    (d : ℕ) (j : Fin (d + 1)) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (E : Set (X (d + 1))) (hE : MeasurableSet E) (c : ℝ) (hc : 0 < c) :
    ∃ G : Set (X (d + 1)), MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal (2 * μ.real E / c) ∧
      ∀ x ∈ G, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩
          {t | rightAction x (rootCanonicalFlow d j (-2 * t)) ∈ E}) ≤ c * T := by
  let Φ : ℝ → X (d + 1) → X (d + 1) :=
    fun t x => rightAction x (rootCanonicalFlow d j (-2 * t))
  have hcont : Continuous (fun p : X (d + 1) × ℝ => Φ p.2 p.1) := by
    have hD : Continuous (fun p : X (d + 1) × ℝ => rootCanonicalFlow d j (-2 * p.2)) :=
      (continuous_diagonalOneParameter (rootCanonicalWeights d j)
        (rootCanonicalWeights_sum d j)).comp (continuous_const.mul continuous_snd)
    exact (continuous_rightAction_uncurry (d + 1)).comp (continuous_fst.prodMk hD)
  have hzero (x : X (d + 1)) : Φ 0 x = x := by
    simp [Φ, rootCanonicalFlow, diagonalOneParameter_zero]
  have hadd (s t : ℝ) (x : X (d + 1)) : Φ (s + t) x = Φ s (Φ t x) := by
    dsimp [Φ, rootCanonicalFlow]
    rw [rightAction_mul, ← diagonalOneParameter_add]
    congr 2
    ring
  exact exists_flow_return_good_set μ hcont.measurable hzero hadd
    (fun t => rootCanonicalFlow_preserving d j (-2 * t) μ hA) hE c hc

end DukePrimeDegree

end

end OAI
