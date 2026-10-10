import OAI.NumberTheory.DukePrimeDegree.Arithmetic.ExceptionalSetExclusion
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingSelectedConvergence

namespace OAI

/-!
# Noncentral neutral return matrices tending to identity

The proved nullity of exceptional return sets supplies arbitrarily small
noncentral lifts on every positive-measure set. Choosing exponentially
shrinking neighborhoods gives the sequence needed for shearing.
Leaf-data equality along the neutral return is not assumed here.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_noncentral_neutral_return
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ x ∈ K, ∃ ell : Fin (d + 1) → ℝ, ∃ hell : ∑ a, ell a = 0,
      ell i = ell j ∧ rightAction x (diagonalOneParameter ell hell 1) ∈ K ∧
      ∃ g ∈ matrixBall (d + 1) r,
        rightAction x g = rightAction x (diagonalOneParameter ell hell 1) ∧
        g ∉ singleRootCentralizer hij := by
  by_contra h
  apply hpos
  apply exceptional_neutral_return_set_null d hd hij μ hA K hK r hr
  intro x hx ell hell hn hy g hg heq
  by_contra hnot
  exact h ⟨x, hx, ell, hell, hn, hy, g, hg, heq, hnot⟩

lemma tendsto_one_of_shrinking_matrixBall
    {n : ℕ} (g : ℕ → G n) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hg : ∀ m, g m ∈ matrixBall n (r m)) : Tendsto g atTop (𝓝 1) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun m => abs_nonneg _) (fun m => (hg m a b).le) hr

theorem exists_noncentral_neutral_return_sequence
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ (x y : ℕ → X (d + 1)) (g : ℕ → G (d + 1)),
      Tendsto g atTop (𝓝 1) ∧ ∀ m,
        x m ∈ K ∧ y m ∈ K ∧ rightAction (x m) (g m) = y m ∧
        (¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g m) ∧
        ∃ ell : Fin (d + 1) → ℝ, ∃ hell : ∑ a, ell a = 0,
          ell i = ell j ∧ rightAction (x m) (diagonalOneParameter ell hell 1) = y m := by
  have hex (m : ℕ) := exists_noncentral_neutral_return d hd hij μ hA K hK hpos
    (Real.exp (-(m : ℝ))) (Real.exp_pos _)
  choose x hx ell hell hn hy g hg heq hnot using hex
  let y : ℕ → X (d + 1) := fun m => rightAction (x m) (diagonalOneParameter (ell m) (hell m) 1)
  refine ⟨x, y, g, ?_, ?_⟩
  · apply tendsto_one_of_shrinking_matrixBall g (fun m => Real.exp (-(m : ℝ))) _ hg
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  · intro m
    refine ⟨hx m, hy m, heq m, ?_, ell m, hell m, hn m, rfl⟩
    intro hc
    exact hnot m ((mem_singleRootCentralizer hij (g m)).mpr (hc 1))

end DukePrimeDegree

end

end OAI
