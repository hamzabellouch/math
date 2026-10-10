import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistSliceVariationPairCorrelation

namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_trimmed_fixed_outer_cells
    {A K X Ω : Type*} [Fintype A] [Fintype K] [DecidableEq K] [Fintype X] [Fintype Ω]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] [IsEmpty (Σ j, J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}
    (W : A → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (P : K → ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hperiod : ((∏ a, (W a).modulus : ℕ) : ℝ) ≤ Real.exp p)
    (hP : ∀ k, Real.exp (3 * p + 16) ≤ (P k : ℝ))
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (B τ : ℝ) (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hPB : (∑ k, (P k : ℝ)) ≤ B)
    (z : Ω → A → rectangularWeightIndices 0 (trimmedSpatialWidths (K := K) B τ N) 1)
    (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (μ : Ω → A → FiniteProbabilityWeights (∀ k, Fin (P k)))
    (signal : Ω → A → (∀ k, Fin (P k)) → ℂ)
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hproductive : κ ≤ outer.mass productive)
    (hsignal : ∀ ω ∈ productive, ∀ a t, ‖signal ω a t‖ ≤ 1)
    (hbias : ∀ ω ∈ productive, ∀ a,
      δ ≤ ‖(μ ω a).complexMean (fun t => star ((W a).eval N poly
        (centeredIntegerPhysicalSite (fun k => ((t k).val : ℤ)) N (z ω a).val)) * signal ω a t)‖) :
    ∃ (Q : ∀ k, FiniteProgressionPartition (P k))
      (cell : A → ∀ k, (Q k).Label) (retained : Finset Ω),
      (∀ k c, (Q k).step c = ∏ a, (W a).modulus) ∧
      (∀ k c, 0 < (Q k).length c) ∧
      (∀ k c, (P k : ℝ) * Real.exp (-(3 * p + 16)) ≤ (Q k).length c) ∧
      (Fintype.card (∀ k, (Q k).Label) : ℝ) ≤
        Real.exp (Fintype.card K * (3 * p + 16)) ∧
      retained ⊆ productive ∧ retained.Nonempty ∧ 0 < outer.mass retained ∧
      κ * Real.exp (-((Fintype.card K * (3 * p + 16)) * Fintype.card A)) ≤
        outer.mass retained ∧
      ∀ ω ∈ retained, ∀ a,
        ∃ hc : 0 < (μ ω a).mass
            (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = cell a)),
          δ / (2 * Fintype.card (∀ k, (Q k).Label)) ≤ (μ ω a).mass
            (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = cell a)) ∧
          δ / 2 - (L : ℝ) * Real.exp (-(2 * p)) * τ / 32 ≤
            ‖((μ ω a).condition
              (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = cell a))
              hc).complexMean (signal ω a)‖ := by
  obtain ⟨Q, hstep, hlength, hlower, hcard, hlocal⟩ :=
    exists_trimmed_local_parameter_cells_with_correlation W P p hp hperiod hP
  let rel := fun (ω : Ω) (a : A) (c : ∀ k, (Q k).Label) =>
    ∃ hc : 0 < (μ ω a).mass
        (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c)),
      δ / (2 * Fintype.card (∀ k, (Q k).Label)) ≤ (μ ω a).mass
        (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c)) ∧
      δ / 2 - (L : ℝ) * Real.exp (-(2 * p)) * τ / 32 ≤
        ‖((μ ω a).condition
          (Finset.univ.filter (fun t => BoxProgressionPartition.cell Q t = c))
          hc).complexMean (signal ω a)‖
  have hrel : ∀ ω ∈ productive, ∀ a, ∃ c, rel ω a c := by
    intro ω hω a
    exact hlocal N hN poly B τ hB hτ hPB (z ω) a (μ ω a) (signal ω a) δ hδ
      (hsignal ω hω a) (hbias ω hω a)
  obtain ⟨cell, retained, hsub, hn, hpos, hmass, hretained⟩ :=
    outer.exists_fixed_outer_cells_exp productive rel hκ hproductive hrel hcard
  exact ⟨Q, cell, retained, hstep, hlength, hlower, hcard, hsub, hn, hpos, hmass, hretained⟩

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
