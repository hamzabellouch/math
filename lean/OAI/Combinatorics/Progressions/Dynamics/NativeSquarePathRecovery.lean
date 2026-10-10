import OAI.Combinatorics.Progressions.Estimates.NativeSquareRecovery

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct

theorem exists_native_square_path_recovery (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)] {p : ℝ},
      2 ≤ p → D.GeometryComplexityLE p →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (w : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
        (m : ℕ) (hm : 0 < m)
        (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates
          (D.filtration.squareFinBasis b w (hF 2)) (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b w (hF 2))
          (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid m),
        let V := D.filtration.squareFiltration.ofAdaptedBasis
          (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
          (D.filtration.squareFinBasis_layers b w hF)
          (D.filtration.squareLattice D.lattice) m hm hin hout
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        V.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (Δ : Bool → Subgroup D.filtration.Group) (l : Bool → ℕ)
          (hl : ∀ i, 0 < l i)
          (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates D.basis (Δ i))
          (hlout : ∀ i, bchSubgroupCoordinates D.basis (Δ i) ⊆ denominatorGrid (l i)),
          let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
          (∀ i, Δ i ≤ D.lattice ∧ ((Δ i).subgroupOf D.lattice).Characteristic ∧
            ((Δ i).subgroupOf D.lattice).Normal ∧ ((Δ i).subgroupOf D.lattice).FiniteIndex ∧
            ((Δ i).relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
          (∀ i, (E i).GeometryComplexityLE ((p + C) ^ C)) ∧
          letI : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
          letI := V.metricSpace
          ∀ {σ : Type*} (ω : σ → ℕ), (∀ i, 0 < ω i) →
            ∀ (g : D.filtration.realification.PolynomialOrbit ω) (a b : σ → ℤ),
            ∃ (ε γ : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit ω),
              γ ∈ D.realLattice ∧
              (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : σ → ℤ,
                D.filtration.realSquareFstHom
                  (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q) =
                    ε⁻¹ * D.filtration.realification.polynomialOrbitEval ω (x + a) g * γ⁻¹ ∧
                D.filtration.realSquareSndHom
                  (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q) =
                    D.filtration.realification.polynomialOrbitEval ω (x + b) g) ∧
              ∀ (x y : σ → ℤ) (ρ : ℝ), 0 ≤ ρ → ρ ≤ Real.exp (-((p + C) ^ C)) →
                dist (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (x + a) g) :
                  (E true).Space)
                  (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (y + a) g)) ≤ ρ →
                dist (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (x + b) g) :
                  (E false).Space)
                  (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval ω (y + b) g)) ≤ ρ →
                dist (QuotientGroup.mk
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q) : V.Space)
                  (QuotientGroup.mk
                    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω y q)) ≤
                      Real.exp ((p + C) ^ C) * ρ := by
  obtain ⟨A, _, hnorm⟩ := exists_native_two_shift_normalization s
  obtain ⟨B, _, hrec⟩ := exists_native_square_recovery s A
  let X : Polynomial ℕ := Polynomial.X
  let R := X + Polynomial.C A + 1
  let P := (R + Polynomial.C B) ^ B + (X + 1 + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L _ _ d _ _ _ _ D _ _ _ _ p hp hD
  have hp0 : 0 ≤ p := by linarith
  let r := p + A + 1
  have hpr : p ≤ r := by
    have hA : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    dsimp [r]
    linarith
  have hr : 2 ≤ r := hp.trans hpr
  obtain ⟨b, w, hF, m, hm, hin, hout, hb, hV, Δ, l, hl, hlin, hlout, hindex, hE, hrecover⟩ :=
    hrec D hr (hD.mono D hpr)
  let V := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b w (hF 2)) (NilpotentLieFiltration.squareFinWeight w)
    (D.filtration.squareFinBasis_layers b w hF)
    (D.filtration.squareLattice D.lattice) m hm hin hout
  let E := fun i => D.withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i)
  have hsum : (r + B) ^ B + (p + 1 + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, R, P, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hBC : (r + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans hsum
  have hAC : (p + 1 + A) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (by dsimp [r]; positivity) _)).trans hsum
  refine ⟨b, w, hF, m, hm, hin, hout, fun i j => (hb i j).trans hBC, hV.mono V hBC,
    Δ, l, hl, hlin, hlout, ?_, fun i => (hE i).mono (E i) hBC, ?_⟩
  · intro i
    rcases hindex i with ⟨hle, hchar, hnormal, hfinite, hi⟩
    exact ⟨hle, hchar, hnormal, hfinite, hi.trans (Real.exp_le_exp.mpr hBC)⟩
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  let := V.metricSpace
  dsimp only
  intro σ ω hω g a b
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D hp0 hD ω hω a b g
  refine ⟨ε, γ, q, hγ, fun i => (hε i).trans (Real.exp_le_exp.mpr hAC), hq, ?_⟩
  intro x y ρ hρ hsmall hfirst hsecond
  have hεr : ∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((r + 2) ^ A) := by
    intro i
    apply (hε i).trans
    apply Real.exp_le_exp.mpr
    apply pow_le_pow_left₀ (by positivity) _ A
    dsimp [r]
    linarith
  have hd := hrecover ε γ hγ hεr
    (D.filtration.realification.polynomialOrbitEval ω (x + a) g)
    (D.filtration.realification.polynomialOrbitEval ω (x + b) g)
    (D.filtration.realification.polynomialOrbitEval ω (y + a) g)
    (D.filtration.realification.polynomialOrbitEval ω (y + b) g)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω x q)
    (D.filtration.squareFiltration.realification.polynomialOrbitEval ω y q)
    (hq x).1 (hq x).2 (hq y).1 (hq y).2 ρ hρ
    (hsmall.trans (Real.exp_le_exp.mpr (neg_le_neg hBC))) hfirst hsecond
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hBC) hρ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
