import OAI.Combinatorics.Progressions.Estimates.NativeFrozenMarkedLocalMark

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_formal_marked_restoration
    (T : D.Niltest w) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (c : Basis κ ℚ M) (v : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {k | j ≤ v k}))
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : G.realification.PolynomialOrbit w) :
    ∃ restored : D.Niltest w,
      restored.observable = T.observable ∧
      restored.normBound = T.normBound ∧ restored.lipBound = T.lipBound ∧
      (∀ p, restored.ComplexityLE p ↔ T.ComplexityLE p) ∧
      (restored.UnitIntervalValued ↔ T.UnitIntervalValued) ∧
      map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) restored.orbit.log = q.log ∧
      ∀ z : σ → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
          (D.filtration.realification.polynomialOrbitEval w z T.orbit) =
            G.realification.polynomialOrbitEval w z q →
        restored.eval z = T.eval z := by
  obtain ⟨orbit, hmap, _, heval⟩ := D.filtration.exists_formal_marked_orbit_restoration
    G φ hφ c v hG hsurj w T.orbit q
  refine ⟨T.withOrbit orbit, rfl, rfl, rfl, fun _ => Iff.rfl, Iff.rfl, hmap, ?_⟩
  intro z hz
  have hz' : NilpotentLieBCHGroup.realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w (fun i => (z i : ℝ)) T.orbit) =
          G.realification.polynomialOrbitRealEval w (fun i => (z i : ℝ)) q := by
    simpa only [NilpotentLieFiltration.polynomialOrbitRealEval_integer] using hz
  have h := heval (fun i => (z i : ℝ)) hz'
  simp only [NilpotentLieFiltration.polynomialOrbitRealEval_integer] at h
  exact congrArg (fun g : D.RealGroup => T.observable (QuotientGroup.mk g)) h

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
