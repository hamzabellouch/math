import OAI.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison

namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_residue_event_or_anchored_child (s : ℕ) (hs : 1 ≤ s) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (V : RationalFilteredNilmanifold K t e)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (q₀ P C a : ℕ) (hP : 0 < P) (cost : ℝ),
      FixedResidueDescent D W V (fun _ : σ => 1) b child p q₀ P hP C a cost →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
          ⟨⟨T.orbit.log, T.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q₀ R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp ((p + 2) ^ a)) E →
          ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (_hM : 0 < M) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ _hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)],
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF T W lo N M u v J ((q + B) ^ B) ∨
          AnchoredChildResidueComparison V child cost (Δ / 4) δ lo N M P u v J := by
  obtain ⟨B, hB, hstep⟩ := exists_residue_event_or_child_descent s hs
  refine ⟨B, hB, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ d t e D V ω hF p q rho hp hpq hσ hfreq hrho hrhop
    W b child q₀ P C a hP cost hdesc T hunit hT E R κ hκ hprod hgrid A hA hE
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  rcases hstep D V ω hF p q rho hp hpq hσ hfreq hrho hrhop W b child q₀ P C a hP cost
    hdesc T hunit hT E R κ hκ hprod hgrid A hA hE lo N M hM u v J hJ hv hcop hsteplarge
    Δ ε δ hδ hδone hε hprojection hfreezing hlarge hphysical hcount hgap with hevent | hchild
  · exact Or.inl hevent
  · obtain ⟨H, hH, hHN, hlower, hupper, k, hk₀, hk₁, U, hU, hunitU, hcostU, hgapU⟩ := hchild
    exact Or.inr (anchored_child_comparison_of_piece V child cost (Δ / 4) δ lo N H hH hHN
      hlower hupper M P hM hP u v J hv hcop k hk₀ hk₁ U hU hunitU hcostU hgapU)

end Erdos3

end

end OAI
