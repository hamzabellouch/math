import OAI.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

namespace CertifiedFullChartFiniteHistory

variable {m s : ℕ} {X ι η L : Type} [Fintype ι] [Fintype η]
  [LieRing L] [LieAlgebra ℚ L]
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {W : LieSubalgebra ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule))}
  {lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem exists_rational_affine_globalMarkedNativeFactors
    (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
      Z Set.univ Utag poly N Bphase s)
    (hW : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule)
    (g : (F.realification.adaptedPolynomialFiltration wt).Group)
    (hZ : F.realPolynomialSymbolHom b ω hF wt g = Z)
    {p : ℝ} {blocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ history.K p blocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p) :
    let q := p + ((p + 2) ^ 2 + 2) ^ 63
    ∃ (V : ∀ j, Submodule ℚ (J j → ℚ))
      (P : ∀ j, Matrix (J j) (J j) ℚ) (D : Fin m → ℕ),
      history.K = {t | ∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈
        realRationalCoordinateSpan (V j)} ∧
      (∀ j,
        LinearMap.range (fullTaggedRealMatrixProjection J P j) = realRationalCoordinateSpan (V j) ∧
        (∀ x ∈ realRationalCoordinateSpan (V j), fullTaggedRealMatrixProjection J P j x = x) ∧
        (∀ i a, rationalLogHeight (P j i a) ≤ (q + 2) ^ 8) ∧
        0 < D j ∧ (D j : ℝ) ≤ Real.exp ((q + 2) ^ 10) ∧
        (∀ i a, ∃ z : ℤ, (D j : ℝ) * (P j i a : ℝ) = (z : ℝ)) ∧
        ∀ (l : ℕ) (x : J j → ℝ), x ∈ realDenominatorGrid l →
          fullTaggedRealMatrixProjection J P j x ∈ realDenominatorGrid (D j * l)) ∧
      ∀ c : ∀ j, J j → ℝ,
        let β := fullTaggedAffineMapChart (X := X) J (fullTaggedRealMatrixProjection J P) c
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF wt wt
          (fun i => weightedHomogeneousComponent wt (wt i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        Nonempty (GlobalMarkedNativeFactors F b ω hF wt W
          (F.weightedAdaptedRealChartHom wt wt β
            (fullTaggedAffineMapChart_support J _ c) g)
          (pull history.outer.1) (pull history.outer.2)) := by
  intro q
  obtain ⟨V, P, D, hK, hP⟩ := hcert.exists_bounded_rational_retractions J hp hdim hblocks
  refine ⟨V, P, D, hK, hP, ?_⟩
  intro c
  apply history.nonempty_globalMarkedNativeFactors hW _ _ g hZ
  intro t
  apply fullTaggedAffineMapChart_top_mem_set J (fullTaggedRealMatrixProjection J P) c
    (fun j => realRationalCoordinateSpan (V j))
  · intro j x
    rw [← (hP j).1]
    exact ⟨x, rfl⟩
  · intro y hy
    rw [hK]
    exact hy

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
