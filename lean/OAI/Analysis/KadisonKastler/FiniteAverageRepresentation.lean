import OAI.Analysis.KadisonKastler.FiniteInnerTransport

namespace OAI

/-! # Transporting finite averages between represented algebras -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

namespace FiniteInnerAverage

/-- Pull each finite averaging unitary back to the original representation. -/
def pullback (A : FiniteInnerAverage N) (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) :
    FiniteInnerAverage M where
  Index := A.Index
  fintype := A.fintype
  nonempty := A.nonempty
  unitary i := Unitary.map (StarMonoidHom.ofClass e.symm) (A.unitary i)

theorem pullback_algebraApply (A : FiniteInnerAverage N)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (x : Algebra M) :
    e ((A.pullback e).algebraApply x) = A.algebraApply (e x) := by
  let L : Algebra M →ₗ[ℂ] Algebra N := e.toAlgEquiv.toLinearMap
  change L ((Fintype.card A.Index : ℂ)⁻¹ •
      (∑ i, e.symm (A.unitary i) * x * star (e.symm (A.unitary i)))) =
    (Fintype.card A.Index : ℂ)⁻¹ • ∑ i,
      (A.unitary i : Algebra N) * e x * star (A.unitary i : Algebra N)
  rw [L.map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change e (e.symm (A.unitary i) * x * star (e.symm (A.unitary i))) = _
  rw [map_mul, map_mul, e.apply_symm_apply]
  congr 1
  have hs : e (star (e.symm (A.unitary i))) = star (A.unitary i : Algebra N) := by
    exact (e.map_star' _).trans (congrArg star (e.apply_symm_apply _))
  exact hs

/-- Isometric algebra transport preserves the scalar approximation error. -/
theorem pullback_norm_error (A : FiniteInnerAverage N)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (he : ∀ x : Algebra M, ‖e x‖ = ‖x‖)
    (x : Algebra M) (z : ℂ) :
    ‖(A.pullback e).apply x.val - z • (1 : H →L[ℂ] H)‖ =
      ‖A.apply (e x).val - z • (1 : K →L[ℂ] K)‖ := by
  rw [← (A.pullback e).algebraApply_val, ← A.algebraApply_val]
  change ‖(A.pullback e).algebraApply x - z • (1 : Algebra M)‖ =
    ‖A.algebraApply (e x) - z • (1 : Algebra N)‖
  rw [← he, map_sub, A.pullback_algebraApply]
  have hs : e (z • (1 : Algebra M)) = z • (1 : Algebra N) := by
    calc
      e (z • (1 : Algebra M)) = z • e 1 := e.map_smul' _ _
      _ = _ := by rw [map_one]
  rw [hs]

end FiniteInnerAverage

end

end KadisonKastler

end OAI
