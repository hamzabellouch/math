import OAI.Analysis.KadisonKastler.TypeIIIDixmier

namespace OAI

/-! # Exact Dixmier averaging in a full finite matrix factor -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

private theorem matrix_size_positive {n : ℕ} (E : MatrixUnitSystem (Fin n) (Algebra M)) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  have he : (0 : Algebra M) = 1 := by simpa using E.total
  have he' : (0 : H →L[ℂ] H) = 1 := congrArg Subtype.val he
  exact zero_ne_one he'

/-- A full matrix presentation supplies a single exact scalar average. -/
theorem exists_exact_matrix_factor_average {n : ℕ}
    (E : MatrixUnitSystem (Fin n) (Algebra M)) (hE : Function.Surjective E.hom)
    (x : Algebra M) :
    ∃ (A : FiniteInnerAverage M) (z : ℂ), A.apply x.val = z • (1 : H →L[ℂ] H) := by
  let : Nonempty (Fin n) := ⟨⟨0, matrix_size_positive E⟩⟩
  let F := E.map M.toStarSubalgebra.subtype
  have hF : F.algebra ≤ M.toStarSubalgebra :=
    (F.algebra_le_iff _).mpr (fun i j => (E.entry i j).property)
  have hx : x.val ∈ F.algebra := by
    obtain ⟨a, ha⟩ := hE x
    apply (F.mem_algebra x.val).mpr
    refine ⟨a, ?_⟩
    have he : (E.hom a).val = ∑ i, ∑ j, a i j • F.entry i j := by
      let L : Algebra M →ₗ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype.toAlgHom.toLinearMap
      change L (∑ i, ∑ j, a i j • E.entry i j) = _
      simp only [map_sum, L.map_smul]
      rfl
    rw [← he]
    exact congrArg Subtype.val ha
  obtain ⟨z, hz⟩ := matrixUnitAverage_scalar F x.val hx
  exact ⟨matrixInnerAverage F hF, z, hz⟩

/-- The published conclusion for a represented finite full matrix factor. -/
theorem publishedDixmierOfFullMatrix {n : ℕ}
    (E : MatrixUnitSystem (Fin n) (Algebra M)) (hE : Function.Surjective E.hom) :
    PublishedDixmierAveraging M := by
  intro x hx
  obtain ⟨A, z, hz⟩ := exists_exact_matrix_factor_average E hE ⟨x, hx.1⟩
  refine ⟨z • (1 : H →L[ℂ] H),
    (concreteCenter M).toStarSubalgebra.smul_mem (concreteCenter M).one_mem _, ?_⟩
  rw [← hz]
  exact subset_closure (A.apply_mem_orbitHull x)

end

end KadisonKastler

end OAI
