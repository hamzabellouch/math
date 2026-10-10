import OAI.Analysis.KadisonKastler.MatrixCommutantSpatialSplit
import OAI.Analysis.KadisonKastler.FiniteFactorDixmier

namespace OAI

/-! # Spatial splitting for a finite type I commutant in any multiplicity -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_finite_typeI_commutant
    (M : VonNeumannAlgebra H) (hN : IsTypeIFactor M.commutant)
    (hfinite : FiniteProjectionIn M.commutant 1)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant := by
  obtain ⟨p, hp⟩ := hN.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M.commutant ξ
  let e := typeICyclicEquiv hN.factor p hp ξ hξ hpξ
  have hK : ∀ v : K →L[ℂ] K, star v * v = 1 → v * star v = 1 := by
    intro v hv
    let a := e.symm v
    have hi : star a * a = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      have hs : e (star a) = star v :=
        (e.map_star' a).trans (congrArg star (e.apply_symm_apply v))
      change e (star a) * e a = 1
      rw [hs, e.apply_symm_apply]
      exact hv
    have ho := hfinite a hi (one_mul _)
    have he := congrArg e ho
    have hs : e (star a) = star v :=
      (e.map_star' a).trans (congrArg star (e.apply_symm_apply v))
    rw [map_mul, map_one] at he
    change e a * e (star a) = 1 at he
    rw [hs, e.apply_symm_apply] at he
    exact he
  let _ : FiniteDimensional ℂ K := finiteDimensional_of_all_isometries_coisometric hK
  let b := stdOrthonormalBasis ℂ K
  let E := (orthonormalMatrixUnits b).map e.symm.toStarAlgHom
  have hE : Function.Surjective E.hom := by
    intro a
    obtain ⟨c, hc⟩ := orthonormalMatrixUnits_surjective b (e a)
    refine ⟨c, ?_⟩
    rw [matrixUnits_map_hom, hc]
    exact e.symm_apply_apply a
  let F := E.map M.commutant.toStarSubalgebra.subtype
  have hF : F.algebra ≤ M.commutant.toStarSubalgebra :=
    (F.algebra_le_iff _).mpr (fun i j => (E.entry i j).property)
  have hfull : M.commutant.toStarSubalgebra ≤ F.algebra := by
    intro x hx
    obtain ⟨c, hc⟩ := hE ⟨x, hx⟩
    apply (F.mem_algebra x).mpr
    refine ⟨c, ?_⟩
    have he : (E.hom c).val = ∑ i, ∑ j, c i j • F.entry i j := by
      let L : Algebra M.commutant →ₗ[ℂ] (H →L[ℂ] H) :=
        M.commutant.toStarSubalgebra.subtype.toAlgHom.toLinearMap
      change L (∑ i, ∑ j, c i j • E.entry i j) = _
      simp only [map_sum, L.map_smul]
      rfl
    rw [← he]
    exact congrArg Subtype.val hc
  exact exists_selfAdjoint_split_of_matrix_commutant M F hF hfull T hTsa hT

end

end KadisonKastler

end OAI
