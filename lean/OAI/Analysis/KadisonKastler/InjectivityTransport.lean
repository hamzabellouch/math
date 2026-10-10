import OAI.Analysis.KadisonKastler.Amenable
import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! # Transport of an ambient contractive projection

An isomorphism of represented algebras transports injectivity whenever
it extends to a contractive linear map of the ambient operator spaces.
The application uses compression of a countable diagonal amplification.
-/

namespace KadisonKastler

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isInjective_of_contracting_extension
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    (R : (H →L[ℂ] H) →ₗ[ℂ] (K →L[ℂ] K))
    (hR : ∀ T, ‖R T‖ ≤ ‖T‖)
    (hRa : ∀ a : Algebra M, R a.val = (e a).val)
    (hN : IsInjective N) : IsInjective M := by
  let : CStarAlgebra (Algebra M) := {}
  let : CStarAlgebra (Algebra N) := {}
  obtain ⟨E, hE, hEN, hfix⟩ := hN
  let E₀ : (K →L[ℂ] K) →ₗ[ℂ] Algebra N :=
    { toFun T := ⟨E T, hEN T⟩
      map_add' T S := Subtype.ext (map_add E T S)
      map_smul' c T := Subtype.ext (map_smul E c T) }
  let F : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) :=
    M.toStarSubalgebra.subtype.toAlgHom.toLinearMap.comp
      (e.symm.toAlgEquiv.toLinearMap.comp (E₀.comp R))
  have he (a : Algebra N) : ‖e.symm a‖ = ‖a‖ :=
    NonUnitalStarAlgHom.norm_map e.symm.toStarAlgHom e.symm.injective a
  have hF (T : H →L[ℂ] H) : ‖F T‖ ≤ ‖T‖ := by
    change ‖e.symm (E₀ (R T))‖ ≤ ‖T‖
    rw [he]
    change ‖E (R T)‖ ≤ ‖T‖
    exact ((E.le_opNorm (R T)).trans
      (by nlinarith [norm_nonneg (R T)])).trans (hR T)
  let P := F.mkContinuous 1 (fun T => by simpa only [one_mul] using hF T)
  refine ⟨P, P.opNorm_le_bound zero_le_one (fun T => by
    change ‖F T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using hF T), ?_, ?_⟩
  · intro T
    exact (e.symm (E₀ (R T))).property
  · intro T hT
    let a : Algebra M := ⟨T, hT⟩
    have hE₀ : E₀ (R a.val) = e a := by
      apply Subtype.ext
      change E (R a.val) = (e a).val
      rw [hRa]
      exact hfix _ (e a).property
    change (e.symm (E₀ (R a.val))).val = a.val
    rw [hE₀, e.symm_apply_apply]

end

end KadisonKastler

end OAI
