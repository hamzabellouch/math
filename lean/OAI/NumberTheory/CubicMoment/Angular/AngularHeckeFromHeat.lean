import OAI.NumberTheory.CubicMoment.Angular.AngularHeatLattice
import OAI.NumberTheory.CubicMoment.Estimates.PublishedAngularHecke

namespace OAI

/-! The actual angular Hecke analytic package follows from its finite
character theta transformation. This introduces no analytic input. -/
noncomputable section
namespace CubicFirstMoment

lemma angularHecke_from_heatTransformation {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1) (root : ℂ) (hr : ‖root‖ = 1)
    (hFE : ∀ t : ℝ, 0 < t →
      angularLatticeHeat q χ ℓ (residueHeckeScale q) (|(ℓ:ℝ)|/2) (1/t) =
        root*(t:ℂ)*angularLatticeHeat q (star χ) (-ℓ)
          (residueHeckeScale q) (|(ℓ:ℝ)|/2) t) :
    ∃ (L Ldual : ℂ → ℂ), Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar q χ ℓ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar q (star χ) (-ℓ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) (|(ℓ:ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) (|(ℓ:ℝ)|/2) L := by
  have hr0 : root ≠ 0 := by
    intro he
    rw [he,norm_zero] at hr
    norm_num at hr
  exact idealHeat_completion (residueHeckeScale_pos hq) (by positivity) _ _
    (angularResidueIdealChar_norm_le_one hq χ ℓ)
    (angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ)) hr0
    (angularHeat_inversion_of_lattice hq χ ℓ hu hn (residueHeckeScale_pos hq) (by positivity) hFE)

end CubicFirstMoment

end

end OAI
