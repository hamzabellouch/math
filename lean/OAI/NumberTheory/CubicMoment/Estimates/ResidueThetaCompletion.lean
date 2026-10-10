import OAI.NumberTheory.CubicMoment.Estimates.ThetaMellinGrowth
import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke

namespace OAI

/-! Exact analytic completion of a residue theta transformation. The
finite-character Poisson identity is the only remaining construction here;
no continuation, growth, or Dirichlet-series identity is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma residueTheta_completion {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) {root : ℂ} (hroot : root ≠ 0)
    (hFE : ∀ t : ℝ, 0 < t →
      idealTheta (residueHeckeScale q) (residueIdealChar q χ) (1/t) =
        root*(t:ℂ)*idealTheta (residueHeckeScale q) (residueIdealChar q (star χ)) t) :
    ∃ L Ldual : ℂ → ℂ, Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s = normDirichletSeries (residueIdealChar q χ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries (residueIdealChar q (star χ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) 0 root L Ldual ∧
      CompletedHeckeFiniteOrder (residueHeckeScale q) L := by
  have hA := residueHeckeScale_pos hq
  have hχ := residueIdealChar_norm_le_one hq χ
  have hd := residueIdealChar_norm_le_one hq (star χ)
  let P := idealThetaFEPair hA (residueIdealChar q χ) (residueIdealChar q (star χ)) hχ hd hroot hFE
  have he := idealThetaFEPair_hecke hA (residueIdealChar q χ) (residueIdealChar q (star χ)) hχ hd hroot hFE
  exact ⟨thetaHeckeL (residueHeckeScale q) P.Λ,
    thetaHeckeL (residueHeckeScale q) P.symm.Λ,he.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2,
    idealThetaFEPair_finiteOrder hA (residueIdealChar q χ) (residueIdealChar q (star χ)) hχ hd hroot hFE⟩

end CubicFirstMoment

end

end OAI
