import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.DerivativeLocalization
import OAI.Geometry.PrescribedPotential.LiteralWeakHessian

namespace OAI

/-! Weak Derivative Localization. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma distribution_embed_forcing (s : ℝ) (p : ι) (f : Smooth A) :
    D.localizers.distribution s p (D.localizers.embed s f) =
      SchwartzMap.toTemperedDistributionCLM (EC d) ℂ volume (D.forcing p f) := D.localizers.distribution_embed s p f

lemma completedLocalize_lower (k l : ℕ) (hlk : l ≤ k) (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source)
    (u : D.localizers.Sobolev (k : ℝ)) :
    realize (l : ℝ) (D.completedLocalize (l : ℝ) i ρ hρ
      (D.localizers.lower (k : ℝ) (l : ℝ) u)) =
      realize (k : ℝ) (D.completedLocalize (k : ℝ) i ρ hρ u) := by
  have hkl : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  have he : (fun u : D.localizers.Sobolev (k : ℝ) => realize (l : ℝ)
      (D.completedLocalize (l : ℝ) i ρ hρ (D.localizers.lower (k : ℝ) (l : ℝ) u))) =
      (fun u => realize (k : ℝ) (D.completedLocalize (k : ℝ) i ρ hρ u)) := by
    apply (D.localizers.embed_dense (k : ℝ)).equalizer (by fun_prop) (by fun_prop)
    funext f
    dsimp only [Function.comp_apply]
    simp only [D.localizers.lower_embed hkl,D.completedLocalize_embed,realize_schwartzCoord]
  exact congr_fun he u

lemma distribution_derivative (k : ℕ) (p : ι) (v : EC d)
    (u : D.localizers.Sobolev ((k : ℝ)+1)) :
    (∂_{v} (D.localizers.distribution ((k : ℝ)+1) p u) : 𝓢'(EC d,ℂ)) =
      realize (k : ℝ) (D.completedLocalize (k : ℝ) (D.patch p).index
        (D.localizedDerivative p v (D.localizers.weight p)) (D.derivativeWeight_support p v)
        (D.localizers.lower ((k : ℝ)+1) (k : ℝ) u)) +
      D.localizers.distribution (k : ℝ) p (D.completedDerivative k p v u) := by
  have he : (fun u : D.localizers.Sobolev ((k : ℝ)+1) =>
      (∂_{v} (D.localizers.distribution ((k : ℝ)+1) p u) : 𝓢'(EC d,ℂ))) =
      (fun u => realize (k : ℝ) (D.completedLocalize (k : ℝ) (D.patch p).index
        (D.localizedDerivative p v (D.localizers.weight p)) (D.derivativeWeight_support p v)
        (D.localizers.lower ((k : ℝ)+1) (k : ℝ) u)) +
      D.localizers.distribution (k : ℝ) p (D.completedDerivative k p v u)) := by
    apply (D.localizers.embed_dense ((k : ℝ)+1)).equalizer
      ((lineDerivOpCLM ℂ 𝓢'(EC d,ℂ) v).continuous.comp
        (D.localizers.distribution ((k : ℝ)+1) p).continuous) (by fun_prop)
    funext f
    dsimp only [Function.comp_apply]
    rw [D.distribution_embed_forcing,D.localizers.lower_embed (by linarith : (k : ℝ) ≤ (k : ℝ)+1),
      D.completedLocalize_embed,realize_schwartzCoord,D.completedDerivative_embed,
      D.distribution_embed_forcing,lineDerivOpCLM_apply,
      lineDerivOp_toTemperedDistributionCLM_eq,D.forcing_derivative,map_add]
  exact congr_fun he u

end GluingData
end GlobalElliptic

end
end

end OAI
