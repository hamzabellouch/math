import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation
import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # Local representatives and bounded truncation of Poisson solutions -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Agreement on the working set preserves every zero-boundary pairing. -/
theorem energyForm_eq_of_ae_eq_on {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g : SobolevSpace μ hQ}
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g)
    (φ : SobolevSpace.dirichlet μ hQ Ω) : energyForm μ hQ f φ.val = energyForm μ hQ g φ.val := by
  rw [← integral_localGamma_dirichlet μ hQ Ω hΩ f φ,
    ← integral_localGamma_dirichlet μ hQ Ω hΩ g φ]
  apply integral_congr_ae
  filter_upwards [hfg,ae_restrict_of_ae (localGamma_eq_on_eq μ hQ f g φ.val)] with x hx hlocal
  exact hlocal hx

/-- The local weak Poisson equation only depends on the representative
inside its domain. -/
theorem IsConstantLaplacianOn.congr_ae {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f g : SobolevSpace μ hQ} {c : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (hfg : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g) :
    IsConstantLaplacianOn μ hQ Ω g c := by
  intro φ hφ
  rw [← energyForm_eq_of_ae_eq_on μ hQ hΩ hfg ⟨φ,hφ⟩]
  exact hf φ hφ

/-- A local amplitude bound permits a globally bounded representative in
the same Sobolev class on the working domain, without changing its source. -/
theorem IsConstantLaplacianOn.bounded_extension {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f : SobolevSpace μ hQ} {c : ℝ} (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (A : ℝ≥0) (hA : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ A) :
    ∃ g : SobolevSpace μ hQ,
      IsConstantLaplacianOn μ hQ Ω g c ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ A) ∧
      SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g := by
  let g := SobolevSpace.compContraction μ hQ (clipReal_lipschitz A) (clipReal_zero A) f
  have hg : SobolevSpace.toLp μ hQ g =ᵐ[μ]
      fun x => clipReal A (SobolevSpace.toLp μ hQ f x) :=
    (clipReal_lipschitz A).coeFn_compLp (clipReal_zero A) _
  have heq : SobolevSpace.toLp μ hQ f =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ g := by
    filter_upwards [hA,ae_restrict_of_ae hg] with x hx he
    exact (he.trans (clipReal_eq_self A hx)).symm
  refine ⟨g,hf.congr_ae μ hQ hΩ heq,?_,heq⟩
  filter_upwards [hg] with x hx
  rw [hx]
  exact clipReal_abs_le _ _

end RegularPointCoordinates

end

end OAI
