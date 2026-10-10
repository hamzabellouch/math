import OAI.Geometry.RCD.Sobolev.HessianActionChain

namespace OAI

/-! # Two logarithmic directions in the actual Hessian action -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem exists_local_hessian_log_directions {Ω : Set X}
    (f u v fu fv uv : SobolevSpace μ Q) (A B C : ℝ≥0)
    (hfuB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fu x| ≤ A)
    (hfvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fv x| ≤ B)
    (huvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q uv x| ≤ C)
    (hfu : SobolevSpace.toLp μ Q fu =ᵐ[μ.restrict Ω] localGamma μ Q f u)
    (hfv : SobolevSpace.toLp μ Q fv =ᵐ[μ.restrict Ω] localGamma μ Q f v)
    (huv : SobolevSpace.toLp μ Q uv =ᵐ[μ.restrict Ω] localGamma μ Q u v)
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hu : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a b)
    (hv : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q v x ∈ Icc c d) :
    ∃ U V fU fV UV : SobolevSpace μ Q,
      (SobolevSpace.toLp μ Q U =ᵐ[μ.restrict Ω]
        fun x => Real.log (SobolevSpace.toLp μ Q u x)) ∧
      (SobolevSpace.toLp μ Q V =ᵐ[μ.restrict Ω]
        fun x => Real.log (SobolevSpace.toLp μ Q v x)) ∧
      (SobolevSpace.toLp μ Q fU =ᵐ[μ.restrict Ω] localGamma μ Q f U) ∧
      (SobolevSpace.toLp μ Q fV =ᵐ[μ.restrict Ω] localGamma μ Q f V) ∧
      (SobolevSpace.toLp μ Q UV =ᵐ[μ.restrict Ω] localGamma μ Q U V) ∧
      (∃ A : ℝ≥0, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fU x| ≤ A) ∧
      (∃ A : ℝ≥0, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q fV x| ≤ A) ∧
      (∃ A : ℝ≥0, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q UV x| ≤ A) ∧
      localHessianAction μ Q f U V fU fV UV =ᵐ[μ.restrict Ω] fun x =>
        localHessianAction μ Q f u v fu fv uv x /
          (SobolevSpace.toLp μ Q u x*SobolevSpace.toLp μ Q v x) := by
  obtain ⟨V,fV,uV,hV,hfV,huV,hfVB,⟨CV,huVB⟩,hlogV⟩ :=
    exists_local_hessian_log_direction μ Q f u v fu fv uv B C
      hfvB huvB hfv huv hc hcd hv
  have hVu : SobolevSpace.toLp μ Q uV =ᵐ[μ.restrict Ω] localGamma μ Q V u :=
    huV.trans (ae_restrict_of_ae (localGamma_comm μ Q u V))
  obtain ⟨U,fU,VU,hU,hfU,hVU,hfUB,hVUB,hlogU⟩ :=
    exists_local_hessian_log_direction μ Q f V u fV fu uV A CV
      hfuB huVB hfu hVu ha hab hu
  refine ⟨U,V,fU,fV,VU,hU,hV,hfU,hfV,?_,hfUB,hfVB,hVUB,?_⟩
  · exact hVU.trans (ae_restrict_of_ae (localGamma_comm μ Q V U))
  · filter_upwards [hlogU,hlogV] with x hx hy
    have hsym : ∀ a b fa fb ab : SobolevSpace μ Q,
        localHessianAction μ Q f a b fa fb ab x = localHessianAction μ Q f b a fb fa ab x := by
      intros
      dsimp only [localHessianAction]
      ring
    rw [hsym U V fU fV VU,hx,hsym V u fV fu uV,hy,div_div,mul_comm]

end RegularPointCoordinates

end

end OAI
