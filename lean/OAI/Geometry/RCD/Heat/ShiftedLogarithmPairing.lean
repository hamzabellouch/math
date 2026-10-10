import OAI.Geometry.RCD.Coordinates.ShiftedLogarithmJets
import OAI.Geometry.RCD.Harmonic.WeightedAffineComposition

namespace OAI

/-! # Fixed Sobolev pairings for the logarithm and centered reciprocal -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem shifted_logarithm_gamma (u ℓ : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x∈Icc 0 (A:ℝ))
    (hℓ : SobolevSpace.toLp μ hQ ℓ =ᵐ[μ]
      fun x => Real.log (ε+SobolevSpace.toLp μ hQ u x)-Real.log ε)
    (w : SobolevSpace μ hQ) :
    localGamma μ hQ ℓ w =ᵐ[μ] fun x => localGamma μ hQ u w x /
      (ε+SobolevSpace.toLp μ hQ u x) := by
  obtain ⟨F,b,db,C,D,J,B,E,hF,hb,_hdb,hF0,hdF,_hdb',hB,_hE,he⟩ :=
    shifted_logarithm_jets hε A.coe_nonneg
  have heq : ℓ = SobolevSpace.comp μ hQ hF hF0 u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hℓ,SobolevSpace.comp_coe μ hQ hF hF0 u,hu] with x hx hy hz
    exact hx.trans ((he _ hz).1.symm.trans hy.symm)
  rw [heq]
  filter_upwards [localGamma_comp_C1 μ hQ u w hF hF0 hb.continuous hdF B hB,hu]
    with x hx hy
  rw [hx,(he _ hy).2.1]
  ring

theorem shifted_reciprocal_sobolev (u : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x∈Icc 0 (A:ℝ)) :
    ∃ (v : SobolevSpace μ hQ) (B : ℝ≥0),
      (SobolevSpace.toLp μ hQ v =ᵐ[μ] fun x =>
        (ε+SobolevSpace.toLp μ hQ u x)⁻¹-ε⁻¹) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ v x|≤B) ∧
      ∀ w : SobolevSpace μ hQ,
        localGamma μ hQ v w =ᵐ[μ] fun x =>
          -localGamma μ hQ u w x/(ε+SobolevSpace.toLp μ hQ u x)^2 := by
  obtain ⟨F,b,db,C,D,J,B,E,_hF,hb,hdb,_hF0,_hdF,hdb',hB,hE,he⟩ :=
    shifted_logarithm_jets hε A.coe_nonneg
  let v := SobolevSpace.comp μ hQ (centeredLipschitz hb) (sub_self _) u
  have hvr := SobolevSpace.comp_coe μ hQ (centeredLipschitz hb) (sub_self _) u
  have h0 : b 0=ε⁻¹ := by simpa only [add_zero] using (he 0 ⟨le_rfl,A.coe_nonneg⟩).2.1
  refine ⟨v,B+B,?_,?_,?_⟩
  · filter_upwards [hvr,hu] with x hx hy
    rw [hx]
    simp only [Function.comp_apply,(he _ hy).2.1,h0]
  · filter_upwards [hvr] with x hx
    rw [hx]
    exact (abs_sub _ _).trans (add_le_add (hB _) (hB 0))
  · intro w
    have hd (a : ℝ) : HasDerivAt (fun a => b a-b 0) (db a) a :=
      (hdb' a).sub_const _
    filter_upwards [localGamma_comp_C1 μ hQ u w (centeredLipschitz hb)
      (sub_self _) hdb.continuous hd E hE,hu] with x hx hy
    rw [hx,(he _ hy).2.2]
    ring

end RegularPointCoordinates

end

end OAI
