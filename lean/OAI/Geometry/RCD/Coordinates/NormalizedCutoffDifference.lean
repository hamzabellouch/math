import OAI.Geometry.RCD.Sobolev.CutoffDifferenceEnergy

namespace OAI

/-! # The exact cutoff comparison in normalized physical units -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem normalized_cutoff_difference_energy (w q η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B A : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x|≤B) (hn : ∀ x, 0≤v x)
    (hrep : SobolevSpace.toLp μ hQ η=ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ η x≤A)
    {Ω : Set X} (hsupp : tsupport v⊆Ω) {a r : ℝ} (hr : 0<r)
    (hmass : 0<μ.real Ω) (hw : IsConstantLaplacianOn μ hQ Ω w (a/r^2)) :
    r^2*(μ.real Ω)⁻¹*(∫ x in Ω, (v x)^2*localGamma μ hQ (w-q) (w-q) x ∂μ)=
      r^2*(μ.real Ω)⁻¹*(∫ x in Ω, (v x)^2*localGamma μ hQ q q x ∂μ)-
      r^2*(μ.real Ω)⁻¹*(∫ x in Ω, (v x)^2*localGamma μ hQ w w x ∂μ)-
      2*(a*(μ.real Ω)⁻¹*(∫ x in Ω, (v x)^2*SobolevSpace.toLp μ hQ (w-q) x ∂μ))-
      4*(r^2*(μ.real Ω)⁻¹*(∫ x in Ω,
        v x*SobolevSpace.toLp μ hQ (w-q) x*localGamma μ hQ w η x ∂μ)) := by
  have hz (x : X) (hx : x∉Ω) : v x=0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
  have hres (F : X → ℝ) : (∫ x, v x*F x ∂μ)=∫ x in Ω, v x*F x ∂μ := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hz x hx,zero_mul])
  have hres2 (F : X → ℝ) : (∫ x, (v x)^2*F x ∂μ)=∫ x in Ω, (v x)^2*F x ∂μ := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hz x hx,zero_pow (by decide : 2≠0),zero_mul])
  have hid := cutoff_difference_energy μ hQ w q η hv hs hb hn hrep hgrad hsupp hw
  rw [hres2,hres2,hres2] at hid
  have hc : (∫ x, v x*SobolevSpace.toLp μ hQ (w-q) x*localGamma μ hQ w η x ∂μ)=
      ∫ x in Ω, v x*SobolevSpace.toLp μ hQ (w-q) x*localGamma μ hQ w η x ∂μ := by
    simpa only [mul_assoc] using hres (fun x => SobolevSpace.toLp μ hQ (w-q) x*localGamma μ hQ w η x)
  rw [hc] at hid
  have he := congrArg (fun y : ℝ => r^2*(μ.real Ω)⁻¹*y) hid
  convert he using 1
  field_simp [hr.ne',hmass.ne']

end RegularPointCoordinates

end

end OAI
