import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # Removing the auxiliary compact contact representative

Equality with a scaled heat slice on the transported measure identifies
both its gradient length and every weak velocity pairing.
-/

open Filter MeasureTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem scaled_contact_gradient_length {ν : Measure X} (hν : ν ≪ μ)
    (u v : SobolevSpace μ Q) {s M : ℝ} (hs : 0 < s) (D : X → ℝ)
    (hu : ∀ᵐ x ∂ν, SobolevSpace.toLp μ Q u x =
      -(s/2)*SobolevSpace.toLp μ Q v x-M)
    (hd : ∀ᵐ x ∂ν, SobolevSpace.minimalSlope μ Q u x = s*D x) :
    ∀ᵐ x ∂ν, SobolevSpace.minimalSlope μ Q v x = 2*D x := by
  let a := -(s/2)
  have hcoeff : ∀ᵐ x ∂ν, SobolevSpace.toLp μ Q (a • v) x =
      a*SobolevSpace.toLp μ Q v x := by
    rw [map_smul]
    exact (Lp.coeFn_smul a (SobolevSpace.toLp μ Q v)).filter_mono hν.ae_le
  have hgrad : ∀ᵐ x ∂ν, SobolevSpace.minimalSlope μ Q (a • v) x =
      |a| *SobolevSpace.minimalSlope μ Q v x := by
    rw [SobolevSpace.minimalSlope_smul]
    exact (Lp.coeFn_smul |a| (SobolevSpace.minimalSlope μ Q v)).filter_mono hν.ae_le
  have hsame := (SobolevSpace.minimalSlope_eq_on_diff_level μ Q u (a • v) (-M)).filter_mono hν.ae_le
  filter_upwards [hu,hd,hcoeff,hgrad,hsame] with x hu hd hc hg he
  have hv : SobolevSpace.minimalSlope μ Q u x = SobolevSpace.minimalSlope μ Q (a • v) x := by
    apply he
    rw [hc,hu]
    dsimp [a]
    ring
  have ha : |a| = s/2 := by dsimp [a]; rw [abs_neg,abs_of_pos (half_pos hs)]
  rw [ha] at hg
  nlinarith

theorem scaled_contact_gradient_ratio {ν : Measure X} (hν : ν ≪ μ)
    (u v : SobolevSpace μ Q) {s M : ℝ} (hs : 0 < s)
    (hu : ∀ᵐ x ∂ν, SobolevSpace.toLp μ Q u x =
      -(s/2)*SobolevSpace.toLp μ Q v x-M) :
    ∀ᵐ x ∂ν, SobolevSpace.minimalSlope μ Q v x =
      (2/s)*SobolevSpace.minimalSlope μ Q u x := by
  have hd : ∀ᵐ x ∂ν, SobolevSpace.minimalSlope μ Q u x =
      s*(SobolevSpace.minimalSlope μ Q u x/s) := Eventually.of_forall fun x => by
    field_simp
  have hh := scaled_contact_gradient_length μ Q hν u v hs
    (fun x => SobolevSpace.minimalSlope μ Q u x/s) hu hd
  filter_upwards [hh] with x hx
  rw [hx]
  ring

theorem scaled_contact_velocity_pair {ν : Measure X} {C : ℝ≥0∞}
    (hC : C ≠ ∞) (hν : ν ≤ C • μ) (u v g : SobolevSpace μ Q)
    {s M : ℝ} (hs : 0 < s)
    (hu : ∀ᵐ x ∂ν, SobolevSpace.toLp μ Q u x =
      -(s/2)*SobolevSpace.toLp μ Q v x-M) :
    weightedGradientPair μ Q ν u g/s = -(1/2)*(∫ x, localGamma μ Q v g x ∂ν) := by
  let a := -(s/2)
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le_smul hν
  have hcoeff : ∀ᵐ x ∂ν, SobolevSpace.toLp μ Q (a • v) x =
      a*SobolevSpace.toLp μ Q v x := by
    rw [map_smul]
    exact (Lp.coeFn_smul a (SobolevSpace.toLp μ Q v)).filter_mono hac.ae_le
  have hsame := (localGamma_eq_on_diff_level μ Q u (a • v) g (-M)).filter_mono hac.ae_le
  have hscale := (localGamma_smul_left μ Q a v g).filter_mono hac.ae_le
  have he : localGamma μ Q u g =ᵐ[ν] fun x => a*localGamma μ Q v g x := by
    filter_upwards [hu,hcoeff,hsame,hscale] with x hu hc he hs
    rw [←hs]
    apply he
    rw [hu,hc]
    dsimp [a]
    ring
  rw [weightedGradientPair_eq_bracket μ Q hC hν,←integral_localGamma μ Q hC hν,
    integral_congr_ae he,integral_const_mul]
  dsimp [a]
  field_simp

end RegularPointCoordinates

end

end OAI
