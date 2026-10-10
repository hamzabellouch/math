import OAI.Geometry.Riemannian.HarmonicCore.EnergyStability
import OAI.Geometry.Riemannian.HarmonicCore.SobolevSix
import OAI.Geometry.Riemannian.HarmonicCore.VolumeRatio
import OAI.Geometry.Riemannian.HarmonicCore.TransferOperator
import OAI.Geometry.Riemannian.HarmonicCore.WarpingBounds
import OAI.Geometry.Riemannian.HarmonicCore.Frequency

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace
open scoped BigOperators

namespace HarmonicCounterexample
open Main

def roundAngular : Main.AngularTensor where
  coeff := fun _ _ ↦ 1
  smooth := by intros; exact contDiffAt_const
  positive := fun _ _ _ ↦ Matrix.PosDef.one
  radial := by intros; simp
  homogeneous := by intros; rfl
  det_one := by intros; simp
  round := by intros; rfl

lemma roundAngular_bounds : Main.AngularBounds roundAngular 1 1 := by
  intro t x hx v
  simp [roundAngular, Main.dotProduct_self_norm]

theorem scalar_polar_realization (H : Main.AngularTensor) {c B : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hB : 1 ≤ B) (hH : Main.AngularBounds H c B)
    (C : ℝ) (hC : 0 < C) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∃ g : Main.SmoothMetric3,
      g.coeff = Main.polarCoeff (warping C J) H ∧
      g.Complete ∧ g.EuclideanNearOrigin ∧ g.HasAVR ((24/25 : ℝ)^2) ∧
      ∀ x : Main.E3, g.distance 0 x = ‖x‖ := by
  obtain ⟨J₀, hJ₀⟩ := scalar_warping_realization C hC
  refine ⟨J₀, ?_⟩
  intro J hJ
  obtain ⟨h4, hm, hs, hcore, _⟩ := hJ₀ J hJ
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have ha : 0 < a := by norm_num [a]
  have ha1 : a ≤ 1 := by norm_num [a]
  have hb : ∀ r : ℝ, 0 ≤ r → a * r ≤ warping C J r ∧ warping C J r ≤ r :=
    fun r hr ↦ warping_bounds hJpos hC.le hm.le hr
  refine ⟨Main.polarMetric ha (warping C J) H hs hcore hb, rfl,
    Main.polarMetric_complete ha ha1 hc hc1 hB _ H hs hcore hb hH,
    Main.polarMetric_euclidean ha _ H hs hcore hb, ?_,
    Main.polarMetric_distance_origin ha _ H hs hcore hb⟩
  simpa only [a] using Main.polarMetric_hasAVR ha ha1 (warping C J) H hs hcore hb
    (warping_ratio_tendsto hJpos hC.le hm.le)

theorem exists_complete_euclidean_core_AVR :
    ∃ g : Main.SmoothMetric3, g.Complete ∧ g.EuclideanNearOrigin ∧
      g.HasAVR ((24/25 : ℝ)^2) ∧ ∀ x : Main.E3, g.distance 0 x = ‖x‖ := by
  obtain ⟨J₀, hJ₀⟩ := scalar_polar_realization roundAngular
    (c := 1) (B := 1) (by norm_num) le_rfl le_rfl roundAngular_bounds 1 (by norm_num)
  obtain ⟨g, _, hg⟩ := hJ₀ J₀ le_rfl
  exact ⟨g, hg⟩

end HarmonicCounterexample

end

end OAI
