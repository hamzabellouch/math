import Mathlib.Analysis.SpecificLimits.Basic
import OAI.Geometry.NodalSets.Charts.SphereFiniteNormIntrinsicCompactness
import OAI.Geometry.NodalSets.Charts.SphereNormalizedSimpleUniqueness

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Filter Metric Yau.Geometry
open scoped ContDiff Topology
noncomputable section

theorem sphere_finite_norm_simple_uniform_persistence (d : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density) (N : ℕ)
    (u : Base → ℝ) (hun : sphereWeightedPairing d.density u u=1)
    (hsimple : ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
        sphereIndexedEigenvalue d N*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ y ∈ ball (0 : Yau.Jets.Coord) (1/512), sphereChartCoordMap p y=x) ∧
      ∀ eps > 0, ∃ eta > 0, ∀ b : SphereEnergyData,
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
        sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
        ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
          sphereWeightedPairing b.density v v=1 →
          (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
            sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) →
          (∀ x, |v x-u x| < eps) ∨ (∀ x, |v x+u x| < eps) := by
  classical
  obtain ⟨P,hP,eta₀,heta₀,H⟩ := sphere_finite_norm_indexed_intrinsic_compactness d hd N
  refine ⟨P,hP,?_⟩
  intro eps heps
  let Good (v : Base → ℝ) : Prop := (∀ x, |v x-u x| < eps) ∨ (∀ x, |v x+u x| < eps)
  change ∃ eta > 0, ∀ b : SphereEnergyData,
    ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density →
    sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
    ∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
      sphereWeightedPairing b.density v v=1 →
      (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
        sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) → Good v
  by_contra hbad
  push Not at hbad
  choose b hb hdist v hv hn he hbad using
    (fun j : ℕ ↦ hbad (min eta₀ (1/((j:ℝ)+1))) (lt_min heta₀ (by positivity)))
  have hcoeff : Tendsto (fun j ↦ sphereCoefficientDistance P 8 d.tensor d.density
      (b j).tensor (b j).density) atTop (𝓝 0) := by
    apply squeeze_zero _ _ tendsto_one_div_add_atTop_nhds_zero_nat
    · intro j
      exact sphereCoefficientDistance_nonneg P 8 d.tensor (b j).tensor d.density (b j).density
        (fun p _ ↦ intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
        (fun p _ ↦ intrinsic_coefficient_chart_smooth (b j).tensor (b j).smooth (b j).symm (b j).pos
          (b j).density (hb j) p)
    · intro j
      exact (hdist j).le.trans (min_le_right _ _)
  obtain ⟨v₀,hv₀,hn₀,_,he₀,nu,hnu,ht,_⟩ := H b hb
    (fun j ↦ (hdist j).trans_le (min_le_left _ _)) hcoeff v hv hn he
  have hsigned := sphere_normalized_simple_eigenfunction_signed d u hun (sphereIndexedEigenvalue d N)
    hsimple v₀ hv₀ hn₀ he₀
  have hc := (Metric.tendstoUniformly_iff.mp ht) eps heps
  obtain ⟨j,hj⟩ := hc.exists
  apply hbad (nu j)
  rcases hsigned with rfl | rfl
  · left
    intro x
    simpa only [Real.dist_eq,abs_sub_comm] using hj x
  · right
    intro x
    simpa only [Pi.neg_apply,Real.dist_eq,abs_sub_comm,sub_neg_eq_add] using hj x

end
end Yau.Target

end OAI
