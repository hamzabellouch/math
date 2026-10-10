import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.AbsGammaLipschitz

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma weakGradient_zero_on_zero {u : X → ℝ} (hu : LocalSobolev m u)
    (hmu : Measurable u) : ∀ᵐ x ∂m, u x = 0 → weakGradient m u x = 0 := by
  have hz : LocalSobolev m (fun _ : X => (0:ℝ)) :=
    ⟨fun _ _ _ => MemLp.zero,_,isMinimalLocalWeakUpperGradient_const 0⟩
  filter_upwards [weakGradient_locality hu hz (hmu (measurableSet_singleton (0:ℝ)))
    (ae_of_all _ fun x hx => hx),weakGradient_const (m := m) 0] with x h1 h2 hx
  exact (h1 hx).trans h2

lemma weakGradient_le_localSlope (hfinite : FiniteOnBoundedSets m)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    ∀ᵐ x ∂m, weakGradient m u x ≤ (localSlope u x).toReal :=
  (weakGradient_isMinimal (localSobolev_of_lipschitz hfinite hu).2).2 _
    (localSlope_isLocalWeakUpperGradient hfinite hu)

lemma fisher_young {a b r : ℝ} (hr : 0 ≤ r) (hz : r = 0 → a = 0) :
    a*b-r*b^2/2 ≤ (a^2/r)/2 := by
  rcases hr.eq_or_lt with hr | hr
  · have ha := hz hr.symm
    simp [hr.symm,ha]
  · have H : 2*a*b-r*b^2 ≤ a^2/r := (le_div_iff₀ hr).mpr (by
      nlinarith [sq_nonneg (a-r*b)])
    linarith

def fisherDensity (u : X → ℝ) (x : X) : ℝ := (weakGradient m u x)^2/u x

lemma weakGradient_le_fisher {u : X → ℝ} (hu : LocalSobolev m u)
    (hmu : Measurable u) (hun : ∀ᵐ x ∂m, 0 ≤ u x) :
    ∀ᵐ x ∂m, weakGradient m u x ≤ (fisherDensity (m := m) u x+u x)/2 := by
  filter_upwards [hun,weakGradient_zero_on_zero hu hmu] with x hx hz
  have H := fisher_young (a := weakGradient m u x) (b := 1) hx hz
  simp only [mul_one,one_pow] at H
  dsimp [fisherDensity]
  linarith

lemma integrable_gradient_of_fisher {u : X → ℝ} (hu : LocalSobolev m u)
    (hmu : Measurable u) (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
    (hI : Integrable (fisherDensity (m := m) u) m) :
    Integrable (weakGradient m u) m := by
  apply ((hI.add hi).div_const 2).mono' (weakGradient_isMinimal hu.2).1.1.aestronglyMeasurable
  filter_upwards [weakGradient_le_fisher hu hmu hun,weakGradient_nonneg (m := m) u] with x hx hn
  simpa only [Real.norm_of_nonneg hn,Pi.add_apply] using hx

lemma gamma_fisher_young (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u φ : X → ℝ} (hu : LocalSobolev m u)
    (hmu : Measurable u) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    ∀ᵐ x ∂m, -gamma m u φ x-u x*(localSlope φ x).toReal^2/2 ≤
      fisherDensity (m := m) u x/2 := by
  filter_upwards [hun,weakGradient_zero_on_zero hu hmu,weakGradient_nonneg (m := m) u,
    abs_gamma_le hfinite hpar hu (localSobolev_of_lipschitz hfinite hφ),
    weakGradient_le_localSlope hfinite hφ] with x hx hz hn hγ hsl
  have H := fisher_young (a := weakGradient m u x) (b := (localSlope φ x).toReal) hx hz
  have hg : -gamma m u φ x ≤ weakGradient m u x*(localSlope φ x).toReal :=
    (neg_le_abs _).trans (hγ.trans (mul_le_mul_of_nonneg_left hsl hn))
  dsimp only [fisherDensity]
  linarith

omit [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma integrable_density_slope_sq (_ : FiniteOnBoundedSets m)
    {u φ : X → ℝ} (hi : Integrable u m) {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    Integrable (fun x => u x*(localSlope φ x).toReal^2) m := by
  apply hi.mul_bdd ((measurable_localSlope hφ.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
    (c := (L:ℝ)^2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ ENNReal.toReal_nonneg L.coe_nonneg |>.mpr
    ((ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hφ x)).trans_eq (ENNReal.coe_toReal L))

lemma IsLaplacian.fisher_pairing (hfinite : FiniteOnBoundedSets m) (o : X)
    (hpar : LocalGradientParallelogram m) {u A φ : X → ℝ} (hu : IsLaplacian m u A)
    (hmu : Measurable u) (hun : ∀ᵐ x ∂m, 0 ≤ u x) (hi : Integrable u m)
    (hI : Integrable (fisherDensity (m := m) u) m) (hA : Integrable A m)
    {L : ℝ≥0} (hφ : LipschitzWith L φ) {B : ℝ} (hB : ∀ x,|φ x| ≤ B) :
    (∫ x,A x*φ x ∂m)-(∫ x,u x*(localSlope φ x).toReal^2 ∂m)/2 ≤
      (∫ x,fisherDensity (m := m) u x ∂m)/2 := by
  have hD := integrable_gradient_of_fisher hu.1.2.1 hmu hun hi hI
  rw [hu.bounded_lipschitz_pairing hfinite hpar o hA hD hφ hB]
  have hγ := integrable_gamma_lipschitz hfinite hpar hu.1.2.1 hD hφ
  have hs := integrable_density_slope_sq hfinite hi hφ
  have hγ' : Integrable (fun x => -gamma m u φ x) m := hγ.neg
  have hs' : Integrable (fun x => u x*(localSlope φ x).toReal^2/2) m := hs.div_const 2
  have H : (∫ x,-gamma m u φ x-u x*(localSlope φ x).toReal^2/2 ∂m) ≤
      (∫ x,fisherDensity (m := m) u x/2 ∂m) :=
    integral_mono_ae (hγ'.sub hs') (hI.div_const 2)
      (gamma_fisher_young hfinite hpar hu.1.2.1 hmu hun hφ)
  rw [integral_sub hγ' hs',integral_neg,integral_div,integral_div] at H
  exact H
end WeakHessian
end
end InlinedFile0

end OAI
