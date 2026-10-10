import OAI.Geometry.RCD.Heat.WeightedSourceSquare
import OAI.Geometry.RCD.Coordinates.RegularizedFisherInterpolation

namespace OAI

/-! # The mass and first moment of the logarithmic source

All weights and sources are the actual L² representatives. Their algebraic
relations give integrability before the weighted square estimate is used.
-/

open MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem shifted_product_mass (u w R : Lp ℝ 2 μ) (ε : ℝ) (hw : Integrable w μ)
    (hR : R =ᵐ[μ] fun x => (ε+u x)*w x) :
    Integrable R μ ∧ (∫ x, R x ∂μ)=ε*(∫ x, w x ∂μ)+inner ℝ u w := by
  have hprod := (Lp.memLp u).integrable_mul (Lp.memLp w)
  have he : (fun x => ε*w x+u x*w x) =ᵐ[μ] R := by
    filter_upwards [hR] with x hx
    rw [hx]
    ring
  refine ⟨((hw.const_mul ε).add hprod).congr he,?_⟩
  have hadd := integral_add (hw.const_mul ε) hprod
  simp only [Pi.mul_apply] at hadd
  rw [←integral_congr_ae he,hadd,integral_const_mul,L2.inner_def]
  simp only [Real.inner_apply]

theorem fisher_source_moment (u w d S R : Lp ℝ 2 μ) (g : X → ℝ)
    {ε : ℝ} (hε : 0<ε) (hu : ∀ᵐ x ∂μ, 0≤u x)
    (hR : R =ᵐ[μ] fun x => (ε+u x)*w x)
    (hS : S =ᵐ[μ] fun x => d x/(ε+u x)-g x/(ε+u x)^2) :
    Integrable (fun x => w x*g x/(ε+u x)) μ ∧
      (∫ x, R x*S x ∂μ)=inner ℝ w d-(∫ x, w x*g x/(ε+u x) ∂μ) := by
  have hrs := (Lp.memLp R).integrable_mul (Lp.memLp S)
  have hwd := (Lp.memLp w).integrable_mul (Lp.memLp d)
  have he : (fun x => w x*d x-R x*S x) =ᵐ[μ] fun x => w x*g x/(ε+u x) := by
    filter_upwards [hu,hR,hS] with x hx hr hs
    rw [hr,hs]
    have hz : ε+u x≠0 := (add_pos_of_pos_of_nonneg hε hx).ne'
    field_simp [hz]
    ring
  refine ⟨(hwd.sub hrs).congr he,?_⟩
  have hsub := integral_sub hwd hrs
  simp only [Pi.mul_apply] at hsub
  rw [←integral_congr_ae he,hsub,L2.inner_def]
  simp only [Real.inner_apply]
  ring

theorem fisher_source_moment_square (u w d S R : Lp ℝ 2 μ) (g : X → ℝ)
    {ε : ℝ} (hε : 0<ε) (hu : ∀ᵐ x ∂μ, 0≤u x) (hw : Integrable w μ)
    (hR0 : ∀ᵐ x ∂μ, 0≤R x) (B : ℝ≥0) (hRb : ∀ᵐ x ∂μ, |R x|≤B)
    (hR : R =ᵐ[μ] fun x => (ε+u x)*w x)
    (hS : S =ᵐ[μ] fun x => d x/(ε+u x)-g x/(ε+u x)^2) :
    (inner ℝ w d-(∫ x, w x*g x/(ε+u x) ∂μ))^2 ≤
      (ε*(∫ x, w x ∂μ)+inner ℝ u w)*(∫ x, R x*(S x)^2 ∂μ) := by
  have hm := shifted_product_mass μ u w R ε hw hR
  have hs := fisher_source_moment μ u w d S R g hε hu hR hS
  have hi := (Lp.memLp S).integrable_sq.bdd_mul (Lp.aestronglyMeasurable R)
    (by simpa only [Real.norm_eq_abs] using hRb)
  have hh := weighted_source_square μ hm.1 hR0 (Lp.aestronglyMeasurable S).aemeasurable hi
  simpa only [hs.2,hm.2] using hh.2

end RegularPointCoordinates

end

end OAI
