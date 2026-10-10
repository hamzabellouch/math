import OAI.Geometry.RCD.Sobolev.GradientQuadraticEnergy
import OAI.Geometry.RCD.Sobolev.SobolevQuadraticEnergy

namespace OAI

/-! # Polarization with the same compact weight on both sides -/

open Set Filter MeasureTheory InnerProductSpace
open scoped BoundedContinuousFunction RealInnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem weighted_integral_localGamma_add_smul_square (μ : Measure X)
    (hQ : QuadraticCheegerEnergy μ) (f g : SobolevSpace μ hQ) (t : ℝ) (A : Set X)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (μ.restrict A))
    {C : ℝ} (hb : ∀ᵐ x ∂μ.restrict A, ‖φ x‖≤C) :
    (∫ x in A, φ x*localGamma μ hQ (f+t • g) (f+t • g) x ∂μ)=
      (∫ x in A, φ x*localGamma μ hQ f f x ∂μ)+
        2*t*(∫ x in A, φ x*localGamma μ hQ f g x ∂μ)+
        t^2*(∫ x in A, φ x*localGamma μ hQ g g x ∂μ) := by
  have hi (a b : SobolevSpace μ hQ) := (localGamma_memL1 μ hQ a b).restrict.bdd_mul hφ hb
  have he : (fun x => φ x*localGamma μ hQ (f+t • g) (f+t • g) x)=ᵐ[μ.restrict A]
      fun x => φ x*localGamma μ hQ f f x+2*t*(φ x*localGamma μ hQ f g x)+
        t^2*(φ x*localGamma μ hQ g g x) := by
    filter_upwards [ae_restrict_of_ae (localGamma_add_smul_square μ hQ f g t)] with x hx
    rw [hx]
    ring
  rw [integral_congr_ae he]
  have hs := integral_add ((hi f f).add ((hi f g).const_mul (2*t))) ((hi g g).const_mul (t^2))
  have hf := integral_add (hi f f) ((hi f g).const_mul (2*t))
  simp only [Pi.add_apply] at hs hf
  rw [hs,hf,integral_const_mul,integral_const_mul]

theorem weighted_gradient_quadratic_energy {n : ℕ} (f g : Euclidean n → ℝ)
    (A : Set (Euclidean n)) (φ : Euclidean n →ᵇ ℝ)
    (hf : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A, DifferentiableAt ℝ f x)
    (hg : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A, DifferentiableAt ℝ g x)
    (hfi : IntegrableOn (fun x => ‖fderiv ℝ f x‖^2) A volume)
    (hgi : IntegrableOn (fun x => ‖fderiv ℝ g x‖^2) A volume) (t : ℝ) :
    (∫ x in A, φ x*‖fderiv ℝ (fun y => f y+t*g y) x‖^2)=
      (∫ x in A, φ x*‖fderiv ℝ f x‖^2)+
      2*t*(∫ x in A, φ x*inner ℝ (gradient f x) (gradient g x))+
      t^2*(∫ x in A, φ x*‖fderiv ℝ g x‖^2) := by
  have hn (u : Euclidean n → ℝ) (x : Euclidean n) : ‖gradient u x‖=‖fderiv ℝ u x‖ :=
    (toDual ℝ (Euclidean n)).symm.norm_map _
  obtain ⟨hcross,_,_⟩ := gradient_quadratic_energy f g A hf hg hfi hgi t
  have hb : ∀ᵐ x ∂(volume : Measure (Euclidean n)).restrict A, ‖φ x‖≤‖φ‖ :=
    Eventually.of_forall φ.norm_coe_le_norm
  have hiF := hfi.bdd_mul φ.continuous.aestronglyMeasurable hb
  have hiG := hgi.bdd_mul φ.continuous.aestronglyMeasurable hb
  have hiC := hcross.bdd_mul φ.continuous.aestronglyMeasurable hb
  have hp : (fun x => φ x*‖fderiv ℝ (fun y => f y+t*g y) x‖^2)=ᵐ[volume.restrict A]
      fun x => φ x*‖fderiv ℝ f x‖^2+2*t*(φ x*inner ℝ (gradient f x) (gradient g x))+
        t^2*(φ x*‖fderiv ℝ g x‖^2) := by
    filter_upwards [hf,hg] with x hfx hgx
    have hd := (hfx.hasFDerivAt.add (hgx.hasFDerivAt.const_smul t)).fderiv
    have hgrad : gradient (fun y => f y+t*g y) x=gradient f x+t • gradient g x := by
      dsimp only [gradient]
      rw [show fderiv ℝ (fun y => f y+t*g y) x=fderiv ℝ f x+t • fderiv ℝ g x from hd,
        map_add,map_smul]
    rw [← hn,hgrad,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,hn,hn]
    ring
  rw [integral_congr_ae hp]
  have hs := integral_add (hiF.add (hiC.const_mul (2*t))) (hiG.const_mul (t^2))
  have hfirst := integral_add hiF (hiC.const_mul (2*t))
  simp only [Pi.add_apply] at hs hfirst
  rw [hs,hfirst,integral_const_mul,integral_const_mul]

end RegularPointCoordinates

end

end OAI
