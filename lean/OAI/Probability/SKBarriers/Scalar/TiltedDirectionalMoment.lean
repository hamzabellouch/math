import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianQuadraticIBP

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem HasExpGrowth.pow {E : Type} [NormedAddCommGroup E] {f : E → ℝ}
    (hf : HasExpGrowth f) (k : ℕ) : HasExpGrowth (fun x => f x^k) := by
  induction k with
  | zero => simpa using HasExpGrowth.const (E:=E) (1:ℝ)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem fiberGaussian_tilted_directional_stein (n : ℕ) (V g : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (hc : ContDiff ℝ 1 g)
    (hg : HasExpGrowth g) (hdg : HasExpGrowth (fderiv ℝ g)) (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, coordinateLinear n a z*g z ∂(fiberGaussian n x).tilted V) =
      (∫ z, fderiv ℝ g z (coordinateVector n a) ∂(fiberGaussian n x).tilted V) +
      ∫ z, g z*fderiv ℝ V z (coordinateVector n a) ∂(fiberGaussian n x).tilted V := by
  have hdV : HasExpGrowth (fderiv ℝ V) := by
    obtain ⟨_,C,D,hC,hD,hb,hbb⟩ := hV
    exact HasExpGrowth.of_bounded hC hb
  have hi₁ (i : Fin n) := ((HasExpGrowth.linear (coordinateProjection n i)).mul hg).integrable_tilted_fiberGaussian n V hV
    ((coordinateProjection n i).continuous.mul hc.continuous) x
  have hi₂ (i : Fin n) := (hdg.derivative_eval (coordinateAxis n i)).integrable_tilted_fiberGaussian n V hV
    ((hc.continuous_fderiv (by norm_num)).clm_apply continuous_const) x
  have hi₃ (i : Fin n) := (hg.mul (hdV.derivative_eval (coordinateAxis n i))).integrable_tilted_fiberGaussian n V hV
    (hc.continuous.mul ((hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)) x
  simp only [coordinateLinear_apply,coordinateVector,map_sum,map_smul,smul_eq_mul,
    Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [integral_finsetSum _ (fun i _ => (hi₁ i).const_mul (a i)),
    integral_finsetSum _ (fun i _ => (hi₂ i).const_mul (a i))]
  have he : (fun z : ParameterSpace n => ∑ i, g z*(a i*fderiv ℝ V z (coordinateAxis n i))) =
      fun z => ∑ i, a i*(g z*fderiv ℝ V z (coordinateAxis n i)) := by
    funext z; apply Finset.sum_congr rfl; intro i _; ring
  rw [he,integral_finsetSum _ (fun i _ => (hi₃ i).const_mul (a i)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [integral_const_mul]
  rw [fiberGaussian_tilted_weighted_stein n V g hV hc hg hdg,mul_add]

theorem tilted_linear_moment_recursion (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) (p : ℕ) :
    (∫ z, (coordinateLinear n a z)^(p+2) ∂(fiberGaussian n x).tilted V) =
      (p+1:ℕ)*(∑ i, (a i)^2)*(∫ z, (coordinateLinear n a z)^p ∂(fiberGaussian n x).tilted V)+
      ∫ z, (coordinateLinear n a z)^(p+1)*fderiv ℝ V z (coordinateVector n a)
        ∂(fiberGaussian n x).tilted V := by
  let L := coordinateLinear n a
  have hc : ContDiff ℝ 1 (fun z => L z^(p+1)) := L.contDiff.pow _
  have he : fderiv ℝ (fun z => L z^(p+1))=fun z => ((p+1:ℕ)*L z^p) • L := by
    funext z
    simpa only [Nat.add_sub_cancel,L.fderiv,nsmul_eq_mul] using (L.hasFDerivAt.pow (p+1)).fderiv
  have hg := (HasExpGrowth.linear L).pow p
  have hdg : HasExpGrowth (fderiv ℝ (fun z => L z^(p+1))) := by
    rw [he]
    exact ((HasExpGrowth.const ((p+1:ℕ):ℝ)).mul hg).smul (HasExpGrowth.const L)
  have H := fiberGaussian_tilted_directional_stein n V (fun z => L z^(p+1)) hV hc
    ((HasExpGrowth.linear L).pow _) hdg x a
  simp only [he,smul_apply,smul_eq_mul,L,coordinateLinear_coordinateVector] at H
  rw [show (fun z => (p+1:ℕ)*coordinateLinear n a z^p*(∑ i, a i^2))=
      fun z => ((p+1:ℕ)*(∑ i, a i^2))*coordinateLinear n a z^p by funext z; ring,
    integral_const_mul] at H
  convert H using 1
  congr 1; funext z; ring

theorem tilted_linear_even_moment_step (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B) (p : ℕ) :
    (∫ z, (coordinateLinear n a z)^(2*p+2) ∂(fiberGaussian n x).tilted V) ≤
      (2*(2*p+1:ℕ)*(∑ i, (a i)^2)+B^2)*
        (∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) := by
  let L := coordinateLinear n a
  let μ := (fiberGaussian n x).tilted V
  let d := fun z => fderiv ℝ V z (coordinateVector n a)
  have hi (k : ℕ) : Integrable (fun z => L z^k) μ :=
    ((HasExpGrowth.linear L).pow k).integrable_tilted_fiberGaussian n V hV (L.continuous.pow k) x
  have hd : Continuous d := (hV.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : HasExpGrowth d := HasExpGrowth.of_bounded hB (fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hip : Integrable (fun z => L z^(2*p+1)*d z) μ :=
    (((HasExpGrowth.linear L).pow _).mul hdg).integrable_tilted_fiberGaussian n V hV
      ((L.continuous.pow _).mul hd) x
  have hb' (z) : 2*(L z^(2*p+1)*d z) ≤ L z^(2*p+2)+B^2*L z^(2*p) := by
    have hz : 0 ≤ L z^(2*p) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) _
    have hdz : d z^2 ≤ B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (d z)) hB).mpr (hb z)
    have H := mul_nonneg hz (sq_nonneg (L z-d z))
    have H' := mul_le_mul_of_nonneg_right hdz hz
    simp only [pow_succ] at ⊢
    nlinarith
  have H := integral_mono (hip.const_mul 2) ((hi _).add ((hi _).const_mul (B^2))) hb'
  simp only [Pi.add_apply] at H
  rw [integral_const_mul,integral_add (hi _) ((hi _).const_mul (B^2)),integral_const_mul] at H
  have HE := tilted_linear_moment_recursion n V hV x a (2*p)
  change (∫ z, L z^(2*p+2) ∂μ)=(2*p+1:ℕ)*(∑ i, a i^2)*(∫ z, L z^(2*p) ∂μ)+
    ∫ z, L z^(2*p+1)*d z ∂μ at HE
  nlinarith

end SK.Analytic

end
end

end OAI
