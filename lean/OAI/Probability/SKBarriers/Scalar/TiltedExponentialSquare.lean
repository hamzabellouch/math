import Mathlib
import OAI.Probability.SKBarriers.Scalar.TiltedDirectionalMoment

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem tilted_linear_even_moment_bound (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B) (p : ℕ) :
    (∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) ≤
      (p.factorial:ℝ)*(4*(∑ i, (a i)^2)+B^2)^p := by
  let σ := ∑ i, (a i)^2
  have hσ : 0 ≤ σ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ 4*σ+B^2 := by positivity
  let := fiberGaussian_tilted_probability n V hV x
  induction p with
  | zero => simp
  | succ p ih =>
    have H := tilted_linear_even_moment_step n V hV x a hB hb p
    have hm : 0 ≤ 2*(2*p+1:ℕ)*σ+B^2 := by positivity
    have hp : 0 ≤ (p:ℝ) := Nat.cast_nonneg p
    have hcoef : 2*(2*p+1:ℕ)*σ+B^2 ≤ (p+1:ℕ)*(4*σ+B^2) := by
      push_cast
      nlinarith [mul_nonneg hp (sq_nonneg B)]
    calc
      _ ≤ (2*(2*p+1:ℕ)*σ+B^2)*(∫ z, (coordinateLinear n a z)^(2*p) ∂(fiberGaussian n x).tilted V) := by
        simpa only [Nat.mul_add,Nat.mul_one] using H
      _ ≤ (2*(2*p+1:ℕ)*σ+B^2)*((p.factorial:ℝ)*(4*σ+B^2)^p) := mul_le_mul_of_nonneg_left ih hm
      _ ≤ (p+1:ℕ)*(4*σ+B^2)*((p.factorial:ℝ)*(4*σ+B^2)^p) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]; ring

theorem tilted_linear_exp_square_bound (n : ℕ) (V : ParameterSpace n → ℝ)
    (hV : BoundedDerivs V) (x : ℝ) (a : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z, |fderiv ℝ V z (coordinateVector n a)| ≤ B)
    {c : ℝ} (hc : 0 ≤ c) (hsmall : c*(4*(∑ i, (a i)^2)+B^2) ≤ 1/2) :
    Integrable (fun z => Real.exp (c*(coordinateLinear n a z)^2)) ((fiberGaussian n x).tilted V) ∧
    (∫ z, Real.exp (c*(coordinateLinear n a z)^2) ∂(fiberGaussian n x).tilted V) ≤ 2 := by
  let L := coordinateLinear n a
  let μ := (fiberGaussian n x).tilted V
  let C := 4*(∑ i, (a i)^2)+B^2
  let F (p : ℕ) := fun z => (c^p/(p.factorial:ℝ))*L z^(2*p)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hi (p) : Integrable (F p) μ :=
    (((HasExpGrowth.linear L).pow _).integrable_tilted_fiberGaussian n V hV (L.continuous.pow _) x).const_mul _
  have hFp (p) (z) : 0 ≤ F p z := by
    dsimp only [F]
    apply mul_nonneg (by positivity)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hnorm (p) : (∫ z, ‖F p z‖ ∂μ)=(∫ z, F p z ∂μ) := by
    apply integral_congr_ae; filter_upwards [] with z; exact Real.norm_of_nonneg (hFp p z)
  have hbound (p) : (∫ z, F p z ∂μ) ≤ (1/2:ℝ)^p := by
    rw [show F p=fun z => (c^p/(p.factorial:ℝ))*L z^(2*p) from rfl,integral_const_mul]
    have H := tilted_linear_even_moment_bound n V hV x a hB hb p
    calc
      _ ≤ (c^p/(p.factorial:ℝ))*((p.factorial:ℝ)*C^p) := mul_le_mul_of_nonneg_left H (by positivity)
      _ = (c*C)^p := by rw [mul_pow]; field_simp
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hc hC) hsmall p
  have hsgeom : Summable (fun p : ℕ => (1/2:ℝ)^p) := summable_geometric_of_abs_lt_one (by norm_num)
  have hs : Summable (fun p => ∫ z, F p z ∂μ) :=
    Summable.of_nonneg_of_le (fun p => integral_nonneg (hFp p)) hbound hsgeom
  have hsN : Summable (fun p => ∫ z, ‖F p z‖ ∂μ) := by simpa only [hnorm] using hs
  have he (z) : (∑' p, F p z)=Real.exp (c*L z^2) := by
    rw [Real.exp_eq_exp_ℝ]
    convert (NormedSpace.expSeries_div_hasSum_exp (c*L z^2)).tsum_eq using 1
    apply tsum_congr
    intro p
    dsimp only [F]
    rw [mul_pow,pow_mul]
    ring
  have HE := integral_tsum_of_summable_integral_norm hi hsN
  simp_rw [he] at HE
  have h1 : 1 ≤ (∫ z, Real.exp (c*L z^2) ∂μ) := by
    rw [← HE]
    have H := hs.le_tsum 0 (fun p _ => integral_nonneg (hFp p))
    have hzero : (∫ z, F 0 z ∂μ)=1 := by
      let := fiberGaussian_tilted_probability n V hV x
      simp [F,μ]
    rwa [hzero] at H
  refine ⟨?_,?_⟩
  · by_contra hn
    rw [integral_undef hn] at h1
    norm_num at h1
  · change (∫ z, Real.exp (c*L z^2) ∂μ) ≤ 2
    rw [← HE]
    calc
      _ ≤ ∑' p : ℕ, (1/2:ℝ)^p := hs.tsum_le_tsum hbound hsgeom
      _ = 2 := by rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)]; norm_num

end SK.Analytic

end
end

end OAI
