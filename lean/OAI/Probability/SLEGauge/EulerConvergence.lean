import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StoppedEstimates

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
namespace SLEExactGauge
namespace Parameter
theorem weighted_young_pair (P : Parameter) {C ε t X Y Z : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (ht : 0 < t)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    C * t ^ (-1 - P.η) * X ^ P.η * Y ^ P.η * Z ^ (1 - 2 * P.η) ≤
      ε * (X + Y) + P.youngConstant C ε * t ^ (-P.M) * Z := by
  let r := 1 - 2 * P.η
  have hr : 0 < r := by dsimp [r]; linarith [P.η_lt_half]
  have hη := P.η_pos
  have hηε : 0 < P.η / ε := div_pos hη hε
  have hεη : 0 < ε / P.η := div_pos hε hη
  let B := C ^ (1 / r) * (P.η / ε) ^ (2 * P.η / r) * t ^ (-P.M)
  have hB : 0 < B := by dsimp [B]; positivity
  have heM : (-P.M) * r = -1 - P.η := by
    have hM : P.M * r = 1 + P.η := by
      dsimp [M, r]
      exact div_mul_cancel₀ _ (by linarith [P.η_lt_half])
    nlinarith
  have hBr : B ^ r = C * (P.η / ε) ^ (2 * P.η) * t ^ (-1 - P.η) := by
    dsimp only [B]
    rw [Real.mul_rpow (by positivity : 0 ≤ C ^ (1 / r) *
        (P.η / ε) ^ (2 * P.η / r)) (by positivity),
      Real.mul_rpow (by positivity : 0 ≤ C ^ (1 / r)) (by positivity),
      ← Real.rpow_mul hC.le, ← Real.rpow_mul hηε.le,
      ← Real.rpow_mul ht.le, heM]
    rw [div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne', Real.rpow_one]
  have hinv : (ε / P.η) ^ P.η * (ε / P.η) ^ P.η *
      (P.η / ε) ^ (2 * P.η) = 1 := by
    rw [← Real.rpow_add hεη, show P.η + P.η = 2 * P.η by ring,
      ← Real.mul_rpow hεη.le hηε.le]
    have hprod : ε / P.η * (P.η / ε) = 1 := by field_simp
    rw [hprod, Real.one_rpow]
  have hamgm := Real.geom_mean_le_arith_mean3_weighted hη.le hη.le hr.le
    (mul_nonneg hεη.le hX) (mul_nonneg hεη.le hY) (mul_nonneg hB.le hZ)
    (show P.η + P.η + r = 1 by dsimp [r]; ring)
  have hleft : (ε / P.η * X) ^ P.η * (ε / P.η * Y) ^ P.η * (B * Z) ^ r =
      C * t ^ (-1 - P.η) * X ^ P.η * Y ^ P.η * Z ^ r := by
    rw [Real.mul_rpow hεη.le hX, Real.mul_rpow hεη.le hY,
      Real.mul_rpow hB.le hZ, hBr]
    calc
      _ = ((ε / P.η) ^ P.η * (ε / P.η) ^ P.η * (P.η / ε) ^ (2 * P.η)) *
        (C * t ^ (-1 - P.η) * X ^ P.η * Y ^ P.η * Z ^ r) := by ring
      _ = _ := by rw [hinv, one_mul]
  have hright : P.η * (ε / P.η * X) + P.η * (ε / P.η * Y) + r * (B * Z) =
      ε * (X + Y) + P.youngConstant C ε * t ^ (-P.M) * Z := by
    dsimp only [B, youngConstant]
    change P.η * (ε / P.η * X) + P.η * (ε / P.η * Y) +
      r * (C ^ (1 / r) * (P.η / ε) ^ (2 * P.η / r) * t ^ (-P.M) * Z) =
      ε * (X + Y) + r * C ^ (1 / r) * (P.η / ε) ^ (2 * P.η / r) * t ^ (-P.M) * Z
    field_simp
  rw [hleft, hright] at hamgm
  exact hamgm

end Parameter
end SLEExactGauge

open Filter Topology

namespace SLEExactGauge.Parameter

lemma hasDerivAt_factor_first (P : Parameter) {δ θ : ℝ} (hs : 0 < Real.sin θ) :
    HasDerivAt (fun t : ℝ => P.angularDerivative δ (Real.sin t) (Real.cos t))
      (P.p*(P.p-1)*Real.cos θ^2*Real.sin θ^(P.p-2)-P.p*Real.sin θ^P.p+
       δ*(P.q*(P.q-1)*Real.cos θ^2*Real.sin θ^(P.q-2)-P.q*Real.sin θ^P.q)) θ := by
  convert! (hasDerivAt_sinePower_first P.p θ hs).add
    ((hasDerivAt_sinePower_first P.q θ hs).const_mul δ) using 1
  ext t
  unfold angularDerivative
  simp only [Pi.add_apply]
  ring

lemma deriv_factor (P : Parameter) {δ θ : ℝ} (hs : 0 < Real.sin θ) :
    deriv (fun t : ℝ => P.f δ (Real.sin t)) θ =
      P.angularDerivative δ (Real.sin θ) (Real.cos θ) :=
  (P.hasDerivAt_factor hs).deriv

lemma factor_deriv_differentiable (P : Parameter) {δ θ : ℝ} (hs : 0 < Real.sin θ) :
    HasDerivAt (deriv (fun t : ℝ => P.f δ (Real.sin t)))
      (P.p*(P.p-1)*Real.cos θ^2*Real.sin θ^(P.p-2)-P.p*Real.sin θ^P.p+
       δ*(P.q*(P.q-1)*Real.cos θ^2*Real.sin θ^(P.q-2)-P.q*Real.sin θ^P.q)) θ := by
  have he : deriv (fun t : ℝ => P.f δ (Real.sin t)) =ᶠ[nhds θ]
      (fun t : ℝ => P.angularDerivative δ (Real.sin t) (Real.cos t)) := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds hs)] with t ht
    exact P.deriv_factor ht
  exact (P.hasDerivAt_factor_first hs).congr_of_eventuallyEq he

lemma angleGenerator_factor (P : Parameter) {δ θ : ℝ} (hs : 0 < Real.sin θ) :
    P.angleGenerator (fun t : ℝ => P.f δ (Real.sin t)) θ =
      P.angleGenerator (fun t : ℝ => Real.sin t^P.p) θ+
      δ*P.angleGenerator (fun t : ℝ => Real.sin t^P.q) θ := by
  unfold angleGenerator
  rw [(P.factor_deriv_differentiable hs).deriv,P.deriv_factor hs,
    secondDeriv_sinePower P.p θ hs,secondDeriv_sinePower P.q θ hs,
    deriv_sinePower P.p θ hs,deriv_sinePower P.q θ hs]
  unfold angularDerivative
  ring

 

lemma shifted_sine_generator (P : Parameter) (r θ : ℝ) (hs : 0 < Real.sin θ) :
    P.angleGenerator (fun t : ℝ => Real.sin t^r) θ+P.p/2*Real.sin θ^r =
      (P.p-r)*(r+1)/2*Real.sin θ^r-r*(P.p-r)/2*Real.sin θ^(r-2) := by
  have hp1 : Real.sin θ^(r-1) = Real.sin θ^r/Real.sin θ := by
    rw [Real.rpow_sub hs,Real.rpow_one]
  have hp2 : Real.sin θ^(r-2) = Real.sin θ^r/Real.sin θ^2 := by
    rw [Real.rpow_sub hs,Real.rpow_two]
  have hcos : Real.cos θ^2 = 1-Real.sin θ^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  unfold angleGenerator
  rw [secondDeriv_sinePower r θ hs,deriv_sinePower r θ hs,hp1,hp2]
  unfold p
  field_simp
  rw [hcos]
  ring

 

theorem exact_factor_drift (P : Parameter) {δ θ : ℝ} (_hδ : 0 < δ)
    (hs : 0 < Real.sin θ) (σ : ℝ) :
    (P.angleGenerator (fun t : ℝ => P.f δ (Real.sin t)) θ+
      P.p/2*P.f δ (Real.sin θ)+σ*δ*(1+Real.sin θ^P.q))/P.f δ (Real.sin θ) =
      P.drift δ (Real.sin θ) σ := by
  rw [P.angleGenerator_factor hs]
  have hp := P.shifted_sine_generator P.p θ hs
  have hq := P.shifted_sine_generator P.q θ hs
  simp only [sub_self,zero_mul,mul_zero,zero_div] at hp
  unfold drift f k at *
  linear_combination (norm := ring_nf) hp / (Real.sin θ ^ P.p+δ*(1+Real.sin θ^P.q)) +
    δ / (Real.sin θ ^ P.p+δ*(1+Real.sin θ^P.q)) * hq

end SLEExactGauge.Parameter

 

noncomputable section
open Complex Real Set Filter
open scoped Topology
namespace SLEExactGauge.AngleCalculus

 
def angleD (z : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.imCLM.comp (z⁻¹ • (1 : ℂ →L[ℝ] ℂ))

lemma hasFDerivAt_arg {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasFDerivAt Complex.arg (angleD z) z := by
  simpa only [angleD,Function.comp_def,Complex.imCLM_apply,Complex.log_im] using
    Complex.imCLM.hasFDerivAt.comp z (Complex.hasStrictFDerivAt_log_real hz).hasFDerivAt

lemma angleD_apply (z w : ℂ) : angleD z w = (w/z).im := by
  simp [angleD,div_eq_mul_inv,mul_comm]

 
def V (z : ℂ) : ℝ := z.im / Complex.normSq z

lemma driver_angle {z : ℂ} (hy : 0 < z.im) (b : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.arg (z-u)) (V (z-b)) b := by
  have hz : z-(b:ℂ) ∈ Complex.slitPlane := Or.inr (by simpa using ne_of_gt hy)
  have hd := (hasFDerivAt_arg hz).comp_hasDerivAt b
    ((hasDerivAt_const b z).sub Complex.ofRealCLM.hasDerivAt)
  convert! hd using 1
  rw [angleD_apply]
  simp [V,Complex.div_im,Complex.normSq_apply]
  ring

lemma hasDerivAt_driver_V (z : ℂ) (b : ℝ) (hy : 0 < z.im) :
    HasDerivAt (fun u : ℝ => V (z-u))
      (2*(z-b).re*(z-b).im/(Complex.normSq (z-b))^2) b := by
  have hz : z-(b:ℂ) ≠ 0 := by
    intro hh
    have he := congrArg Complex.im hh
    simp at he
    linarith
  have hn : Complex.normSq (z-(b:ℂ)) ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  have hd : HasDerivAt (fun u : ℝ => (z.re-u)^2+z.im^2) (-2*(z.re-b)) b := by
    convert! (((hasDerivAt_const b z.re).sub (hasDerivAt_id b)).pow 2).add_const (z.im^2) using 1
    simp only [Pi.sub_apply,id_eq]
    ring
  have he := (hasDerivAt_const b z.im).div hd (by simpa [Complex.normSq_apply,pow_two] using hn)
  convert! he using 1
  · ext u
    simp [V,Complex.normSq_apply,pow_two]
  · simp [Complex.normSq_apply]
    ring

lemma deriv_driver_angle {z : ℂ} (hy : 0 < z.im) :
    deriv (fun u : ℝ => Complex.arg (z-u)) = fun u : ℝ => V (z-u) := by
  funext u
  exact (driver_angle hy u).deriv

lemma secondDeriv_driver_angle {z : ℂ} (hy : 0 < z.im) (b : ℝ) :
    deriv (deriv (fun u : ℝ => Complex.arg (z-u))) b =
      2*(z-b).re*(z-b).im/(Complex.normSq (z-b))^2 := by
  rw [deriv_driver_angle hy]
  exact (hasDerivAt_driver_V z b hy).deriv

lemma loewner_angle {g : ℝ → ℂ} {a b t : ℝ}
    (hg : HasDerivAt g ((a:ℂ)/(g t-b)) t) (hy : 0 < (g t).im) :
    HasDerivAt (fun u => Complex.arg (g u-b))
      (-2*a*(g t-b).re*(g t-b).im/(Complex.normSq (g t-b))^2) t := by
  have hz : g t-(b:ℂ) ∈ Complex.slitPlane := Or.inr (by simpa using ne_of_gt hy)
  convert! (hasFDerivAt_arg hz).comp_hasDerivAt t (hg.sub_const (b:ℂ)) using 1
  rw [angleD_apply]
  simp [Complex.div_im,Complex.div_re]
  ring

 

lemma angle_generator_coefficients (a : ℝ) {z : ℂ} (hy : 0 < z.im) :
    (-2*a*z.re*z.im/(Complex.normSq z)^2)+
      (2*z.re*z.im/(Complex.normSq z)^2)/2 =
      (1-2*a)*(Real.cos z.arg/Real.sin z.arg)*(V z)^2 := by
  have hz : z ≠ 0 := by intro h; simp [h] at hy
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hN : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz).ne'
  rw [Complex.sin_arg,Complex.cos_arg hz,V]
  field_simp
  ring

end SLEExactGauge.AngleCalculus

namespace SLEExactGauge.AngleCalculus

lemma sin_angle_pos {z : ℂ} (hy : 0 < z.im) : 0 < Real.sin z.arg := by
  rw [Complex.sin_arg]
  apply div_pos hy
  apply norm_pos_iff.mpr
  intro h
  simp [h] at hy

 

def physicalGenerator (a : ℝ) (φ : ℝ → ℝ) (z : ℂ) (b : ℝ) : ℝ :=
  fderiv ℝ (fun w : ℂ => φ (Complex.arg (w-b))) z ((a:ℂ)/(z-b))+
    deriv (deriv (fun c : ℝ => φ (Complex.arg (z-c)))) b/2

lemma driver_comp_first (φ : ℝ → ℝ)
    (hφ : ∀ θ, 0 < Real.sin θ → HasDerivAt φ (deriv φ θ) θ)
    {z : ℂ} (hy : 0 < z.im) (b : ℝ) :
    HasDerivAt (fun c : ℝ => φ (Complex.arg (z-c)))
      (deriv φ (Complex.arg (z-b))*V (z-b)) b :=
  (hφ _ (sin_angle_pos (by simpa using hy))).comp b (driver_angle hy b)

lemma driver_comp_second (φ : ℝ → ℝ)
    (hφ : ∀ θ, 0 < Real.sin θ → HasDerivAt φ (deriv φ θ) θ)
    (hφ' : ∀ θ, 0 < Real.sin θ → HasDerivAt (deriv φ) (deriv (deriv φ) θ) θ)
    {z : ℂ} (hy : 0 < z.im) (b : ℝ) :
    deriv (deriv (fun c : ℝ => φ (Complex.arg (z-c)))) b =
      deriv (deriv φ) (Complex.arg (z-b))*(V (z-b))^2+
      deriv φ (Complex.arg (z-b))*(2*(z-b).re*(z-b).im/(Complex.normSq (z-b))^2) := by
  have he : deriv (fun c : ℝ => φ (Complex.arg (z-c))) =
      fun c : ℝ => deriv φ (Complex.arg (z-c))*V (z-c) := by
    funext c
    exact (driver_comp_first φ hφ hy c).deriv
  rw [he]
  have hd := ((hφ' _ (sin_angle_pos (by simpa using hy))).comp b
    (driver_angle hy b)).mul (hasDerivAt_driver_V z b hy)
  convert! hd.deriv using 1
  simp only [Function.comp_def]
  ring

lemma physical_generator_angle (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ θ, 0 < Real.sin θ → HasDerivAt φ (deriv φ θ) θ)
    (hφ' : ∀ θ, 0 < Real.sin θ → HasDerivAt (deriv φ) (deriv (deriv φ) θ) θ)
    {z : ℂ} (hy : 0 < z.im) (b : ℝ) :
    physicalGenerator a φ z b = (V (z-b))^2 *
      (deriv (deriv φ) (z-b).arg/2+(1-2*a)*
        (Real.cos (z-b).arg/Real.sin (z-b).arg)*deriv φ (z-b).arg) := by
  have hy' : 0 < (z-(b:ℂ)).im := by simpa using hy
  have hz : z-(b:ℂ) ∈ Complex.slitPlane := Or.inr hy'.ne'
  have hd := (hφ _ (sin_angle_pos hy')).hasFDerivAt.comp z
    ((hasFDerivAt_arg hz).comp z ((hasFDerivAt_id z).sub_const (b:ℂ)))
  have hv : angleD (z-b) ((a:ℂ)/(z-b)) =
      -2*a*(z-b).re*(z-b).im/(Complex.normSq (z-b))^2 := by
    rw [angleD_apply]
    simp [Complex.div_im,Complex.div_re]
    ring
  simp only [Function.comp_def,id_eq] at hd
  unfold physicalGenerator
  rw [hd.fderiv,driver_comp_second φ hφ hφ' hy b]
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  rw [hv]
  have hc := angle_generator_coefficients a hy'
  linear_combination deriv φ (z-b).arg * hc

end SLEExactGauge.AngleCalculus

noncomputable section
open scoped Topology
namespace SLEExactGauge.Calculus

lemma fderiv_separable (e δ : ℝ → ℝ) (φ ψ : ℂ → ℝ) (u : ℝ) (z : ℂ)
    (e' δ' : ℝ) (Dφ Dψ : ℂ →L[ℝ] ℝ)
    (he : HasDerivAt e e' u) (hδ : HasDerivAt δ δ' u)
    (hφ : HasFDerivAt φ Dφ z) (hψ : HasFDerivAt ψ Dψ z) (v : ℝ) (w : ℂ) :
    fderiv ℝ (fun x : ℝ × ℂ => e x.1*(φ x.2+δ x.1*ψ x.2)) (u,z) (v,w) =
      e'*v*(φ z+δ u*ψ z)+e u*(Dφ w+δ'*v*ψ z+δ u*Dψ w) := by
  have hfst : HasFDerivAt (fun x : ℝ × ℂ => x.1) (ContinuousLinearMap.fst ℝ ℝ ℂ) (u,z) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun x : ℝ × ℂ => x.2) (ContinuousLinearMap.snd ℝ ℝ ℂ) (u,z) := hasFDerivAt_snd
  have heF := he.hasFDerivAt.comp (u,z) hfst
  have hδF := hδ.hasFDerivAt.comp (u,z) hfst
  have hφF := hφ.comp (u,z) hsnd
  have hψF := hψ.comp (u,z) hsnd
  have hd := heF.mul (hφF.add (hδF.mul hψF))
  simp only [Function.comp_def,Pi.mul_apply,Pi.add_apply] at hd
  change HasFDerivAt (fun x : ℝ × ℂ => e x.1*(φ x.2+δ x.1*ψ x.2)) _ (u,z) at hd
  rw [hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  change e u * (Dφ w + (δ u * Dψ w + ψ z * (v * δ'))) + (φ z + δ u * ψ z) * (v * e') = _
  ring

lemma secondDeriv_linear (C δ : ℝ) (φ ψ : ℝ → ℝ)
    (hφ : ∀ x, DifferentiableAt ℝ φ x) (hψ : ∀ x, DifferentiableAt ℝ ψ x)
    (hφ' : ∀ x, DifferentiableAt ℝ (deriv φ) x)
    (hψ' : ∀ x, DifferentiableAt ℝ (deriv ψ) x) (b : ℝ) :
    deriv (deriv (fun x => C*(φ x+δ*(1+ψ x)))) b =
      C*(deriv (deriv φ) b+δ*deriv (deriv ψ) b) := by
  have he : deriv (fun x => C*(φ x+δ*(1+ψ x))) =
      fun x => C*(deriv φ x+δ*deriv ψ x) := by
    funext x
    simpa using ((hφ x).hasDerivAt.add (((hψ x).hasDerivAt.const_add 1).const_mul δ)).const_mul C |>.deriv
  rw [he]
  simpa using (((hφ' b).hasDerivAt.add ((hψ' b).hasDerivAt.const_mul δ)).const_mul C).deriv

end SLEExactGauge.Calculus

namespace SLEExactGauge.Parameter
open AngleCalculus Calculus

 

def physicalFactor (P : Parameter) (δ : ℝ → ℝ) (x : ℝ × ℂ) (b : ℝ) : ℝ :=
  Real.exp (P.p*x.1/2)/3 * P.f (δ x.1) (Real.sin (x.2-b).arg)

lemma physical_factor_state_derivative (P : Parameter) (δ : ℝ → ℝ)
    (u σ b v : ℝ) (z w : ℂ) (hy : 0 < z.im)
    (hδ : HasDerivAt δ (σ*δ u) u) :
    fderiv ℝ (fun x : ℝ × ℂ => P.physicalFactor δ x b) (u,z) (v,w) =
      Real.exp (P.p*u/2)/3 *
        (fderiv ℝ (fun z : ℂ => P.f (δ u) (Real.sin (z-b).arg)) z w+
          (P.p/2*P.f (δ u) (Real.sin (z-b).arg)+σ*δ u*(1+Real.sin (z-b).arg^P.q))*v) := by
  let e : ℝ → ℝ := fun r => Real.exp (P.p*r/2)/3
  let φ : ℂ → ℝ := fun w => Real.sin (w-b).arg^P.p
  let ψ : ℂ → ℝ := fun w => 1+Real.sin (w-b).arg^P.q
  have hs : 0 < Real.sin (z-(b:ℂ)).arg := sin_angle_pos (by simpa using hy)
  have ha : HasFDerivAt (fun w : ℂ => (w-b).arg) (angleD (z-b)) z := by
    convert! (hasFDerivAt_arg (show z-(b:ℂ) ∈ Complex.slitPlane from Or.inr (by simpa using hy.ne'))).comp z
      ((hasFDerivAt_id z).sub_const (b:ℂ)) using 1
  have hφ := (hasDerivAt_sinePower P.p (z-b).arg hs).hasFDerivAt.comp z ha
  have hψ := ((hasDerivAt_sinePower P.q (z-b).arg hs).const_add 1).hasFDerivAt.comp z ha
  change HasFDerivAt φ _ z at hφ
  change HasFDerivAt ψ _ z at hψ
  have he : HasDerivAt e (P.p/2*e u) u := by
    convert! (((hasDerivAt_id u).const_mul P.p).div_const 2).exp.div_const 3 using 1
    dsimp [e]
    ring
  have hd := fderiv_separable e δ φ ψ u z (P.p/2*e u) (σ*δ u) _ _ he hδ hφ hψ v w
  have hc := hφ.add (hψ.const_mul (δ u))
  change HasFDerivAt (fun z : ℂ => P.f (δ u) (Real.sin (z-b).arg)) _ z at hc
  change fderiv ℝ (fun x : ℝ × ℂ => e x.1*(φ x.2+δ x.1*ψ x.2)) (u,z) (v,w) = _
  rw [hd,hc.fderiv]
  simp only [add_apply,smul_apply]
  change (P.p/2*e u)*v*(φ z+δ u*ψ z)+e u*(_+σ*δ u*v*ψ z+δ u*_) =
    e u*(_+δ u*_+(P.p/2*(φ z+δ u*ψ z)+σ*δ u*ψ z)*v)
  ring

 

theorem physical_factor_generator (P : Parameter) (δ : ℝ → ℝ) (u σ b : ℝ)
    (z : ℂ) (hy : 0 < z.im) (hδ0 : 0 < δ u)
    (hδ : HasDerivAt δ (σ*δ u) u) :
    fderiv ℝ (fun x : ℝ × ℂ => P.physicalFactor δ x b) (u,z)
      ((V (z-b))^2,(P.a:ℂ)/(z-b))+
      deriv (deriv (P.physicalFactor δ (u,z))) b/2 =
      P.physicalFactor δ (u,z) b*(V (z-b))^2*
        P.drift (δ u) (Real.sin (z-b).arg) σ := by
  have hs : 0 < Real.sin (z-(b:ℂ)).arg := sin_angle_pos (by simpa using hy)
  have hphy := physical_generator_angle P.a (fun θ => P.f (δ u) (Real.sin θ))
    (fun θ hθ => (P.hasDerivAt_factor hθ).differentiableAt.hasDerivAt)
    (fun θ hθ => (P.factor_deriv_differentiable hθ).differentiableAt.hasDerivAt) hy b
  change physicalGenerator P.a (fun θ => P.f (δ u) (Real.sin θ)) z b =
    (V (z-b))^2*P.angleGenerator (fun θ => P.f (δ u) (Real.sin θ)) (z-b).arg at hphy
  have hsecond : deriv (deriv (P.physicalFactor δ (u,z))) b =
      Real.exp (P.p*u/2)/3*deriv (deriv (fun c : ℝ => P.f (δ u) (Real.sin (z-c).arg))) b := by
    change deriv (deriv (fun c : ℝ => Real.exp (P.p*u/2)/3*P.f (δ u) (Real.sin (z-c).arg))) b = _
    rw [deriv_const_mul_field',deriv_const_mul_field]
  rw [P.physical_factor_state_derivative δ u σ b _ z _ hy hδ,hsecond]
  have heq := (div_eq_iff (P.f_pos hδ0 hs).ne').mp (P.exact_factor_drift hδ0 hs σ)
  unfold physicalGenerator at hphy
  unfold physicalFactor
  linear_combination (Real.exp (P.p*u/2)/3)*hphy +
    (Real.exp (P.p*u/2)/3*(V (z-b))^2)*heq

end SLEExactGauge.Parameter

namespace SLEExactGauge.Parameter
open AngleCalculus Calculus

open scoped ContDiff
lemma contDiffAt_arg_real {z : ℂ} (hz : z ∈ Complex.slitPlane) (n : ℕ∞ω) :
    ContDiffAt ℝ n Complex.arg z := by
  have h := Complex.imCLM.contDiff.contDiffAt.comp z
    ((Complex.contDiffAt_log (n := n) hz).restrict_scalars ℝ)
  change ContDiffAt ℝ n (fun x => (Complex.log x).im) z at h
  simpa only [Complex.log_im] using h

lemma contDiffAt_physical_factor (P : Parameter) (δ : ℝ → ℝ)
    (u b : ℝ) (z : ℂ) (hy : 0 < z.im) (n : ℕ∞ω)
    (hδ : ContDiffAt ℝ n δ u) :
    ContDiffAt ℝ n (fun x : ℝ × ℂ => P.physicalFactor δ x b) (u,z) := by
  have hs : 0 < Real.sin (z-(b:ℂ)).arg := sin_angle_pos (by simpa using hy)
  have ha := (contDiffAt_arg_real (show z-(b:ℂ) ∈ Complex.slitPlane
      from Or.inr (by simpa using hy.ne')) n).comp (u,z)
    (contDiffAt_snd.sub contDiffAt_const)
  have hsin := ha.sin
  have hp := hsin.rpow_const_of_ne (p := P.p) hs.ne'
  have hq := hsin.rpow_const_of_ne (p := P.q) hs.ne'
  have he : ContDiffAt ℝ n (fun x : ℝ × ℂ => Real.exp (P.p*x.1/2)/3) (u,z) := by fun_prop
  exact he.mul (hp.add ((hδ.comp (u,z) contDiffAt_fst).mul (contDiffAt_const.add hq)))

end SLEExactGauge.Parameter

namespace SLEExactGauge.BrownianCalculus
open Classical
end SLEExactGauge.BrownianCalculus
end
end
end
end
end
end
end
end
end
end

end OAI
