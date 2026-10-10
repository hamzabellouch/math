import OAI.Analysis.IntegralMeans.Model

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def HasLogIncrement (γ : C(unitInterval, ℂ)) (q : ℂ) : Prop :=
  ∃ T : C(unitInterval, ℂ), (∀ t, Complex.exp (T t) = γ t) ∧ T 1-T 0 = q

lemma HasLogIncrement.perturb {γ η : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0)
    (h : ∀ t, ‖η t-γ t‖ < ‖γ t‖) : HasLogIncrement η q := by
  obtain ⟨T,hT,hend⟩ := hγ
  have hn (t) : γ t ≠ 0 := (hT t ▸ Complex.exp_ne_zero (T t))
  have hratio (t) : η t / γ t ∈ Complex.slitPlane := by
    have he : η t / γ t = 1 + (η t-γ t)/γ t := by field_simp [hn t]; ring
    rw [he]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hn t))]
    exact h t
  let R : C(unitInterval, ℂ) := ⟨fun t => Complex.log (η t / γ t), by
    apply Continuous.clog
    · exact η.continuous.div γ.continuous hn
    · exact hratio⟩
  refine ⟨T+R, ?_, ?_⟩
  · intro t
    change Complex.exp (T t+Complex.log (η t/γ t)) = η t
    rw [Complex.exp_add, hT t, Complex.exp_log (Complex.slitPlane_ne_zero (hratio t))]
    field_simp [hn t]
  · change (T 1+Complex.log (η 1/γ 1))-(T 0+Complex.log (η 0/γ 0))=q
    rw [hloopγ,hloopη]
    linear_combination hend

def circleLoop : C(unitInterval, ℂ) :=
  ⟨fun t => Complex.exp ((2*Real.pi*(t : ℝ) : ℝ)*Complex.I), by fun_prop⟩

@[simp] lemma circleLoop_zero : circleLoop 0 = 1 := by simp [circleLoop]

@[simp] lemma circleLoop_one : circleLoop 1 = 1 := by
  simp [circleLoop, Complex.exp_two_pi_mul_I]

@[simp] lemma norm_circleLoop (t : unitInterval) : ‖circleLoop t‖ = 1 := by
  simp [circleLoop, Complex.norm_exp]

lemma circleLoop_logIncrement (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement (a • circleLoop) (2*Real.pi*Complex.I) := by
  refine ⟨⟨fun t => Complex.log a+(2*Real.pi*(t : ℝ) : ℝ)*Complex.I, by fun_prop⟩, ?_, ?_⟩
  · intro t
    simp [Complex.exp_add, Complex.exp_log ha, circleLoop]
  · simp

lemma conj_circleLoop_logIncrement (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement
      ⟨fun t => a*conj (circleLoop t), by fun_prop⟩ (-(2*Real.pi*Complex.I)) := by
  refine ⟨⟨fun t => Complex.log a-(2*Real.pi*(t : ℝ) : ℝ)*Complex.I, by fun_prop⟩, ?_, ?_⟩
  · intro t
    simp only [ContinuousMap.coe_mk, circleLoop, Complex.exp_sub, Complex.exp_log ha]
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      Complex.exp_neg]
    rfl
  · simp

def linearPart (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1-Complex.I*A Complex.I)/2

def antiLinearPart (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1+Complex.I*A Complex.I)/2

lemma realLinear_decomposition (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = linearPart A*z+antiLinearPart A*conj z := by
  have he : z = z.re • (1 : ℂ)+z.im • Complex.I := by simp [Complex.real_smul]
  calc
    A z = z.re • A 1+z.im • A Complex.I := by
      conv_lhs => rw [he, map_add, map_smul, map_smul]
    _ = linearPart A*z+antiLinearPart A*conj z := by
      apply Complex.ext <;>
        simp [linearPart, antiLinearPart, Complex.mul_re, Complex.mul_im,
          Complex.real_smul] <;> ring

lemma determinant_complex_real (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re*(A Complex.I).im-(A Complex.I).re*(A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

lemma det_eq_linearParts (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det A.toLinearMap = ‖linearPart A‖^2-‖antiLinearPart A‖^2 := by
  rw [determinant_complex_real]
  simp only [← Complex.normSq_eq_norm_sq, linearPart, antiLinearPart,
    Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

lemma linear_circle_logIncrement_pos (A : ℂ →L[ℝ] ℂ)
    (hA : 0 < LinearMap.det A.toLinearMap) :
    HasLogIncrement ⟨fun t => A (circleLoop t), by fun_prop⟩ (2*Real.pi*Complex.I) := by
  have hn : ‖antiLinearPart A‖ < ‖linearPart A‖ := by
    rw [det_eq_linearParts] at hA
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  have ha : linearPart A ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hn)
  apply (circleLoop_logIncrement (linearPart A) ha).perturb
  · simp
  · simp
  · intro t
    simp only [ContinuousMap.coe_mk, ContinuousMap.coe_smul, Pi.smul_apply,
      smul_eq_mul, realLinear_decomposition, add_sub_cancel_left, norm_mul,
      RCLike.norm_conj, norm_circleLoop, mul_one]
    exact hn

lemma linear_circle_logIncrement_neg (A : ℂ →L[ℝ] ℂ)
    (hA : LinearMap.det A.toLinearMap < 0) :
    HasLogIncrement ⟨fun t => A (circleLoop t), by fun_prop⟩ (-(2*Real.pi*Complex.I)) := by
  have hn : ‖linearPart A‖ < ‖antiLinearPart A‖ := by
    rw [det_eq_linearParts] at hA
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  have ha : antiLinearPart A ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hn)
  apply (conj_circleLoop_logIncrement (antiLinearPart A) ha).perturb
  · simp
  · simp
  · intro t
    simp only [ContinuousMap.coe_mk, realLinear_decomposition, add_sub_cancel_right,
      norm_mul, RCLike.norm_conj, norm_circleLoop, mul_one]
    exact hn

lemma HasLogIncrement.smul {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) {c : ℂ} (hc : c ≠ 0) :
    HasLogIncrement (c • γ) q := by
  obtain ⟨T,hT,hend⟩ := hγ
  refine ⟨T+ContinuousMap.const _ (Complex.log c), ?_, ?_⟩
  · intro t
    change Complex.exp (T t+Complex.log c) = c*γ t
    rw [Complex.exp_add, hT t, Complex.exp_log hc, mul_comm]
  · change (T 1+Complex.log c)-(T 0+Complex.log c)=q
    linear_combination hend

lemma norm_linear_lower_pos (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    (‖linearPart A‖-‖antiLinearPart A‖)*‖z‖ ≤ ‖A z‖ := by
  have ht := norm_sub_norm_le (linearPart A*z) (-antiLinearPart A*conj z)
  rw [norm_mul, norm_mul, norm_neg, RCLike.norm_conj] at ht
  simp only [neg_mul, sub_neg_eq_add, ← realLinear_decomposition] at ht
  nlinarith

lemma norm_linear_lower_neg (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    (‖antiLinearPart A‖-‖linearPart A‖)*‖z‖ ≤ ‖A z‖ := by
  have ht := norm_sub_norm_le (antiLinearPart A*conj z) (-linearPart A*z)
  rw [norm_mul, norm_mul, norm_neg, RCLike.norm_conj] at ht
  simp only [neg_mul, sub_neg_eq_add, add_comm, ← realLinear_decomposition] at ht
  nlinarith

lemma local_logIncrement_of_derivative {X : ℂ → ℂ} {z : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hX : Continuous X) (hzero : X z = 0) (hd : HasFDerivAt X A z)
    {c : ℝ} (hc : 0 < c) (hlower : ∀ w, c*‖w‖ ≤ ‖A w‖) {q : ℂ}
    (hA : HasLogIncrement ⟨fun t => A (circleLoop t), by fun_prop⟩ q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      HasLogIncrement ⟨fun t => X (z+(r : ℂ)*circleLoop t), by fun_prop⟩ q := by
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound (by positivity : 0 < c/2)
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp hrem
  refine ⟨δ,hδ,fun r hr hrd => ?_⟩
  have hn (t : unitInterval) : ‖(r : ℂ)*circleLoop t‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  apply (hA.smul (Complex.ofReal_ne_zero.mpr hr.ne')).perturb
  · simp
  · simp
  · intro t
    have hb := hbound (show dist ((r : ℂ)*circleLoop t) 0 < δ by simpa only [dist_zero_right, hn] using hrd)
    have he : A ((r : ℂ)*circleLoop t) = (r : ℂ)*A (circleLoop t) := by
      exact A.map_smul r (circleLoop t)
    change ‖X (z+(r : ℂ)*circleLoop t)-(r : ℂ)*A (circleLoop t)‖ < ‖(r : ℂ)*A (circleLoop t)‖
    rw [hzero, sub_zero, he, hn] at hb
    have hl := hlower ((r : ℂ)*circleLoop t)
    rw [hn, he] at hl
    exact hb.trans_lt ((by nlinarith : c/2*r < c*r).trans_le hl)

lemma local_logIncrement_pos {X : ℂ → ℂ} {z : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hX : Continuous X) (hzero : X z = 0) (hd : HasFDerivAt X A z)
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      HasLogIncrement ⟨fun t => X (z+(r : ℂ)*circleLoop t), by fun_prop⟩ (2*Real.pi*Complex.I) := by
  have hc : 0 < ‖linearPart A‖-‖antiLinearPart A‖ := by
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  exact local_logIncrement_of_derivative hX hzero hd hc (norm_linear_lower_pos A)
    (linear_circle_logIncrement_pos A hdet)

lemma local_logIncrement_neg {X : ℂ → ℂ} {z : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hX : Continuous X) (hzero : X z = 0) (hd : HasFDerivAt X A z)
    (hdet : LinearMap.det A.toLinearMap < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      HasLogIncrement ⟨fun t => X (z+(r : ℂ)*circleLoop t), by fun_prop⟩ (-(2*Real.pi*Complex.I)) := by
  have hc : 0 < ‖antiLinearPart A‖-‖linearPart A‖ := by
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  exact local_logIncrement_of_derivative hX hzero hd hc (norm_linear_lower_neg A)
    (linear_circle_logIncrement_neg A hdet)

lemma exists_log_lift (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    ∃ T : C(unitInterval, ℂ), ∀ t, Complex.exp (T t) = γ t := by
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨T, ⟨-,hT⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    γ (Complex.exp_log (hγ 0)) hγ
  exact ⟨T, fun t => congrFun hT t⟩

lemma log_lifts_difference_constant.{u_1} {X : Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B : X → ℂ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, Complex.exp (A x) = Complex.exp (B x)) (x y : X) :
    A y - B y = A x - B x := by
  have hC : Continuous (fun z => B z + (A x - B x)) := hB.add continuous_const
  have he (z) : Complex.exp (A z) = Complex.exp (B z + (A x - B x)) := by
    rw [Complex.exp_add, Complex.exp_sub, h x, div_self (Complex.exp_ne_zero _), mul_one]
    exact h z
  have heq : A = fun z => B z + (A x - B x) :=
    Complex.isCoveringMap_exp.eq_of_comp_eq hA hC
      (by funext z; exact Subtype.ext (he z)) x (by ring)
  have hy := congrFun heq y
  linear_combination hy

lemma HasLogIncrement.unique {γ : C(unitInterval, ℂ)} {p q : ℂ}
    (hp : HasLogIncrement γ p) (hq : HasLogIncrement γ q) : p = q := by
  obtain ⟨A,hA,hp⟩ := hp
  obtain ⟨B,hB,hq⟩ := hq
  have he := log_lifts_difference_constant A.continuous B.continuous
    (fun t => (hA t).trans (hB t).symm) (0 : unitInterval) 1
  linear_combination hp.symm - hq.symm + he

lemma HasLogIncrement.mul {γ η : C(unitInterval, ℂ)} {p q : ℂ}
    (hγ : HasLogIncrement γ p) (hη : HasLogIncrement η q) :
    HasLogIncrement (γ * η) (p + q) := by
  obtain ⟨A,hA,hp⟩ := hγ
  obtain ⟨B,hB,hq⟩ := hη
  refine ⟨A+B, ?_, ?_⟩
  · intro t
    change Complex.exp (A t+B t) = γ t * η t
    rw [Complex.exp_add, hA t, hB t]
  · change (A 1+B 1)-(A 0+B 0)=p+q
    linear_combination hp+hq

lemma HasLogIncrement.inv {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => (γ t)⁻¹, by
      exact γ.continuous.inv₀ (fun t => by
        obtain ⟨A,hA,-⟩ := hγ
        exact (hA t ▸ Complex.exp_ne_zero (A t)))⟩ (-q) := by
  obtain ⟨A,hA,hq⟩ := hγ
  refine ⟨-A, ?_, ?_⟩
  · intro t
    change Complex.exp (-A t) = (γ t)⁻¹
    rw [Complex.exp_neg, hA t]
  · change -A 1-(-A 0) = -q
    linear_combination -hq

lemma HasLogIncrement.conj {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => conj (γ t), by fun_prop⟩ (conj q) := by
  obtain ⟨A,hA,hq⟩ := hγ
  refine ⟨⟨fun t => conj (A t), by fun_prop⟩, ?_, ?_⟩
  · intro t
    exact (Complex.exp_conj _).trans (congrArg conj (hA t))
  · change conj (A 1)-conj (A 0)=conj q
    rw [← map_sub, hq]

lemma HasLogIncrement.of_global_log.{u_1} {X : Type u_1} [TopologicalSpace X]
    (f : C(X, ℂ)) (A : C(X, ℂ)) (hA : ∀ x, Complex.exp (A x) = f x)
    (γ : C(unitInterval, X)) (hγ : γ 1 = γ 0) :
    HasLogIncrement (f.comp γ) 0 := by
  refine ⟨A.comp γ, fun t => hA (γ t), ?_⟩
  change A (γ 1)-A (γ 0)=0
  rw [hγ, sub_self]

lemma HasLogIncrement.integer {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) (hloop : γ 1 = γ 0) :
    ∃ n : ℤ, q = n*(2*Real.pi*Complex.I) := by
  obtain ⟨A,hA,hq⟩ := hγ
  apply Complex.exp_eq_one_iff.mp
  rw [← hq, Complex.exp_sub, hA 1, hA 0, hloop,
    div_self (hA 0 ▸ Complex.exp_ne_zero _)]

lemma period_ne_zero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

lemma integer_period_injective : Function.Injective
    (fun n : ℤ => (n : ℂ)*(2*Real.pi*Complex.I)) := by
  intro n m h
  exact_mod_cast (mul_right_cancel₀ period_ne_zero h : (n : ℂ) = m)

lemma exists_integer_logIncrement (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ≠ 0) :
    ∃ n : ℤ, HasLogIncrement γ (n*(2*Real.pi*Complex.I)) := by
  obtain ⟨A, hA⟩ := exists_log_lift γ hγ
  have hi : HasLogIncrement γ (A 1-A 0) := ⟨A,hA,rfl⟩
  obtain ⟨n,hn⟩ := hi.integer hloop
  exact ⟨n, hn ▸ hi⟩

def windingNumber (γ : C(unitInterval, ℂ)) : ℤ := by
  classical
  exact if h : γ 1 = γ 0 ∧ ∀ t, γ t ≠ 0 then
    Classical.choose (exists_integer_logIncrement γ h.1 h.2)
  else 0

lemma windingNumber_spec (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ≠ 0) :
    HasLogIncrement γ ((windingNumber γ)*(2*Real.pi*Complex.I)) := by
  rw [windingNumber, dite_eq_left ⟨hloop,hγ⟩]
  exact Classical.choose_spec (exists_integer_logIncrement γ hloop hγ)

lemma windingNumber_eq_of_logIncrement {γ : C(unitInterval, ℂ)} {n : ℤ}
    (hloop : γ 1 = γ 0) (h : HasLogIncrement γ (n*(2*Real.pi*Complex.I))) :
    windingNumber γ = n := by
  have hn (t) : γ t ≠ 0 := by
    obtain ⟨A,hA,-⟩ := h
    exact hA t ▸ Complex.exp_ne_zero _
  exact integer_period_injective ((windingNumber_spec γ hloop hn).unique h)

lemma windingNumber_mul (γ η : C(unitInterval, ℂ))
    (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0)
    (hγ : ∀ t, γ t ≠ 0) (hη : ∀ t, η t ≠ 0) :
    windingNumber (γ*η) = windingNumber γ + windingNumber η := by
  apply windingNumber_eq_of_logIncrement (by simp [hloopγ,hloopη])
  convert (windingNumber_spec γ hloopγ hγ).mul (windingNumber_spec η hloopη hη) using 1
  push_cast
  ring

lemma windingNumber_perturb {γ η : C(unitInterval, ℂ)}
    (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0) (hγ : ∀ t, γ t ≠ 0)
    (h : ∀ t, ‖η t-γ t‖ < ‖γ t‖) : windingNumber η = windingNumber γ :=
  windingNumber_eq_of_logIncrement hloopη
    ((windingNumber_spec γ hloopγ hγ).perturb hloopγ hloopη h)

lemma exists_log_lift_of_simplyConnected.{u_1} {X : Type u_1} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x : X)
    (f : C(X, ℂ)) (hf : ∀ y, f y ≠ 0) :
    ∃ A : C(X, ℂ), ∀ y, Complex.exp (A y) = f y := by
  obtain ⟨A, ⟨-,hA⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    f (Complex.exp_log (hf x)) hf
  exact ⟨A, fun y => congrFun hA y⟩

lemma HasLogIncrement.homotopy {H : C(unitInterval × unitInterval, ℂ)}
    (hH : ∀ p, H p ≠ 0) (hloop : ∀ s, H (s,1) = H (s,0)) {q : ℂ}
    (h : HasLogIncrement ⟨fun t => H (0,t), by fun_prop⟩ q) :
    HasLogIncrement ⟨fun t => H (1,t), by fun_prop⟩ q := by
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA⟩ := exists_log_lift_of_simplyConnected (0,0) H hH
  have hi : HasLogIncrement ⟨fun t => H (0,t), by fun_prop⟩ (A (0,1)-A (0,0)) :=
    ⟨⟨fun t => A (0,t), by fun_prop⟩, fun t => hA (0,t), rfl⟩
  have hc := log_lifts_difference_constant
    (show Continuous (fun s => A (s,1)) by fun_prop)
    (show Continuous (fun s => A (s,0)) by fun_prop)
    (fun s => by rw [hA, hA, hloop]) (0 : unitInterval) 1
  refine ⟨⟨fun t => A (1,t), by fun_prop⟩, fun t => hA (1,t), ?_⟩
  change A (1,1)-A (1,0)=q
  exact hc.trans (hi.unique h)

lemma windingNumber_homotopy (H : C(unitInterval × unitInterval, ℂ))
    (hH : ∀ p, H p ≠ 0) (hloop : ∀ s, H (s,1) = H (s,0)) :
    windingNumber ⟨fun t => H (1,t), by fun_prop⟩ =
      windingNumber ⟨fun t => H (0,t), by fun_prop⟩ := by
  apply windingNumber_eq_of_logIncrement (hloop 1)
  exact (windingNumber_spec ⟨fun t => H (0,t), by fun_prop⟩ (hloop 0)
    (fun t => hH (0,t))).homotopy hH hloop

def loopIndex (γ : C(unitInterval, ℂ)) (a : ℂ) : ℤ :=
  windingNumber ⟨fun t => γ t-a, by fun_prop⟩

lemma loopIndex_eventually_eq (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : a ∉ range γ) : ∀ᶠ b in 𝓝 a, loopIndex γ b = loopIndex γ a := by
  have hn (t) : γ t-a ≠ 0 := sub_ne_zero.mpr (fun h => ha ⟨t,h⟩)
  obtain ⟨d,hd,hdist⟩ := isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t : unitInterval => ‖γ t-a‖) univ by fun_prop)
    (a := 0) (fun t _ => norm_pos_iff.mpr (hn t))
  filter_upwards [Metric.ball_mem_nhds a hd] with b hb
  apply windingNumber_perturb (by simp [hloop]) (by simp [hloop]) hn
  intro t
  change ‖(γ t-b)-(γ t-a)‖ < ‖γ t-a‖
  rw [show (γ t-b)-(γ t-a)=a-b by ring, norm_sub_rev]
  exact (show ‖b-a‖ < d by simpa [Metric.mem_ball, dist_eq_norm] using hb).trans_le (hdist t (mem_univ t))

lemma continuousOn_loopIndex (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    ContinuousOn (loopIndex γ) (range γ)ᶜ := by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have he : loopIndex γ =ᶠ[𝓝 a] fun _ => loopIndex γ a :=
    loopIndex_eventually_eq γ hloop ha
  exact continuousAt_const.congr he.symm

lemma hasLogIncrement_constant (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement (ContinuousMap.const unitInterval a) 0 := by
  exact ⟨ContinuousMap.const unitInterval (Complex.log a),
    fun _ => Complex.exp_log ha, sub_self _⟩

lemma loopIndex_eq_zero_of_norm_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, ‖γ t‖ < ‖a‖) : loopIndex γ a = 0 := by
  have hane : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg (γ 0)).trans_lt (ha 0))
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  have hh : HasLogIncrement ⟨fun t => γ t-a, by fun_prop⟩ 0 :=
    (hasLogIncrement_constant (-a) (neg_ne_zero.mpr hane)).perturb rfl
      (by simp [hloop]) (fun t => by simpa using ha t)
  simpa using hh

lemma loopIndex_zero_outside_ball (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : ℂ, R ≤ ‖a‖ → loopIndex γ a = 0 := by
  obtain ⟨R,-,hR⟩ := (isCompact_range γ.continuous).isBounded.exists_pos_norm_lt
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro a ha
  apply loopIndex_eq_zero_of_norm_lt γ hloop
  intro t
  exact (hR (γ t) ⟨t,rfl⟩).trans_le ((le_max_left R 1).trans ha)

def windingInterior (γ : C(unitInterval, ℂ)) : Set ℂ :=
  {a | a ∉ range γ ∧ loopIndex γ a ≠ 0}

lemma isOpen_windingInterior (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    IsOpen (windingInterior γ) := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hc := (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds ha.1
  filter_upwards [hc, loopIndex_eventually_eq γ hloop ha.1] with b hb heq
  exact ⟨hb, heq ▸ ha.2⟩

lemma isBounded_windingInterior (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    Bornology.IsBounded (windingInterior γ) := by
  obtain ⟨R,-,hR⟩ := loopIndex_zero_outside_ball γ hloop
  apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset
  intro a ha
  rw [Metric.mem_ball, dist_zero_right]
  by_contra h
  exact ha.2 (hR a (le_of_not_gt h))

lemma frontier_windingInterior_subset (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    frontier (windingInterior γ) ⊆ range γ := by
  intro a ha
  by_contra han
  have hn : (range γ)ᶜ ∈ 𝓝 a :=
    (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds han
  have he := loopIndex_eventually_eq γ hloop han
  by_cases hi : loopIndex γ a = 0
  · have hh : (windingInterior γ)ᶜ ∈ 𝓝 a := by
      filter_upwards [he] with b hb
      intro hbin
      exact hbin.2 (hb.trans hi)
    exact (mem_closure_iff_nhds.1 ha.1 _ hh).elim (fun b hb => hb.1 hb.2)
  · have hnmem := ha.2
    rw [(isOpen_windingInterior γ hloop).interior_eq] at hnmem
    exact hnmem ⟨han,hi⟩

end Brennan

end

end OAI
