import Mathlib

namespace OAI

section
/-! Literal first and second coordinate chain rules. The maps are genuine
Frechet-smooth maps; a tensor pullback will use these identities, rather
than postulating a transformed elasticity operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChainRule
abbrev Y := Fin 3 → ℝ
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dd (f : E → ℂ) (v : E) (x : E) : ℂ := fderiv ℝ f x v
def cp (f : Y → ℂ) (α : Fin 3) : Y → ℂ := dd f (Pi.single α 1)
def jac (ψ : E → Y) (v : E) (α : Fin 3) (x : E) : ℝ := fderiv ℝ ψ x v α

def hess (ψ : E → Y) (v w : E) (α : Fin 3) (x : E) : ℝ :=
  fderiv ℝ (jac ψ w α) x v

lemma smooth_dd {f : E → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (dd f v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma smooth_jac {ψ : E → Y} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v : E) (α : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (jac ψ v α) :=
  (contDiff_apply ℝ ℝ α).comp ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)

lemma fderiv_basis (f : Y → ℂ) (x v : Y) :
    fderiv ℝ f x v=∑ α, (v α:ℂ)*cp f α x := by
  have hv : v=∑ α : Fin 3, v α • Pi.single α (1:ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    _ = fderiv ℝ f x (∑ α, v α • Pi.single α (1:ℝ)) := congrArg _ hv
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro α _
      rw [map_smul]
      exact Complex.real_smul

lemma dd_comp {f : Y → ℂ} {ψ : E → Y} (hf : Differentiable ℝ f)
    (hψ : Differentiable ℝ ψ) (v x : E) :
    dd (fun x => f (ψ x)) v x=∑ α, (jac ψ v α x:ℂ)*cp f α (ψ x) := by
  change fderiv ℝ (f ∘ ψ) x v=_
  rw [fderiv_comp x (hf _) (hψ x), ContinuousLinearMap.comp_apply, fderiv_basis]
  rfl

lemma dd_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℂ)
    (hf : ∀ i∈s, Differentiable ℝ (f i)) (v x : E) :
    dd (fun z => ∑ i∈s, f i z) v x=∑ i∈s, dd (f i) v x := by
  rw [dd, fderiv_fun_sum (fun i hi => hf i hi x), sum_apply]
  rfl

lemma dd_mul {f g : E → ℂ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (v x : E) : dd (fun z => f z*g z) v x=dd f v x*g x+f x*dd g v x := by
  rw [dd, fderiv_fun_mul (hf x) (hg x)]
  simp only [add_apply, smul_apply, smul_eq_mul, dd]
  ring

lemma dd_ofReal {f : E → ℝ} (hf : Differentiable ℝ f) (v x : E) :
    dd (fun z => (f z:ℂ)) v x=(fderiv ℝ f x v:ℂ) := by
  exact congrArg (fun A : E →L[ℝ] ℂ => A v)
    (Complex.ofRealCLM.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv

/-- The second chain rule with the exact Hessian-of-coordinate lower term. -/
theorem dd_dd_comp {f : Y → ℂ} {ψ : E → Y}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (v w x : E) :
    dd (dd (fun z => f (ψ z)) w) v x=
      (∑ β, (hess ψ v w β x:ℂ)*cp f β (ψ x))+
      ∑ β, ∑ α, (jac ψ w β x:ℂ)*(jac ψ v α x:ℂ)*cp (cp f β) α (ψ x) := by
  have heq : dd (fun z => f (ψ z)) w=
      fun z => ∑ β, (jac ψ w β z:ℂ)*cp f β (ψ z) :=
    funext (dd_comp (hf.differentiable (by simp)) (hψ.differentiable (by simp)) w)
  rw [heq, dd_sum]
  · have hc (β : Fin 3) : Differentiable ℝ (cp f β) :=
      (smooth_dd hf _).differentiable (by simp)
    have hJ (β : Fin 3) : Differentiable ℝ (jac ψ w β) :=
      (smooth_jac hψ w β).differentiable (by simp)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro β _
    rw [dd_mul (f := fun z => (jac ψ w β z : ℂ)) (g := fun z => cp f β (ψ z))
      (Complex.ofRealCLM.differentiable.comp (hJ β))
      ((hc β).comp (hψ.differentiable (by simp))), dd_ofReal (hJ β),
      dd_comp (hc β) (hψ.differentiable (by simp)), Finset.mul_sum]
    simp only [hess, mul_assoc]
  · intro β _
    exact (Complex.ofRealCLM.differentiable.comp ((smooth_jac hψ w β).differentiable (by simp))).mul
      (((smooth_dd hf _).differentiable (by simp)).comp (hψ.differentiable (by simp)))

end ElasticityBoundaryChainRule

end
end
section
/-! Literal smooth polynomial amplitudes in boundary coordinates, including
actual Frechet derivatives and polynomial growth. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace ElasticityBoundaryMVCalculus
abbrev Y := Fin 3 → ℝ
abbrev MP := MvPolynomial (Fin 3) ℂ

def complexCoord (i : Fin 3) : Y →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

@[simp] lemma complexCoord_apply (i : Fin 3) (y : Y) : complexCoord i y=(y i : ℂ) := rfl

def value (p : MP) (y : Y) : ℂ := eval (fun i => (y i : ℂ)) p

@[simp] lemma value_C (c : ℂ) (y : Y) : value (C c) y=c := by simp [value]
@[simp] lemma value_X (i : Fin 3) (y : Y) : value (X i) y=(y i : ℂ) := by simp [value]
@[simp] lemma value_zero (y : Y) : value 0 y=0 := by simp [value]
@[simp] lemma value_one (y : Y) : value 1 y=1 := by simp [value]
@[simp] lemma value_add (p q : MP) (y : Y) : value (p+q) y=value p y+value q y := by simp [value]
@[simp] lemma value_sub (p q : MP) (y : Y) : value (p-q) y=value p y-value q y := by simp [value]
@[simp] lemma value_mul (p q : MP) (y : Y) : value (p*q) y=value p y*value q y := by simp [value]
@[simp] lemma value_smul (c : ℂ) (p : MP) (y : Y) : value (c • p) y=c*value p y := by
  simp [value, smul_eq_C_mul]

lemma value_C_fn (c : ℂ) : value (C c) = (fun _ => c) := funext (value_C c)
lemma value_add_fn (p q : MP) : value (p+q)=value p+value q := funext (value_add p q)
lemma value_mul_fn (p q : MP) : value (p*q)=value p*value q := funext (value_mul p q)
lemma value_X_fn (i : Fin 3) : value (X i)=complexCoord i := funext (value_X i)

lemma smooth_value (p : MP) : ContDiff ℝ (⊤ : ℕ∞) (value p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [value_C_fn]; exact contDiff_const
  | add p q hp hq => rw [value_add_fn]; exact hp.add hq
  | mul_X p i hp => rw [value_mul_fn, value_X_fn]; exact hp.mul (complexCoord i).contDiff

def differential (p : MP) (y : Y) : Y →L[ℝ] ℂ :=
  ∑ i, value (pderiv i p) y • complexCoord i

@[simp] lemma differential_C (c : ℂ) (y : Y) : differential (C c) y=0 := by
  apply ContinuousLinearMap.ext
  intro z
  simp [differential, sum_apply, smul_apply]

@[simp] lemma differential_add (p q : MP) (y : Y) :
    differential (p+q) y=differential p y+differential q y := by
  apply ContinuousLinearMap.ext
  intro z
  simp [differential, sum_apply, smul_apply, add_mul, Finset.sum_add_distrib]

lemma differential_mul_X (p : MP) (j : Fin 3) (y : Y) :
    differential (p*X j) y = value p y • complexCoord j + (y j : ℂ) • differential p y := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [differential, pderiv_mul, value_add, value_mul, pderiv_X, Pi.single_apply,
    sum_apply, add_apply,
    smul_apply, complexCoord_apply, smul_eq_mul]
  simp only [value_X, add_mul, Finset.sum_add_distrib]
  have h (i : Fin 3) : value (if j=i then 1 else 0 : MP) y = if j=i then 1 else 0 := by
    split_ifs <;> simp
  simp only [h, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The evaluated formal partial derivatives are the actual Frechet derivative. -/
theorem hasFDerivAt_value (p : MP) (y : Y) : HasFDerivAt (value p) (differential p y) y := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [value_C_fn, differential_C]; exact hasFDerivAt_const c y
  | add p q hp hq => rw [value_add_fn, differential_add]; exact hp.add hq
  | mul_X p i hp =>
      rw [value_mul_fn, value_X_fn, differential_mul_X]
      exact hp.mul ((complexCoord i).hasFDerivAt (x := y))

lemma differential_basis (p : MP) (y : Y) (i : Fin 3) :
    differential p y (Pi.single i 1) = value (pderiv i p) y := by
  simp [differential, Pi.single_apply, apply_ite Complex.ofReal, mul_ite]

theorem fderiv_value_basis (p : MP) (y : Y) (i : Fin 3) :
    fderiv ℝ (value p) y (Pi.single i 1)=value (pderiv i p) y := by
  rw [(hasFDerivAt_value p y).fderiv, differential_basis]

/-- Every fixed amplitude is bounded by a uniform polynomial moment, so the
Gaussian/exponential majorants used for its remainder are honest integrable functions. -/
theorem polynomialGrowth (p : MP) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ y : Y, ‖value p y‖ ≤ C*(1+‖y‖)^d := by
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, norm_nonneg _, 0, fun y => by simp⟩
  | add p q hp hq =>
      obtain ⟨A,hA,a,ha⟩ := hp
      obtain ⟨B,hB,b,hb⟩ := hq
      refine ⟨A+B,add_nonneg hA hB,max a b,fun y => ?_⟩
      have hbase : 1 ≤ 1+‖y‖ := by linarith [norm_nonneg y]
      calc
        _ ≤ ‖value p y‖+‖value q y‖ := by rw [value_add]; exact norm_add_le _ _
        _ ≤ A*(1+‖y‖)^a+B*(1+‖y‖)^b := add_le_add (ha y) (hb y)
        _ ≤ A*(1+‖y‖)^(max a b)+B*(1+‖y‖)^(max a b) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_left _ _)) hA)
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (le_max_right _ _)) hB)
        _ = _ := by ring
  | mul_X p i hp =>
      obtain ⟨A,hA,a,ha⟩ := hp
      refine ⟨A,hA,a+1,fun y => ?_⟩
      have hcoord : ‖(y i : ℂ)‖ ≤ 1+‖y‖ := by
        rw [Complex.norm_real]
        exact (norm_le_pi_norm y i).trans (by linarith)
      calc
        _ = ‖value p y‖*‖(y i : ℂ)‖ := by rw [value_mul, value_X, norm_mul]
        _ ≤ (A*(1+‖y‖)^a)*(1+‖y‖) :=
          mul_le_mul (ha y) hcoord (norm_nonneg _) (by positivity)
        _ = _ := by rw [pow_succ]; ring

end ElasticityBoundaryMVCalculus

end
end
section
/-! Exact anisotropic boundary scaling, retaining the physical dimension-three
Jacobian δ⁴. No asymptotic change-of-variable formula is postulated. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryScaling
abbrev Y := Fin 3 → ℝ

def scaleFactor (δ : ℝ) (i : Fin 3) : ℝ := if i=2 then δ^2 else δ

def scale (δ : ℝ) : Y →L[ℝ] Y :=
  ContinuousLinearMap.pi (fun i =>
    (scaleFactor δ i • ContinuousLinearMap.id ℝ ℝ).comp (ContinuousLinearMap.proj i))

@[simp] lemma scale_apply (δ : ℝ) (y : Y) (i : Fin 3) :
    scale δ y i = scaleFactor δ i * y i := rfl

lemma scale_zero (y : Y) : scale 0 y = 0 := by
  ext i
  simp [scaleFactor]

lemma scale_comp (δ ε : ℝ) (y : Y) : scale δ (scale ε y) = scale (δ*ε) y := by
  ext i
  simp only [scale_apply, scaleFactor]
  split_ifs <;> ring

@[simp] lemma scale_one (y : Y) : scale 1 y = y := by
  ext i
  simp [scaleFactor]

lemma scale_inv (δ : ℝ) (hδ : δ≠0) (y : Y) : scale δ (scale δ⁻¹ y) = y := by
  rw [scale_comp, mul_inv_cancel₀ hδ, scale_one]

lemma scale_injective (δ : ℝ) (hδ : δ≠0) : Function.Injective (scale δ) := by
  intro y z h
  have := congrArg (scale δ⁻¹) h
  simpa only [scale_comp, inv_mul_cancel₀ hδ, scale_one] using this

lemma scale_surjective (δ : ℝ) (hδ : δ≠0) : Function.Surjective (scale δ) :=
  fun y => ⟨scale δ⁻¹ y, scale_inv δ hδ y⟩

lemma scale_det (δ : ℝ) : (scale δ).det = δ^4 := by
  change LinearMap.det (LinearMap.pi (fun i : Fin 3 =>
    (scaleFactor δ i • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj i))) = _
  rw [LinearMap.det_pi]
  simp [scaleFactor, Fin.prod_univ_three]
  ring

lemma scale_norm_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (y : Y) :
    ‖scale δ y‖ ≤ δ*‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hδ (norm_nonneg y))).mpr
  intro i
  have hc : |scaleFactor δ i| ≤ δ := by
    unfold scaleFactor
    split_ifs
    · rw [abs_of_nonneg (sq_nonneg δ)]
      nlinarith
    · rw [abs_of_nonneg hδ]
  simpa only [scale_apply, Real.norm_eq_abs, abs_mul] using
    mul_le_mul hc (norm_le_pi_norm y i) (abs_nonneg (y i)) hδ

lemma continuous_scale_at (y : Y) : Continuous (fun δ : ℝ => scale δ y) := by
  apply continuous_pi
  intro i
  simp only [scale_apply, scaleFactor]
  split_ifs <;> fun_prop

lemma scale_tendsto_zero (y : Y) : Filter.Tendsto (fun δ : ℝ => scale δ y) (nhds 0) (nhds 0) := by
  simpa only [scale_zero] using (continuous_scale_at y).tendsto 0

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact full-space change of variables; valid even when the integral is the
Bochner fallback zero, and for vector-valued functions. -/
theorem integral_scale {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    (∫ y, f y) = δ^4 • ∫ y, f (scale δ y) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure Y)
    (f := scale δ) (f' := fun _ => scale δ) MeasurableSet.univ
    (fun y _ => (scale δ).hasFDerivAt.hasFDerivWithinAt)
    (scale_injective δ hδ).injOn f
  simpa only [image_univ, (scale_surjective δ hδ).range_eq, Measure.restrict_univ,
    scale_det, abs_of_nonneg (show 0 ≤ δ^4 by positivity), integral_smul] using h

lemma scaled_integrable_iff {δ : ℝ} (hδ : δ≠0) (f : Y → F) :
    Integrable (fun y => f (scale δ y)) ↔ Integrable f := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure Y)
    (f := scale δ) (f' := fun _ => scale δ) MeasurableSet.univ
    (fun y _ => (scale δ).hasFDerivAt.hasFDerivWithinAt)
    (scale_injective δ hδ).injOn f
  have hp : δ^4 ≠ 0 := pow_ne_zero _ hδ
  simpa only [image_univ, (scale_surjective δ hδ).range_eq, integrableOn_univ,
    scale_det, abs_of_nonneg (show 0 ≤ δ^4 by positivity), integrable_fun_smul_iff hp] using h.symm

end ElasticityBoundaryScaling

end
end
section
/-! Integrable polynomial majorants for the physical anisotropic boundary-layer
profiles. The decay and all moments are proved, not assumed symbol bounds. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ElasticityBoundaryWeights
abbrev Y := Fin 3 → ℝ

def factor (b : ℝ) (i : Fin 3) (t : ℝ) : ℝ :=
  if i = 2 then (Ioi (0 : ℝ)).indicator (fun s => Real.exp (-b*s)) t
  else Real.exp (-b*t^2)

def weight (b : ℝ) (y : Y) : ℝ := ∏ i, factor b i (y i)

lemma factor_nonneg (b : ℝ) (i : Fin 3) (t : ℝ) : 0 ≤ factor b i t := by
  unfold factor
  split_ifs
  · exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  · exact (Real.exp_pos _).le

lemma weight_nonneg (b : ℝ) (y : Y) : 0 ≤ weight b y :=
  Finset.prod_nonneg (fun i _ => factor_nonneg b i (y i))

lemma measurable_factor (b : ℝ) (i : Fin 3) : Measurable (factor b i) := by
  unfold factor
  by_cases hi : i = 2
  · simp only [hi, ite_true]
    exact (by fun_prop : Measurable (fun s : ℝ => Real.exp (-b*s))).indicator measurableSet_Ioi
  · simp only [hi, ite_false]
    fun_prop

lemma measurable_weight (b : ℝ) : Measurable (weight b) := by
  unfold weight
  exact Finset.measurable_prod _ (fun i _ => (measurable_factor b i).comp (measurable_pi_apply i))

lemma integrable_factor_pow {b : ℝ} (hb : 0 < b) (i : Fin 3) (n : ℕ) :
    Integrable (fun t : ℝ => |t|^n * factor b i t) := by
  by_cases hi : i = 2
  · have h : IntegrableOn (fun t : ℝ => t^n * Real.exp (-b*t)) (Ioi 0) := by
      simpa only [Real.rpow_natCast, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1)
          (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hb)
    have h' : (fun t : ℝ => |t|^n * factor b i t) =
        (Ioi (0 : ℝ)).indicator (fun t => t^n * Real.exp (-b*t)) := by
      funext t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · simp [factor, hi, ht, abs_of_pos (mem_Ioi.mp ht)]
      · simp [factor, hi, ht]
    rw [h']
    exact h.integrable_indicator measurableSet_Ioi
  · have h : Integrable (fun t : ℝ => t^n * Real.exp (-b*t^2)) := by
      simpa only [Real.rpow_natCast] using
        (integrable_rpow_mul_exp_neg_mul_sq (s := (n : ℝ)) hb (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
    simpa only [factor, hi, ite_false, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using h.norm

lemma integrable_factor {b : ℝ} (hb : 0 < b) (i : Fin 3) : Integrable (factor b i) := by
  simpa using integrable_factor_pow hb i 0

lemma integrable_weight {b : ℝ} (hb : 0 < b) : Integrable (weight b) :=
  Integrable.fintype_prod (fun i => integrable_factor hb i)

lemma integrable_coordinate_moment {b : ℝ} (hb : 0 < b) (i : Fin 3) (n : ℕ) :
    Integrable (fun y : Y => |y i|^n * weight b y) := by
  let g : Fin 3 → ℝ → ℝ := fun j t => (if i=j then |t|^n else 1) * factor b j t
  have hg (j : Fin 3) : Integrable (g j) := by
    by_cases hij : i=j
    · simpa [g, hij] using integrable_factor_pow hb j n
    · simpa [g, hij] using integrable_factor hb j
  have h := Integrable.fintype_prod hg
  simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, ite_true] at h
  exact h

lemma norm_pow_le_sum (y : Y) (n : ℕ) : ‖y‖^n ≤ ∑ i, |y i|^n := by
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm y
  rw [← hi]
  exact Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (y j)) n) (Finset.mem_univ i)

/-- Every finite radial moment of the Gaussian-tangential, exponential-normal
profile is integrable over the full coordinate space (zero for t≤0). -/
theorem integrable_norm_moment {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun y : Y => ‖y‖^n * weight b y) := by
  have h := integrable_finsetSum Finset.univ (fun i _ => integrable_coordinate_moment hb i n)
  apply h.mono' ((continuous_norm.measurable.pow_const n).mul (measurable_weight b)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => by
    change ‖‖y‖^n * weight b y‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg y) n) (weight_nonneg b y)),
      ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (norm_pow_le_sum y n) (weight_nonneg b y))

end ElasticityBoundaryWeights

end
end

end OAI
