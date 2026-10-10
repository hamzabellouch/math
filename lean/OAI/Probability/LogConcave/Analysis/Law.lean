import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget
import OAI.Probability.LogConcave.Dynamics.DistanceCoupled

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal

variable {d : ℕ}

lemma measurable_iterate_map {T : Point d → Point d} (hT : Measurable T)
    (σ : ℝ) (n : ℕ) (x : Point d) :
    Measurable (fun g : PiLp 2 (fun _ : Fin n => Point d) => iterate T σ n x g.ofLp) := by
  have h (n : ℕ) : Measurable (iterate T σ n x) := by
    induction n with
    | zero => exact measurable_const
    | succ n ih =>
      exact (hT.comp (ih.comp (Measurable.of_eval (fun index => measurable_pi_apply index.castSucc)))).add
        ((measurable_pi_apply (Fin.last n)).const_smul σ)
  exact (h n).comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => Point d)).measurable

def law (T : Point d → Point d) (σ : ℝ) (n : ℕ) (x : Point d) : Measure (Point d) :=
  (stdGaussian (PiLp 2 (fun _ : Fin n => Point d))).map (fun g => iterate T σ n x g.ofLp)

lemma law_probability {T : Point d → Point d} (hT : Measurable T) (σ : ℝ) (n : ℕ) (x : Point d) :
    IsProbabilityMeasure (law T σ n x) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_iterate_map hT σ n x).aemeasurable).mpr inferInstance

theorem laws_tendsto (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → Point d → Point d} (hT : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ) (N : ℕ → ℕ)
    (hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0))
    {D : ℕ → ℝ} (hD : Tendsto (fun k => (N k:ℝ)*D k) atTop (𝓝 0))
    (hstep : ∀ k (f : Point d → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B →
      (∀ x, |f x| ≤ B) → |(∫ x, operator (T k) (σ k) f x ∂μ)-∫ x, f x ∂μ| ≤ B*D k)
    (x : Point d) :
    Tendsto (fun k => (⟨law (T k) (σ k) (N k) x,law_probability (hT k).continuous.measurable _ _ _⟩ : ProbabilityMeasure (Point d)))
      atTop (nhds (X := ProbabilityMeasure (Point d)) ⟨μ,inferInstance⟩) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hf hl
  obtain ⟨C,hC⟩ := hf
  obtain ⟨L,hL⟩ := hl
  have hb (z : Point d) : |f z|≤C+|f 0| := by
    have h := hC z 0
    rw [Real.dist_eq] at h
    have ha := abs_add_le (f z-f 0) (f 0)
    rw [sub_add_cancel] at ha
    linarith
  have hB : 0≤C+|f 0| := (abs_nonneg (f 0)).trans (hb 0)
  have ht := expectations_tendsto μ hT σ N hq hD hstep hL.uniformContinuous hB hb x
  convert ht using 1
  · funext k
    change (∫z,f z ∂law (T k) (σ k) (N k) x)=_
    rw [law,integral_map (measurable_iterate_map (hT k).continuous.measurable _ _ _).aemeasurable hL.continuous.aestronglyMeasurable]
    exact integral_iterate_gaussian (hT k).continuous.measurable (σ k) hL.continuous.measurable hb (N k) x
  · rfl

lemma comparison_iterate {T U : Point d → Point d} {R : ℝ} (hr : 0≤R)
    (hstep : ∀x y,dist x y≤R → dist (T x) (U y)≤R)
    (σ : ℝ) (n : ℕ) (x : Point d) (g : Fin n → Point d) :
    dist (iterate T σ n x g) (iterate U σ n x g)≤R := by
  induction n with
  | zero => simpa only [iterate,dist_self] using hr
  | succ n ih =>
    simp only [iterate,dist_add_right]
    exact hstep _ _ (ih _)

lemma laws_distanceCoupled {T U : Point d → Point d} (hT : Measurable T) (hU : Measurable U)
    {R : ℝ} (hr : 0≤R) (hstep : ∀x y,dist x y≤R → dist (T x) (U y)≤R)
    (σ : ℝ) (n : ℕ) (x : Point d) : Coupling.DistanceCoupled (law T σ n x) (law U σ n x) R := by
  let J := fun g : PiLp 2 (fun _ : Fin n => Point d) =>
    (iterate T σ n x g.ofLp,iterate U σ n x g.ofLp)
  have hm : Measurable J := (measurable_iterate_map hT _ _ _).prodMk (measurable_iterate_map hU _ _ _)
  refine ⟨(stdGaussian _).map J,inferInstance,?_,?_,?_⟩
  · change ((stdGaussian _).map J).map Prod.fst=_
    rw [Measure.map_map measurable_fst hm]
    rfl
  · change ((stdGaussian _).map J).map Prod.snd=_
    rw [Measure.map_map measurable_snd hm]
    rfl
  · apply ae_map_iff hm.aemeasurable (measurableSet_le (by fun_prop) measurable_const) |>.mpr
    exact Filter.Eventually.of_forall (fun g => comparison_iterate hr hstep σ n x g.ofLp)
end LogConcaveSampling.EulerGeometry

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter EulerGeometry
open scoped Topology Classical NNReal

variable {d : ℕ}

theorem gibbs_distanceCoupled_of_euler
    {H U : Point d → ℝ} (hH : ContDiff ℝ 2 H) (hU : ContDiff ℝ 2 U)
    {MH MU : ℝ≥0} (hMH : LipschitzWith MH (gradient H)) (hMU : LipschitzWith MU (gradient U))
    (hH0 : partition H ≠ 0) (hHt : partition H ≠ ⊤)
    (hU0 : partition U ≠ 0) (hUt : partition U ≠ ⊤)
    (hHi : Integrable (fun x => ‖gradient H x‖^2) (gibbs H))
    (hUi : Integrable (fun x => ‖gradient U x‖^2) (gibbs U))
    {m a B : ℝ} (hm : 0 < m) (ha : 0 < a) (hma : m*a≤1) (hB : 0 ≤ B)
    (hTH : ∀h,0 ≤ h → h ≤ a → ∀x y,dist (eulerDrift H h x) (eulerDrift H h y)≤(1-m*h)*dist x y)
    (hTU : ∀h,0 ≤ h → h ≤ a → ∀x y,dist (eulerDrift U h x) (eulerDrift U h y)≤(1-m*h)*dist x y)
    (hpert : ∀x,‖gradient H x-gradient U x‖≤B) :
    Coupling.DistanceCoupled (gibbs H) (gibbs U) (B/m) := by
  let := probability_gibbs_of_partition hH0 hHt
  let := probability_gibbs_of_partition hU0 hUt
  have hrate : Tendsto (fun s => EulerDefect.rate H s+EulerDefect.rate U s) (𝓝 0) (𝓝 0) := by
    simpa only [zero_add] using (EulerDefect.rate_tendsto hH hMH hHi).add (EulerDefect.rate_tendsto hU hMU hUi)
  obtain ⟨N,s,hs,hD⟩ := exists_consistent_schedule hrate
    (fun s => add_nonneg (EulerDefect.rate_nonneg H s) (EulerDefect.rate_nonneg U s)) ha
  have hq0 (k) : 0 ≤ 1-m*(s k)^2 := by
    have h := mul_le_mul_of_nonneg_left (hs k).2.2.1 hm.le
    linarith
  let q : ℕ → ℝ≥0 := fun k => ⟨1-m*(s k)^2,hq0 k⟩
  have hTL (k) : LipschitzWith (q k) (eulerDrift H ((s k)^2)) :=
    LipschitzWith.of_dist_le_mul (hTH _ (sq_nonneg _) (hs k).2.2.1)
  have hUL (k) : LipschitzWith (q k) (eulerDrift U ((s k)^2)) :=
    LipschitzWith.of_dist_le_mul (hTU _ (sq_nonneg _) (hs k).2.2.1)
  have hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0) :=
    schedule_contraction_tendsto hm N s hq0 (fun k => (hs k).2.2.2)
  have hDH : Tendsto (fun k => (N k:ℝ)*(2*(s k)^2*EulerDefect.rate H (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity [EulerDefect.rate_nonneg H (s k)]) _ hD
    intro k
    gcongr
    exact le_add_of_nonneg_right (EulerDefect.rate_nonneg U _)
  have hDU : Tendsto (fun k => (N k:ℝ)*(2*(s k)^2*EulerDefect.rate U (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by positivity [EulerDefect.rate_nonneg U (s k)]) _ hD
    intro k
    gcongr
    exact le_add_of_nonneg_left (EulerDefect.rate_nonneg H _)
  have hcH := laws_tendsto (gibbs H) hTL (fun k => Real.sqrt 2*s k) N hq hDH
    (fun k f hf B hB hb => euler_operator_gibbs_defect hH hMH hH0 hHt hHi
      (hs k).1.ne' (by rw [abs_of_pos (hs k).1]; exact (hs k).2.1) hf hB hb) 0
  have hcU := laws_tendsto (gibbs U) hUL (fun k => Real.sqrt 2*s k) N hq hDU
    (fun k f hf B hB hb => euler_operator_gibbs_defect hU hMU hU0 hUt hUi
      (hs k).1.ne' (by rw [abs_of_pos (hs k).1]; exact (hs k).2.1) hf hB hb) 0
  apply Coupling.distanceCoupled_of_tendsto hcH hcU
  intro k
  apply laws_distanceCoupled (hTL k).continuous.measurable (hUL k).continuous.measurable
    (div_nonneg hB hm.le)
  intro x y hxy
  have he : dist (eulerDrift H ((s k)^2) y) (eulerDrift U ((s k)^2) y)≤(s k)^2*B := by
    rw [eulerDrift,eulerDrift,dist_eq_norm,show y-(s k)^2 • gradient H y-(y-(s k)^2 • gradient U y) =
      -(s k)^2 • (gradient H y-gradient U y) by module,norm_smul,Real.norm_eq_abs,abs_neg,abs_sq]
    exact mul_le_mul_of_nonneg_left (hpert y) (sq_nonneg _)
  have ht := dist_triangle (eulerDrift H ((s k)^2) x) (eulerDrift H ((s k)^2) y)
    (eulerDrift U ((s k)^2) y)
  have hb := (hTL k).dist_le_mul x y
  have hmul := mul_le_mul_of_nonneg_left hxy (hq0 k)
  have hid : (1-m*(s k)^2)*(B/m)+(s k)^2*B=B/m := by field_simp; ring
  change _≤B/m
  change dist _ _≤(1-m*(s k)^2)*dist x y at hb
  linarith
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal RealInnerProductSpace

variable {d : ℕ}

lemma gradient_contDiff_one {H : Point d → ℝ} (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (gradient H) :=
  (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp (hH.fderiv_right (by norm_num))

lemma hessian_euler_contraction {H : Point d → ℝ} (hH : ContDiff ℝ 2 H)
    {m M s : ℝ} (_ : 0 < m) (hs : 0 ≤ s) (hsM : s*M ≤ 1)
    (hess : ∀x v : Point d,m*‖v‖^2 ≤ inner ℝ v (fderiv ℝ (gradient H) x v) ∧
      inner ℝ v (fderiv ℝ (gradient H) x v) ≤ M*‖v‖^2)
    (hsm : s*m ≤ 1) :
    LipschitzWith ⟨1-s*m,sub_nonneg.mpr hsm⟩ (eulerDrift H s) := by
  have hg := (gradient_contDiff_one hH).differentiable (by norm_num)
  have hd (x : Point d) : fderiv ℝ (eulerDrift H s) x=
      ContinuousLinearMap.id ℝ (Point d)-s • fderiv ℝ (gradient H) x :=
    ((hasFDerivAt_id x).sub ((hg x).hasFDerivAt.const_smul s)).fderiv
  apply lipschitzWith_of_nnnorm_fderiv_le (differentiable_id.sub (hg.const_smul s))
  intro x
  change ‖fderiv ℝ (eulerDrift H s) x‖ ≤ 1-s*m
  rw [hd]
  change ‖ContinuousLinearMap.id ℝ (Point d)-s • fderiv ℝ (gradient H) x‖ ≤ 1-s*m
  have hsym : (ContinuousLinearMap.id ℝ (Point d)-s • fderiv ℝ (gradient H) x).IsSymmetric := by
    intro v w
    change inner ℝ (v-s • fderiv ℝ (gradient H) x v) w=inner ℝ v (w-s • fderiv ℝ (gradient H) x w)
    simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
    have he : inner ℝ (fderiv ℝ (gradient H) x v) w=inner ℝ v (fderiv ℝ (gradient H) x w) :=
      (ContDiff.isSymmetric_gradient_derivative hH x) v w
    rw [he]
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hsym]
  apply ciSup_le
  intro v
  by_cases hv : v=0
  · simp [hv,sub_nonneg.mpr hsm]
  have hp : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  rw [ContinuousLinearMap.rayleighQuotient,ContinuousLinearMap.reApplyInnerSelf_apply,real_inner_comm]
  simp only [RCLike.re_to_real,sub_apply,ContinuousLinearMap.id_apply,
    smul_apply,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  have hn : 0 ≤ ‖v‖^2-s*inner ℝ v (fderiv ℝ (gradient H) x v) := by
    have hh := mul_le_mul_of_nonneg_left (hess x v).2 hs
    have hb := mul_le_mul_of_nonneg_right hsM hp.le
    nlinarith
  rw [abs_of_nonneg (div_nonneg hn hp.le),div_le_iff₀ hp]
  have hh := mul_le_mul_of_nonneg_left (hess x v).1 hs
  nlinarith

def posteriorPotential (V : Point d → ℝ) (h : ℝ) (y z : Point d) : ℝ :=
  V z+‖z-y‖^2/(2*h)

lemma posterior_smooth {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) (y : Point d) :
    ContDiff ℝ 2 (posteriorPotential V h y) :=
  hV.smooth.add (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _)

lemma posterior_gradient {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) (y z : Point d) :
    gradient (posteriorPotential V h y) z=gradient V z+h⁻¹ • (z-y) := by
  apply HasGradientAt.gradient
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have ha := (hasStrictFDerivAt_norm_sq (z-y)).hasFDerivAt.comp z
    ((hasFDerivAt_id z).sub (hasFDerivAt_const y z))
  have hd := (hV.smooth.differentiable (by norm_num) z).hasFDerivAt.add (ha.const_smul (2*h)⁻¹)
  convert! hd using 1
  · funext w
    simp only [posteriorPotential,Pi.add_apply,Pi.smul_apply,Function.comp_apply,Pi.sub_apply,id_eq,smul_eq_mul]
    ring
  ext v
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,sub_apply,ContinuousLinearMap.id_apply,
    map_sub,sub_zero,smul_eq_mul,innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply,inner_add_left,real_inner_smul_left,inner_sub_left,←toDual_gradient]
  ring

lemma posterior_hessian {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) (y z v : Point d) :
    fderiv ℝ (gradient (posteriorPotential V h y)) z v=fderiv ℝ (gradient V) z v+h⁻¹ • v := by
  have he : gradient (posteriorPotential V h y)=(fun z => gradient V z+h⁻¹ • (z-y)) :=
    funext (posterior_gradient hV h y)
  rw [he]
  have hd := (hV.contDiff_gradient.differentiable (by norm_num) z).hasFDerivAt.add
    (((hasFDerivAt_id z).sub (hasFDerivAt_const y z)).const_smul h⁻¹)
  change (fderiv ℝ (gradient V+h⁻¹ • (id-fun _ => y)) z) v=_
  rw [hd.fderiv]
  simp

lemma posterior_tail {V : Point d → ℝ} (hV : Admissible V) {h : ℝ} (hh : 0 < h) (y : Point d) :
    HasGaussianLowerTail (posteriorPotential V h y) := by
  refine ⟨1/2,by norm_num,0,fun z => ?_⟩
  dsimp [posteriorPotential]
  have hq := (hV.quadratic_bounds z).1
  have hn : 0 ≤ ‖z-y‖^2/(2*h) := by positivity
  linarith

lemma posterior_gradient_lipschitz {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0 < h) (y : Point d) :
    LipschitzWith ⟨2+h⁻¹,by positivity⟩ (gradient (posteriorPotential V h y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simp only [posterior_gradient hV h y]
  have hb := dist_add_add_le (gradient V x) (h⁻¹ • (x-y)) (gradient V z) (h⁻¹ • (z-y))
  simp only [dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),dist_sub_right] at hb
  have hg := hV.gradient_lipschitz.dist_le_mul x z
  change _ ≤ (2+h⁻¹)*dist x z
  norm_num at hg
  nlinarith

lemma norm_sq_growth_of_lipschitz {g : Point d → Point d} {L : ℝ≥0} (hg : LipschitzWith L g) :
    HasPolynomialGrowth (fun x => ‖g x‖^2) := by
  obtain ⟨C,hC,n,hb⟩ := growth_of_lipschitz hg
  refine ⟨2*C^2,by positivity,2*n,fun x => ?_⟩
  rw [Real.norm_eq_abs,abs_sq]
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
  have hr := sq_nonneg (1-‖x‖^n)
  rw [mul_comm 2 n,pow_mul]
  nlinarith [mul_nonneg (sq_nonneg C) hr]

lemma posterior_gradient_integrable {V : Point d → ℝ} (hV : Admissible V)
    {h : ℝ} (hh : 0 < h) (y : Point d) :
    Integrable (fun z => ‖gradient (posteriorPotential V h y) z‖^2) (gibbs (posteriorPotential V h y)) :=
  integrable_polynomial_gibbs (posterior_smooth hV h y).continuous (posterior_tail hV hh y)
    ((posterior_gradient_lipschitz hV hh y).continuous.norm.pow 2)
    (norm_sq_growth_of_lipschitz (posterior_gradient_lipschitz hV hh y))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical NNReal RealInnerProductSpace

variable {d : ℕ}

lemma posterior_euler_lipschitz {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0 < h) (y : Point d) {s : ℝ} (hs : 0 ≤ s) (hsM : s*(2+h⁻¹) ≤ 1) :
    ∀ x z, dist (eulerDrift (posteriorPotential V h y) s x)
      (eulerDrift (posteriorPotential V h y) s z) ≤ (1-(1+h⁻¹)*s)*dist x z := by
  have hsm : s*(1+h⁻¹) ≤ 1 := by nlinarith
  have he := hessian_euler_contraction (posterior_smooth hV h y)
    (by positivity : 0 < 1+h⁻¹) hs hsM (fun x v => ?_) hsm
  · intro x z
    have hb := he.dist_le_mul x z
    change dist _ _ ≤ (1-s*(1+h⁻¹))*dist x z at hb
    convert! hb using 1
    ring
  · rw [posterior_hessian hV h y,inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
    obtain ⟨hl,hu⟩ := hV.hessian_bounds x v
    constructor <;> nlinarith

theorem posterior_distanceCoupled {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0 < h) (y z : Point d) :
    Coupling.DistanceCoupled (gibbs (posteriorPotential V h y))
      (gibbs (posteriorPotential V h z)) (dist y z/(1+h)) := by
  have hM : 0 < 2+h⁻¹ := by positivity
  have hm : 0 < 1+h⁻¹ := by positivity
  have hma : (1+h⁻¹)*(2+h⁻¹)⁻¹ ≤ 1 := by
    rw [←div_eq_mul_inv,div_le_one hM]
    linarith
  have hstep (u : Point d) (s : ℝ) (hs : 0 ≤ s) (hsa : s ≤ (2+h⁻¹)⁻¹) :=
    posterior_euler_lipschitz hV hh u hs (by
      have hsc := mul_le_mul_of_nonneg_right hsa hM.le
      rw [inv_mul_cancel₀ hM.ne'] at hsc
      exact hsc)
  have hpert (x : Point d) :
      ‖gradient (posteriorPotential V h y) x-gradient (posteriorPotential V h z) x‖ ≤ h⁻¹*dist y z := by
    rw [posterior_gradient hV h y,posterior_gradient hV h z,
      show gradient V x+h⁻¹ • (x-y)-(gradient V x+h⁻¹ • (x-z))=h⁻¹ • (z-y) by module,
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hh),←dist_eq_norm,dist_comm z y]
  have he := gibbs_distanceCoupled_of_euler (posterior_smooth hV h y) (posterior_smooth hV h z)
    (posterior_gradient_lipschitz hV hh y) (posterior_gradient_lipschitz hV hh z)
    (partition_pos_of_continuous (posterior_smooth hV h y).continuous).ne'
    (partition_ne_top_of_integrable ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous))
    (partition_pos_of_continuous (posterior_smooth hV h z).continuous).ne'
    (partition_ne_top_of_integrable ((posterior_tail hV hh z).integrable_exp (posterior_smooth hV h z).continuous))
    (posterior_gradient_integrable hV hh y) (posterior_gradient_integrable hV hh z)
    hm (inv_pos.mpr hM) hma (mul_nonneg (inv_pos.mpr hh).le dist_nonneg)
    (hstep y) (hstep z) hpert
  have hid : h⁻¹*dist y z/(1+h⁻¹)=dist y z/(1+h) := by
    field_simp
    ring
  rwa [hid] at he

lemma posterior_squaredCoupled {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0 < h) (y z : Point d) :
    Coupling.SquaredAt (gibbs (posteriorPotential V h y))
      (gibbs (posteriorPotential V h z)) id id ((dist y z/(1+h))^2) :=
  (posterior_distanceCoupled hV hh y z).squared (div_nonneg dist_nonneg (by positivity))
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical ENNReal

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

lemma measurable_gibbs_family {H : A → Point d → ℝ}
    (hH : Measurable (uncurry H)) : Measurable (fun a => gibbs (H a)) := by
  have hw : Measurable (fun p : A × Point d => gibbsDensity (H p.1) p.2) := by
    unfold gibbsDensity
    exact (Real.measurable_exp.comp hH.neg).ennreal_ofReal
  have hp : Measurable (fun a => partition (H a)) := hw.lintegral_prod_right
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [gibbs,Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs]
  change Measurable (fun a => (partition (H a))⁻¹ * ∫⁻z in s,gibbsDensity (H a) z)
  exact hp.inv.mul (hw.lintegral_prod_right (ν:=volume.restrict s))

def gibbsKernel (H : A → Point d → ℝ) (hH : Measurable (uncurry H)) : Kernel A (Point d) where
  toFun a := gibbs (H a)
  measurable' := measurable_gibbs_family hH

lemma bounded_integrable {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsFiniteMeasure μ] {f : E → ℝ} (hf : Measurable f) {C : ℝ} (hb : ∀x,|f x|≤C) :
    Integrable f μ := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

lemma bounded_integral {E : Type*} [MeasurableSpace E] {μ : Measure E}
    [IsProbabilityMeasure μ] {f : E → ℝ} {C : ℝ} (_ : 0≤C) (hb : ∀x,|f x|≤C) :
    |∫x,f x ∂μ|≤C := by
  rw [←Real.norm_eq_abs]
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
    (fun x => by simpa only [Real.norm_eq_abs] using hb x))).trans (by simp)

lemma gibbs_family_integral_measurable {H : A → Point d → ℝ}
    (hH : Measurable (uncurry H)) {f : Point d → ℝ} (hf : Measurable f) :
    Measurable (fun a => ∫z,f z ∂gibbs (H a)) :=
  (hf.stronglyMeasurable.integral_kernel (κ:=gibbsKernel H hH)).measurable

def posteriorKernel (V : Point d → ℝ) (hV : Admissible V) (h : ℝ) : Kernel (Point d) (Point d) :=
  gibbsKernel (posteriorPotential V h) (by
    have hm := hV.smooth.continuous.measurable
    unfold uncurry posteriorPotential
    fun_prop)

lemma posteriorKernel_probability {V : Point d → ℝ} (hV : Admissible V) {h : ℝ}
    (hh : 0<h) : IsMarkovKernel (posteriorKernel V hV h) := by
  constructor
  intro y
  exact probability_gibbs_of_partition (partition_pos_of_continuous (posterior_smooth hV h y).continuous).ne'
    (partition_ne_top_of_integrable ((posterior_tail hV hh y).integrable_exp (posterior_smooth hV h y).continuous))

def jointPosteriorLaw (V : Point d → ℝ) (h : ℝ) : Measure (Point d × Point d) :=
  ((gibbs V).prod (stdGaussian (Point d))).map (fun p => (p.1,p.1+Real.sqrt h • p.2))

def noisedLaw (V : Point d → ℝ) (h : ℝ) : Measure (Point d) :=
  ((gibbs V).prod (stdGaussian (Point d))).map (fun p => p.1+Real.sqrt h • p.2)

lemma noisedLaw_probability {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) :
    IsProbabilityMeasure (noisedLaw V h) := by
  let := hV.isProbabilityMeasure_gibbs
  unfold noisedLaw
  infer_instance

lemma jointPosteriorLaw_probability {V : Point d → ℝ} (hV : Admissible V) (h : ℝ) :
    IsProbabilityMeasure (jointPosteriorLaw V h) := by
  let := hV.isProbabilityMeasure_gibbs
  unfold jointPosteriorLaw
  infer_instance

lemma jointPosterior_fst {V : Point d → ℝ} (h : ℝ) :
    (jointPosteriorLaw V h).map Prod.fst=gibbs V := by
  rw [jointPosteriorLaw,Measure.map_map measurable_fst (by fun_prop)]
  simpa only [Function.comp_def,measure_univ,one_smul] using
    (Measure.map_fst_prod (μ:=gibbs V) (ν:=stdGaussian (Point d)))

lemma jointPosterior_snd {V : Point d → ℝ} (h : ℝ) :
    (jointPosteriorLaw V h).map Prod.snd=noisedLaw V h := by
  rw [jointPosteriorLaw,Measure.map_map measurable_snd (by fun_prop)]
  rfl

end LogConcaveSampling

end

end

end OAI
