import OAI.Analysis.Steinitz.HeatL2

namespace OAI

/-! Gaussian heat kernels and autoregressive path laws. -/

section

open MeasureTheory ProbabilityTheory WithLp
open scoped NNReal ENNReal RealInnerProductSpace
namespace GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scaleMap_selfAdjoint (v : ι → ℝ≥0) : IsSelfAdjoint (scaleMap v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  change y i * (scaleMap v x) i = (scaleMap v y) i * x i
  rw [scaleMap_apply, scaleMap_apply]
  ring

noncomputable def symbol (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) : ℝ :=
  (∑ i, (v i : ℝ)*(2*Real.pi*ξ i)^2)/2

lemma symbol_eq (v : ι → ℝ≥0) : HeatL2.gaussianSymbol (scaleMap v) = symbol v := by
  ext ξ
  rw [HeatL2.gaussianSymbol, (scaleMap_selfAdjoint v).adjoint_eq,
    EuclideanSpace.real_norm_sq_eq]
  unfold symbol
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [PiLp.smul_apply, smul_eq_mul, scaleMap_apply, mul_pow,
    Real.sq_sqrt (v i).coe_nonneg]
  ring

omit [DecidableEq ι] in
lemma symbol_continuous (v : ι → ℝ≥0) : Continuous (symbol v) := by
  unfold symbol
  fun_prop

omit [DecidableEq ι] in
lemma symbol_nonneg (v : ι → ℝ≥0) (ξ : EuclideanSpace ℝ ι) : 0 ≤ symbol v ξ := by
  unfold symbol
  positivity

lemma average_diagonal_eq (v : ι → ℝ≥0) :
    HeatL2.average (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (diagonalLaw v) =
      HeatL2.average (scaleMap v) (stdGaussian (EuclideanSpace ℝ ι)) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [HeatL2.average_apply, HeatL2.average_apply, ← stdGaussian_map_scale v]
  change (∫ z, HeatL2.translate z f ∂(stdGaussian (EuclideanSpace ℝ ι)).map (scaleMap v)) = _
  exact integral_map (scaleMap v).measurable.aemeasurable
    (HeatL2.translate_continuous f).aestronglyMeasurable

lemma average_diagonal_heat (v : ι → ℝ≥0) :
    HeatL2.average (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) (diagonalLaw v) =
      HeatL2.heat (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v) := by
  rw [average_diagonal_eq, HeatL2.average_gaussian_eq_heat]
  congr 1
  exact symbol_eq v

noncomputable def kernel (v : ι → ℝ≥0) : HeatL2.BoundedKernel (EuclideanSpace ℝ ι) :=
  HeatL2.densityKernel (density v) (density_continuous v).measurable (density_nonneg v) (density_le_zero v)

omit [DecidableEq ι] in
lemma kernel_symmetric (v : ι → ℝ≥0) (x y : EuclideanSpace ℝ ι) :
    (kernel v).value (x,y) = (kernel v).value (y,x) := by
  change density v (y-x) = density v (x-y)
  rw [← neg_sub y x, density_neg]

lemma kernel_norm_eq (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)] :
    ‖HeatL2.kernelOp (μ := volume.restrict D) (kernel v)‖ =
      ‖HeatL2.compressedHeat D hD (symbol v) (symbol_continuous v).aestronglyMeasurable (symbol_nonneg v)‖ := by
  unfold kernel
  rw [← HeatL2.compressedAverage_kernel_norm D hD (diagonalLaw v) (density v)
    (density_continuous v).measurable (density_nonneg v) (density_le_zero v)
    (diagonalLaw_density v hv), average_diagonal_heat]
  rfl

end GaussianKernel

open MeasureTheory ProbabilityTheory Set WithLp
open scoped NNReal ENNReal
namespace GaussianKernel

lemma gaussianPDF_logconcave {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (x y : ℝ) :
    gaussianPDFReal 0 v x ^ (1-t) * gaussianPDFReal 0 v y ^ t ≤
      gaussianPDFReal 0 v ((1-t)*x+t*y) := by
  have hvp : (0:ℝ)<v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hc : 0 < (Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹ := by positivity
  simp only [gaussianPDFReal, sub_zero]
  rw [Real.mul_rpow hc.le (Real.exp_pos _).le,
    Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul, ← Real.exp_mul]
  calc
    _ = (((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹)^(1-t) *
        ((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹)^t) *
        Real.exp ((-(x^2)/(2*(v:ℝ)))*(1-t)+ (-(y^2)/(2*(v:ℝ)))*t) := by
      rw [Real.exp_add]; ring
    _ = ((Real.sqrt (2 * Real.pi * (v:ℝ)))⁻¹) *
        Real.exp ((-(x^2)/(2*(v:ℝ)))*(1-t)+ (-(y^2)/(2*(v:ℝ)))*t) := by
      rw [← Real.rpow_add hc, sub_add_cancel, Real.rpow_one]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le
      have hq : ((1-t)*x+t*y)^2 ≤ (1-t)*x^2+t*y^2 := by
        nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (x-y))]
      have : -( (1-t)*x^2+t*y^2)/(2*(v:ℝ)) ≤ -(((1-t)*x+t*y)^2)/(2*(v:ℝ)) :=
        div_le_div_of_nonneg_right (neg_le_neg hq) (by positivity)
      convert this using 1; ring

variable {ι : Type*} [Fintype ι]
lemma density_logconcave (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (x y : EuclideanSpace ℝ ι) :
    density v x ^ (1-t) * density v y ^ t ≤ density v ((1-t) • x + t • y) := by
  unfold density
  rw [← Real.finsetProd_rpow _ _ (fun i _ => gaussianPDFReal_nonneg 0 (v i) (x i)),
    ← Real.finsetProd_rpow _ _ (fun i _ => gaussianPDFReal_nonneg 0 (v i) (y i)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _)
      (Real.rpow_nonneg (gaussianPDFReal_nonneg _ _ _) _)
  · intro i _
    exact gaussianPDF_logconcave (hv i) ht (x i) (y i)

end GaussianKernel

end

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2

lemma integral_pi_fin_cons {X G : Type*} [MeasurableSpace X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (μ : Measure X) [SigmaFinite μ]
    {n : ℕ} {f : (Fin (n+1) → X) → G} (hf : Integrable f (Measure.pi fun _ => μ)) :
    (∫ p, f p ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ x, ∫ p, f (Fin.cons x p) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0
  have he : ∀ z : X × (Fin n → X), e.symm z = Fin.cons z.1 z.2 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e]
    · simp [e]
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm
  have hi : Integrable (fun z : X × (Fin n → X) => f (e.symm z)) (μ.prod (Measure.pi fun _ => μ)) :=
    hp.integrable_comp_of_integrable hf
  rw [← hp.integral_comp e.symm.measurableEmbedding f]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => integral_congr_ae
    (Filter.Eventually.of_forall fun p => congrArg f (he (x,p)))

section Chain
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)
noncomputable def tailWeight : (n : ℕ) → X → (Fin n → X) → ℝ
  | 0, _, _ => 1
  | n+1, x, p => k.value (x,p 0) * tailWeight n (p 0) (fun i => p i.succ)

lemma tailWeight_measurable (n : ℕ) : Measurable (fun z : X × (Fin n → X) => tailWeight k n z.1 z.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n hn =>
    exact (k.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).mul
      (hn.comp (((measurable_pi_apply 0).comp measurable_snd).prodMk
        (Measurable.of_eval fun (i : Fin n) => (measurable_pi_apply i.succ).comp measurable_snd)))

lemma tailWeight_nonneg (n : ℕ) (x : X) (p : Fin n → X) : 0 ≤ tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n hn => exact mul_nonneg (k.nonneg _) (hn _ _)

lemma tailWeight_le (n : ℕ) (x : X) (p : Fin n → X) : tailWeight k n x p ≤ k.bound^n := by
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n hn =>
    rw [tailWeight, pow_succ']
    exact mul_le_mul (k.le_bound _) (hn _ _) (tailWeight_nonneg k n _ _) k.bound_nonneg

lemma tailWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    Integrable (tailWeight k n x) (Measure.pi fun _ : Fin n => μ) := by
  apply Integrable.mono' (integrable_const (k.bound^n))
    ((tailWeight_measurable k n).comp measurable_prodMk_left).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖tailWeight k n x p‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg k n x p)]
    exact tailWeight_le k n x p

noncomputable def walk (μ : Measure X) (n : ℕ) (x : X) : ℝ :=
  ∫ p, tailWeight k n x p ∂Measure.pi (fun _ : Fin n => μ)

lemma walk_zero (μ : Measure X) (x : X) : walk k μ 0 x = 1 := by
  simp [walk,tailWeight, Measure.real]

lemma walk_succ {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    walk k μ (n+1) x = ∫ y, k.value (x,y) * walk k μ n y ∂μ := by
  rw [walk, integral_pi_fin_cons μ (tailWeight_integrable k (n+1) x)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun y => ?_
  simp only [tailWeight, Fin.cons_zero, Fin.cons_succ]
  rw [integral_const_mul]
  rfl

lemma walk_measurable {μ : Measure X} [SigmaFinite μ] (n : ℕ) : Measurable (walk k μ n) := by
  exact (tailWeight_measurable k n).stronglyMeasurable.integral_prod_right.measurable

lemma walk_nonneg (μ : Measure X) (n : ℕ) (x : X) : 0 ≤ walk k μ n x :=
  integral_nonneg (fun p => tailWeight_nonneg k n x p)

lemma walk_le {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) (x : X) :
    walk k μ n x ≤ (Measure.pi (fun _ : Fin n => μ)).real univ * k.bound^n := by
  change (∫ p, tailWeight k n x p ∂Measure.pi (fun _ : Fin n => μ)) ≤ _
  change _ ≤ (Measure.pi (fun _ : Fin n => μ)).real univ • (k.bound^n)
  rw [← integral_const]
  exact integral_mono (tailWeight_integrable k n x) (integrable_const _) (tailWeight_le k n x)

lemma kernel_pow_one_coe {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    ((kernelOp (μ := μ) k ^ n) (oneLp : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] fun x => (walk k μ n x : ℂ) := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, walk_zero, Complex.ofReal_one] using oneLp_coe (μ := μ)
  | succ n hn =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [kernelOp_coe k ((kernelOp k ^ n) oneLp)] with x hx
    rw [hx, kernelFun, walk_succ]
    calc
      _ = ∫ y, ((k.value (x,y) * walk k μ n y : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hn] with y hy
        rw [hy, Complex.ofReal_mul]
      _ = _ := integral_complex_ofReal

noncomputable def chainWeight (n : ℕ) (p : Fin (n+1) → X) : ℝ :=
  tailWeight k n (p 0) (fun i => p i.succ)

lemma chainWeight_measurable (n : ℕ) : Measurable (chainWeight k n) := by
  let f : (Fin (n+1) → X) → X × (Fin n → X) := fun p => (p 0, fun i => p i.succ)
  have hf : Measurable f := by
    exact (measurable_pi_apply 0).prodMk
      (Measurable.of_eval fun (i : Fin n) => measurable_pi_apply i.succ)
  exact (tailWeight_measurable k n).comp hf

lemma chainWeight_integrable {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (chainWeight k n) (Measure.pi fun _ : Fin (n+1) => μ) := by
  apply Integrable.mono' (integrable_const (k.bound^n)) (chainWeight_measurable k n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖tailWeight k n (p 0) (fun i => p i.succ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg k n _ _)]
    exact tailWeight_le k n _ _

lemma pathMass_pi {μ : Measure X} [IsFiniteMeasure μ] (n : ℕ) :
    pathMass (μ := μ) k n = ∫ p, chainWeight k n p ∂Measure.pi (fun _ : Fin (n+1) => μ) := by
  rw [pathMass_eq_integral, integral_pi_fin_cons μ (chainWeight_integrable k n)]
  apply integral_congr_ae
  filter_upwards [kernel_pow_one_coe k n] with x hx
  rw [hx,Complex.ofReal_re]
  simp only [chainWeight,Fin.cons_zero,Fin.cons_succ]
  rfl

end Chain
end HeatL2

open MeasureTheory Set
namespace HeatL2
section ChainContinuity
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable (k : BoundedKernel X) (hc : Continuous k.value)
include hc
lemma tailWeight_continuous (n : ℕ) : Continuous (fun z : X × (Fin n → X) => tailWeight k n z.1 z.2) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun z : X × (Fin (n+1) → X) =>
      k.value (z.1,z.2 0) * tailWeight k n (z.2 0) (fun i => z.2 i.succ))
    apply Continuous.mul
    · exact hc.comp (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd))
    · exact ih.comp (((continuous_apply 0).comp continuous_snd).prodMk
        (continuous_pi (fun (i : Fin n) => (continuous_apply i.succ).comp continuous_snd)))

lemma chainWeight_continuous (n : ℕ) : Continuous (chainWeight k n) := by
  let f : (Fin (n+1) → X) → X × (Fin n → X) := fun p => (p 0, fun i => p i.succ)
  have hf : Continuous f := by fun_prop
  exact (tailWeight_continuous k hc n).comp hf
end ChainContinuity
section ChainPos
variable {X : Type*} [MeasurableSpace X] (k : BoundedKernel X)
lemma tailWeight_pos (hp : ∀ z, 0 < k.value z) (n : ℕ) (x : X) (p : Fin n → X) :
    0 < tailWeight k n x p := by
  induction n generalizing x with
  | zero => exact zero_lt_one
  | succ n ih => exact mul_pos (hp _) (ih _ _)
end ChainPos
section ChainConcavity
variable {X : Type*} [MeasurableSpace X] [AddCommGroup X] [Module ℝ X]
variable (k : BoundedKernel X) {t : ℝ}
variable (hl : ∀ x y : X × X, k.value x^(1-t) * k.value y^t ≤ k.value ((1-t)•x+t•y))
include hl
lemma tailWeight_logconcave (n : ℕ) (x y : X) (p q : Fin n → X) :
    tailWeight k n x p^(1-t) * tailWeight k n y q^t ≤
      tailWeight k n ((1-t)•x+t•y) ((1-t)•p+t•q) := by
  induction n generalizing x y with
  | zero => simp [tailWeight]
  | succ n ih =>
    simp only [tailWeight, Pi.add_apply, Pi.smul_apply]
    rw [Real.mul_rpow (k.nonneg _) (tailWeight_nonneg k n _ _),
      Real.mul_rpow (k.nonneg _) (tailWeight_nonneg k n _ _)]
    calc
      _ = (k.value (x,p 0)^(1-t) * k.value (y,q 0)^t) *
          (tailWeight k n (p 0) (fun i => p i.succ)^(1-t) *
            tailWeight k n (q 0) (fun i => q i.succ)^t) := by ring
      _ ≤ _ := mul_le_mul (hl (x,p 0) (y,q 0)) (ih _ _ _ _)
        (mul_nonneg (Real.rpow_nonneg (tailWeight_nonneg k n _ _) _)
          (Real.rpow_nonneg (tailWeight_nonneg k n _ _) _)) (k.nonneg _)

lemma chainWeight_logconcave (n : ℕ) (p q : Fin (n+1) → X) :
    chainWeight k n p^(1-t) * chainWeight k n q^t ≤ chainWeight k n ((1-t)•p+t•q) :=
  tailWeight_logconcave k hl n (p 0) (q 0) (fun i => p i.succ) (fun i => q i.succ)
end ChainConcavity
end HeatL2

end

section

open MeasureTheory
namespace HeatL2
variable {X : Type*} [MeasurableSpace X]

lemma chainWeight_prod (k : BoundedKernel X) (n : ℕ) (p : Fin (n+1) → X) :
    chainWeight k n p = ∏ t : Fin n,k.value (p t.castSucc,p t.succ) := by
  induction n with
  | zero => simp [chainWeight,tailWeight]
  | succ n ih =>
    change k.value (p 0,p (Fin.succ 0))*chainWeight k n (fun t => p t.succ)=_
    rw [ih,Fin.prod_univ_succ]
    congr 1

lemma fin_sum_differences {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ t : Fin n,(f t.castSucc-f t.succ))=f 0-f (Fin.last n) := by
  rw [Finset.sum_sub_distrib]
  have ha := Fin.sum_univ_castSucc f
  have hb := Fin.sum_univ_succ f
  linarith

end HeatL2

end

section

open MeasureTheory WithLp Set
namespace GaussianAR

lemma measurePreserving_curry (T I : Type*) [Fintype T] [Fintype I] :
    MeasurePreserving (MeasurableEquiv.curry T I ℝ) := by
  apply MeasurePreserving.symm (MeasurableEquiv.curry T I ℝ).symm
  refine ⟨(MeasurableEquiv.curry T I ℝ).symm.measurable,?_⟩
  rw [volume_pi]
  apply (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.curry T I ℝ).symm.measurable (MeasurableSet.univ_pi hs)]
  have he : (MeasurableEquiv.curry T I ℝ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun t => Set.univ.pi (fun i => s (t,i))) := by ext x; simp
  rw [he,volume_pi,Measure.pi_pi]
  simp only [Measure.pi_pi,Fintype.prod_prod_type]

noncomputable def unpack (T I : Type*) [Fintype T] [Fintype I] :
    EuclideanSpace ℝ (T×I) ≃ᵐ (T → EuclideanSpace ℝ I) :=
  (MeasurableEquiv.toLp 2 (T×I → ℝ)).symm.trans ((MeasurableEquiv.curry T I ℝ).trans
    (MeasurableEquiv.piCongrRight (fun _ : T => (MeasurableEquiv.toLp 2 (I → ℝ)))))

lemma unpack_apply {T I : Type*} [Fintype T] [Fintype I]
    (x : EuclideanSpace ℝ (T×I)) (t : T) (i : I) : unpack T I x t i=x (t,i) := rfl

lemma unpack_preserving (T I : Type*) [Fintype T] [Fintype I] :
    MeasurePreserving (unpack T I) := by
  have hp : MeasurePreserving (MeasurableEquiv.piCongrRight
      (fun _ : T => MeasurableEquiv.toLp 2 (I → ℝ))) := by
    refine ⟨(MeasurableEquiv.piCongrRight (fun _ : T => MeasurableEquiv.toLp 2 (I → ℝ))).measurable,?_⟩
    change (volume : Measure (T → I → ℝ)).map (fun x t => toLp 2 (x t)) =
      (volume : Measure (T → EuclideanSpace ℝ I))
    let : SigmaFinite ((volume : Measure (I → ℝ)).map (toLp 2)) := by
      rw [(PiLp.volume_preserving_toLp I).map_eq]
      infer_instance
    rw [volume_pi,Measure.pi_map_pi (fun _ => (PiLp.volume_preserving_toLp I).measurable.aemeasurable)]
    simp only [(PiLp.volume_preserving_toLp I).map_eq,← volume_pi]
  exact hp.comp ((measurePreserving_curry T I).comp (PiLp.volume_preserving_ofLp (T×I)))

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory WithLp
open scoped RealInnerProductSpace ENNReal NNReal BigOperators
namespace GaussianAR
open GaussianKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def transition (r : ι → ℝ) (x y : EuclideanSpace ℝ ι) : ℝ :=
  ∏ i,(Real.sqrt (1-(r i)^2))⁻¹*gaussianPDFReal 0 1 ((y i-r i*x i)/Real.sqrt (1-(r i)^2))

omit [DecidableEq ι] in
lemma transition_nonneg (r : ι → ℝ) (x y : EuclideanSpace ℝ ι) : 0≤transition r x y := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg _ _ _)

omit [DecidableEq ι] in
lemma transition_le (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i) (x y : EuclideanSpace ℝ ι) :
    transition r x y ≤ (∏ i,(Real.sqrt (r i))⁻¹)*density w (y-x)*
      Real.exp ((‖x‖^2-‖y‖^2)/4) := by
  calc
    _ ≤ ∏ i, (Real.sqrt (r i))⁻¹ * gaussianPDFReal 0 (w i) (y i-x i) *
        Real.exp (((x i)^2-(y i)^2)/4) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (gaussianPDFReal_nonneg _ _ _)
      · intro i _
        exact transition_scalar (hr i) (hr1 i) (hw i) (w i).coe_nonneg (x i) (y i)
    _ = _ := by
      simp only [Finset.prod_mul_distrib,density,PiLp.sub_apply,← Real.exp_sum,
        ← Finset.sum_div,Finset.sum_sub_distrib,EuclideanSpace.real_norm_sq_eq]

lemma path_density_eq (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i<1) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    |(pathEquiv r hr hr1 n).symm.toContinuousLinearMap.det| *
      density (fun _ => 1) ((pathEquiv r hr hr1 n).symm x) =
    density (fun _ => 1) (unpack (Fin (n+1)) ι x 0) *
      ∏ t : Fin n,transition r (unpack (Fin (n+1)) ι x t.castSucc) (unpack (Fin (n+1)) ι x t.succ) := by
  have hd : (pathEquiv r hr hr1 n).symm.toContinuousLinearMap.det =
      ((∏ i,Real.sqrt (1-(r i)^2))^n)⁻¹ := by
    change (pathEquiv r hr hr1 n).toLinearEquiv.symm.toLinearMap.det=_
    rw [LinearEquiv.det_coe_symm]
    exact congrArg Inv.inv (pathEquiv_det r hr hr1 n)
  rw [hd,abs_of_nonneg (by positivity)]
  simp only [density,Fintype.prod_prod_type,Fin.prod_univ_succ,pathEquiv_symm_initial,
    pathEquiv_symm_step,transition,unpack_apply,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Finset.prod_inv_distrib,← inv_pow]
  ring

lemma path_density_le (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1)×ι)) :
    |(pathEquiv r (fun i => (hr i).le) hr1 n).symm.toContinuousLinearMap.det| *
      density (fun _ => 1) ((pathEquiv r (fun i => (hr i).le) hr1 n).symm x) ≤
    density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
      HeatL2.chainWeight (kernel w) n (unpack (Fin (n+1)) ι x) := by
  let p := unpack (Fin (n+1)) ι x
  rw [path_density_eq]
  change density (fun _ => 1) (p 0)*(∏ t : Fin n,transition r (p t.castSucc) (p t.succ))≤_
  have hp := Finset.prod_le_prod₀ (fun (t : Fin n) (_ : t∈Finset.univ) => transition_nonneg r (p t.castSucc) (p t.succ))
    (fun (t : Fin n) (_ : t∈Finset.univ) => transition_le r hr hr1 w hw (p t.castSucc) (p t.succ))
  apply (mul_le_mul_of_nonneg_left hp (density_nonneg _ _)).trans
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,← Real.exp_sum,
    ← Finset.sum_div]
  rw [HeatL2.fin_sum_differences (fun t => ‖p t‖^2)]
  have hchain : (∏ t : Fin n,density w (p t.succ-p t.castSucc))=HeatL2.chainWeight (kernel w) n p := by
    rw [HeatL2.chainWeight_prod]; rfl
  rw [hchain,density_exp]
  have he : Real.exp (-(∑ i,(p 0 i)^2/(2*(1:ℝ≥0)))) *
      Real.exp ((‖p 0‖^2-‖p (Fin.last n)‖^2)/4) ≤ 1 := by
    rw [← Real.exp_add,Real.exp_le_one_iff]
    simp only [NNReal.coe_one,mul_one,← Finset.sum_div,← EuclideanSpace.real_norm_sq_eq]
    nlinarith [sq_nonneg ‖p 0‖,sq_nonneg ‖p (Fin.last n)‖]
  have hn : 0 ≤ density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
      HeatL2.chainWeight (kernel w) n p := by
    exact mul_nonneg (mul_nonneg (density_nonneg _ _) (by positivity)) (HeatL2.tailWeight_nonneg _ _ _ _)
  nlinarith [mul_le_mul_of_nonneg_left he hn]

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal BigOperators
namespace GaussianAR
open GaussianKernel HeatL2 GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma survival_le_pathMass (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)]
    (n : ℕ) :
    (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
      {x | ∀ t : Fin (n+1), matrixMap (evaluation r n t) x ∈ D} ≤
      density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
        pathMass (μ := volume.restrict D) (kernel w) n := by
  let P : Set (Fin (n+1) → EuclideanSpace ℝ ι) := univ.pi (fun _ => D)
  let S := (unpack (Fin (n+1)) ι) ⁻¹' P
  let e := pathEquiv r (fun i => (hr i).le) hr1 n
  have hP : MeasurableSet P := MeasurableSet.univ_pi (fun _ => hD)
  have hS : MeasurableSet S := hP.preimage (unpack (Fin (n+1)) ι).measurable
  have heq : e ⁻¹' S = {x | ∀ t : Fin (n+1),matrixMap (evaluation r n t) x ∈ D} := by
    ext x
    change (∀ t ∈ univ,unpack (Fin (n+1)) ι (e x) t ∈ D) ↔ _
    have he (t : Fin (n+1)) : unpack (Fin (n+1)) ι (e x) t = matrixMap (evaluation r n t) x := by
      ext i
      rw [unpack_apply,pathEquiv_apply,pathMatrix_apply]
    simp only [he,mem_univ,forall_const,mem_ofPred_eq]
  have hprob : (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
      {x | ∀ t : Fin (n+1),matrixMap (evaluation r n t) x ∈ D} =
      ∫ x in S, |e.symm.toContinuousLinearMap.det| *density (fun _ => 1) (e.symm x) := by
    rw [Measure.real,← heq,← Measure.map_apply e.continuous.measurable hS,
      linear_image_density e hS,ENNReal.toReal_ofReal]
    exact integral_nonneg (fun x => mul_nonneg (abs_nonneg _) (density_nonneg _ _))
  have hchain : Integrable (chainWeight (kernel w) n) (volume.restrict P) := by
    simpa only [P,volume_pi,Measure.restrict_pi_pi] using
      (chainWeight_integrable (kernel w) (μ := volume.restrict D) n)
  have hic : Integrable (fun x => chainWeight (kernel w) n (unpack (Fin (n+1)) ι x)) (volume.restrict S) :=
    ((unpack_preserving (Fin (n+1)) ι).restrict_preimage_emb
      (unpack (Fin (n+1)) ι).measurableEmbedding P).integrable_comp_of_integrable hchain
  rw [hprob]
  calc
    _ ≤ ∫ x in S, density (fun _ : ι => 1) 0 * (∏ i,(Real.sqrt (r i))⁻¹)^n *
        chainWeight (kernel w) n (unpack (Fin (n+1)) ι x) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (density_nonneg _ _))
        (hic.const_mul _)
      exact Filter.Eventually.of_forall (path_density_le r hr hr1 w hw n)
    _ = _ := by
      rw [integral_const_mul,(unpack_preserving (Fin (n+1)) ι).setIntegral_preimage_emb
        (unpack (Fin (n+1)) ι).measurableEmbedding]
      congr 1
      simp only [P,volume_pi,Measure.restrict_pi_pi,pathMass_pi]

lemma kernel_norm_of_survival (r : ι → ℝ) (hr : ∀ i,0<r i) (hr1 : ∀ i,r i<1)
    (w : ι → ℝ≥0) (hw : ∀ i,(w i:ℝ)=(1-(r i)^2)/r i)
    (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)]
    (a b : ℝ) (hs : ∀ n : ℕ, Real.exp (-a-b*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1), matrixMap (evaluation r n t) x ∈ D}) :
    Real.exp (-b) / (∏ i,(Real.sqrt (r i))⁻¹) ≤
      ‖kernelOp (μ := volume.restrict D) (kernel w)‖ := by
  have hρ : 0 < density (fun _ : ι => 1) 0 := density_pos _ (fun _ => by simp) _
  have hc : 0 < ∏ i,(Real.sqrt (r i))⁻¹ := Finset.prod_pos fun i _ =>
    inv_pos.mpr (Real.sqrt_pos.mpr (hr i))
  apply norm_lower_of_pathMass_lower (kernel w) (by positivity) (c := Real.exp (-a)/density (fun _ : ι => 1) 0) (by positivity)
  intro n
  have hn := (hs n).trans (survival_le_pathMass r hr hr1 w hw D hD n)
  have hex : Real.exp (-a-b*n)=Real.exp (-a)*(Real.exp (-b))^n := by
    rw [show -a-b*(n:ℝ)= -a+(-b)*n by ring,Real.exp_add,mul_comm (-b),Real.exp_nat_mul]
  rw [hex] at hn
  apply (mul_le_mul_iff_left₀ (mul_pos hρ (pow_pos hc n))).mp
  convert hn using 1
  · calc
      _ = (Real.exp (-a)/density (fun _ : ι => 1) 0 * density (fun _ : ι => 1) 0) *
          ((Real.exp (-b))^n/(∏ i,(Real.sqrt (r i))⁻¹)^n * (∏ i,(Real.sqrt (r i))⁻¹)^n) := by
        rw [div_pow]; ring
      _ = _ := by rw [div_mul_cancel₀ _ hρ.ne',div_mul_cancel₀ _ (pow_ne_zero n hc.ne')]
  · ring

end GaussianAR

end

end OAI
