import Mathlib
import OAI.Probability.SKFluctuations.ScalarFullOriginMarginality

namespace OAI

/-! Gaussian Small Scale. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem gaussianReal_sqrt_rescale {s : ℝ} (hs : 0 ≤ s) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt s*x)=gaussianReal 0 (Real.toNNReal s) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · exact mul_zero _
  · apply NNReal.eq
    change (Real.sqrt s)^2*1=↑(Real.toNNReal s)
    rw [mul_one,Real.sq_sqrt hs,Real.coe_toNNReal _ hs]

theorem gaussianKernel_integral_rescale {s : ℝ} (hs : 0 < s)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ x, realGaussianKernel s x*f x)=
      ∫ x, f (Real.sqrt s*x) ∂gaussianReal 0 1 := by
  change (∫ x, gaussianPDFReal 0 (Real.toNNReal s) x • f x)=_
  rw [← integral_gaussianReal_eq_integral_smul (Real.toNNReal_pos.mpr hs).ne']
  rw [← gaussianReal_sqrt_rescale hs.le]
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem gaussianStandard_sq_integral : (∫ x : ℝ, x^2 ∂gaussianReal 0 1)=1 := by
  have hh := variance_fun_id_gaussianReal (μ:=0) (v:=1)
  rw [variance_eq_integral (X:=fun x : ℝ => x) (by fun_prop),integral_id_gaussianReal] at hh
  simpa only [sub_zero,NNReal.coe_one] using hh

theorem gaussianStandard_expabs_sq_integrable (a : ℝ) :
    Integrable (fun x : ℝ => x^2*Real.exp (a*|x|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_abs_gaussianReal (a+2) 1)).mono'
    (by fun_prop)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))]
  have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  calc
    _ ≤ (Real.exp |x|)^2*Real.exp (a*|x|) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
    _ = Real.exp ((a+2)*|x|) := by rw [← Real.exp_nat_mul,← Real.exp_add]; congr 1; ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem gaussianSmallScale_dominated_limit {T : ℝ} (hT : 0 < T)
    {R : ℝ × ℝ → ℝ} (hR : Continuous R) {K : ℝ}
    (hb : ∀ p, |R p| ≤ K) {w : ℝ → ℝ} (hw : Continuous w) (hp : ∀ x, 0 ≤ w x)
    (a : ℝ) (hi : Integrable (fun x => w x*Real.exp (|a| *|x|)) (gaussianReal 0 1)) :
    Tendsto (fun q : ℝ => ∫ x, w x*(R (q,Real.sqrt (T*q)*x))^2*
      Real.exp (a*Real.sqrt (T*q)*|x|) ∂gaussianReal 0 1) (𝓝[>] 0)
      (𝓝 (∫ x, w x*(R (0,0))^2 ∂gaussianReal 0 1)) := by
  let F := fun q x : ℝ => w x*(R (q,Real.sqrt (T*q)*x))^2*
    Real.exp (a*Real.sqrt (T*q)*|x|)
  have hs : ∀ᶠ q : ℝ in 𝓝[>] 0, 0 ≤ Real.sqrt (T*q) ∧ Real.sqrt (T*q) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (show (0:ℝ) < 1/T from one_div_pos.mpr hT)))] with q hq hq1
    refine ⟨Real.sqrt_nonneg _,?_⟩
    apply (Real.sqrt_le_iff).mpr
    refine ⟨zero_le_one,?_⟩
    have hh := (lt_div_iff₀ hT).mp hq1
    nlinarith
  apply tendsto_integral_filter_of_dominated_convergence
    (bound:=fun x => K^2*(w x*Real.exp (|a| *|x|)))
  · exact Eventually.of_forall fun q => (by
      have hc : Continuous (F q) := by dsimp only [F]; fun_prop
      exact hc.aestronglyMeasurable)
  · filter_upwards [hs] with q hq
    apply Eventually.of_forall
    intro x
    change ‖F q x‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (hp _) (sq_nonneg _)) (Real.exp_nonneg _))]
    have he : a*Real.sqrt (T*q) ≤ |a| :=
      (mul_le_mul_of_nonneg_right (le_abs_self a) hq.1).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq.2 (abs_nonneg a))
    have hr := pow_le_pow_left₀ (abs_nonneg (R (q,Real.sqrt (T*q)*x))) (hb _) 2
    rw [sq_abs] at hr
    calc
      F q x ≤ w x*K^2*Real.exp (|a| *|x|) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hr (hp x))
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right he (abs_nonneg _)))
          (Real.exp_nonneg _) (mul_nonneg (hp _) (sq_nonneg _))
      _ = _ := by ring
  · exact hi.const_mul (K^2)
  · apply Eventually.of_forall
    intro x
    have hc : Continuous (fun q : ℝ => F q x) := by dsimp only [F]; fun_prop
    simpa only [F,mul_zero,Real.sqrt_zero,zero_mul,Real.exp_zero,mul_one] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus Scalar
open scoped Topology NNReal BigOperators

theorem gaussianLinearEnvelopeMass_rescale {s : ℝ} (hs : 0 < s) (a : ℝ) :
    gaussianLinearEnvelopeMass s a =
      ∫ x, Real.exp (a*Real.sqrt s*|x|) ∂gaussianReal 0 1 := by
  unfold gaussianLinearEnvelopeMass gaussianLinearEnvelope
  rw [gaussianKernel_integral_rescale hs (by fun_prop)]
  congr 1
  funext x
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  ring

theorem gaussianLinearEnvelopeMass_tendsto {T : ℝ} (hT : 0 < T) (a : ℝ) :
    Tendsto (fun q : ℝ => gaussianLinearEnvelopeMass (T*q) a) (𝓝[>] 0) (𝓝 1) := by
  have hh := gaussianSmallScale_dominated_limit hT
    (R:=fun _ => (1:ℝ)) continuous_const (K:=1) (fun _ => by norm_num)
    (w:=fun _ => (1:ℝ)) continuous_const (fun _ => zero_le_one) a
    (by simpa only [one_mul] using integrable_exp_mul_abs_gaussianReal |a| 1)
  simp only [one_pow,mul_one,one_mul] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (gaussianLinearEnvelopeMass_rescale (mul_pos hT hq) a).symm

noncomputable def scalarThirdGaussianEnvelope {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (a q : ℝ) : ℝ :=
  (∫ x, gaussianLinearEnvelope (T*q) a x*
    (scalarTailSpatialJet hT α 3 q (fun _ => x))^2)/q

theorem scalarThirdGaussianEnvelope_rescale {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (a : ℝ) {q : ℝ} (hq : 0 < q) :
    scalarThirdGaussianEnvelope hT α a q=
      T*∫ x, x^2*(scalarThirdSlope hT α q (Real.sqrt (T*q)*x))^2*
        Real.exp (a*Real.sqrt (T*q)*|x|) ∂gaussianReal 0 1 := by
  have hmap : Continuous (fun x : ℝ => (q,fun _ : Fin 1 => x)) :=
    continuous_const.prodMk (continuous_pi fun _ => continuous_id)
  have hc := (scalarTailSpatialJet_continuous hT α 3).comp hmap
  have hr := gaussianKernel_integral_rescale (mul_pos hT hq)
    (f:=fun x => Real.exp (a*|x|)*(scalarTailSpatialJet hT α 3 q (fun _ => x))^2)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul (hc.pow 2)).measurable
  unfold scalarThirdGaussianEnvelope gaussianLinearEnvelope
  simp_rw [mul_assoc]
  rw [hr]
  have he (x : ℝ) : Real.exp (a*|Real.sqrt (T*q)*x|)*
      (scalarTailSpatialJet hT α 3 q (fun _ => Real.sqrt (T*q)*x))^2=
      q*(T*(x^2*(scalarThirdSlope hT α q (Real.sqrt (T*q)*x))^2*
        Real.exp (a*Real.sqrt (T*q)*|x|))) := by
    rw [scalarThirdSlope_factor,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_pos hT hq).le]
    rw [← mul_assoc a (Real.sqrt (T*q)) |x|]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_const_mul]
  rw [mul_div_cancel_left₀ _ hq.ne']
  simp only [mul_assoc]

theorem scalarThirdGaussianEnvelope_tendsto {T : ℝ} (hT : 0 < T)
    (α : boundedMassProfiles) (a : ℝ) :
    Tendsto (scalarThirdGaussianEnvelope hT α a) (𝓝[>] 0)
      (𝓝 (T*(scalarTailSpatialJet hT α 4 0 0)^2)) := by
  have hh := gaussianSmallScale_dominated_limit hT
    (R:=fun p => scalarThirdSlope hT α p.1 p.2) (scalarThirdSlope_continuous hT α)
    (fun p => scalarThirdSlope_bound hT α p.1 p.2)
    (w:=fun x : ℝ => x^2) (continuous_pow 2) (fun x => sq_nonneg x) a
    (gaussianStandard_expabs_sq_integrable |a|)
  rw [integral_mul_const,gaussianStandard_sq_integral,one_mul,scalarThirdSlope_zero] at hh
  apply (hh.const_mul T).congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (scalarThirdGaussianEnvelope_rescale hT α a hq).symm

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
 theorem gaussianHierarchyMean_prefix (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (A : S → ℝ) (pre tail : List (GaussianStep ι)) :
    prefixTest pre (gaussianHierarchy w φ tail) (gaussianHierarchyMean w φ A tail) =
      gaussianHierarchyMean w φ A (pre++tail) := by
  induction pre with
  | nil => rfl
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    simp only [prefixTest,prefixContinuation_hierarchy,ih,List.cons_append,gaussianHierarchyMean]

 theorem gaussianHierarchy_block_upper {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ)
    (pre tail : List (GaussianStep ι)) {a b : ℝ}
    (ha : OrderedSteps a (pre++tail)) (hb : ∀ st ∈ pre, st.1 ≤ b) (x : ι → ℝ) :
    gaussianHierarchyHessian w φ (pre++tail) x v v +
      b*(gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) x)^2 ≤
      prefixTest pre (gaussianHierarchy w φ tail)
        (fun y => gaussianHierarchyHessian w φ tail y v v +
          b*(gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) x := by
  induction pre generalizing a x with
  | nil => exact le_rfl
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    have hrest := ha.2.2.2
    have htail := hrest.suffix pre tail
    have hpos : ∀ st ∈ pre, 0 < st.1 := fun st hs => hrest.mem_pos st (List.mem_append_left tail hs)
    have hi := gaussianHierarchy_integrable hw φ (pre++tail) hrest m q x
    have hM := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) (pre++tail) hrest 0
    have hH := gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v (pre++tail) hrest 0
    have hM2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) y)^2) := by
      simpa only [pow_two] using hM.mul hM
    have hMt := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail htail 0
    have hHt := gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v tail htail 0
    have hMt2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) := by
      simpa only [pow_two] using hMt.mul hMt
    obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail htail 0).1
    have hP := prefixTest_smooth0 hC (hHt.add (hMt2.const_mul b)) pre hpos
    have hle := shiftedMean_mono (hH.add (hM2.const_mul b)) hP
      (fun y => ih hrest (fun st hs => hb st (List.mem_cons_of_mem _ hs)) y) hi
    rw [shiftedMean_add hH (hM2.const_mul b) hi,shiftedMean_const_mul] at hle
    have hj := shiftedMean_square_sub_nonneg
      ((gaussianHierarchy_regular hw φ (pre++tail) hrest 0).1.choose_spec.continuous) hM hi
    have hmass := hb (m,q) List.mem_cons_self
    have hn := mul_nonneg (sub_nonneg.mpr hmass) hj
    change gaussianHierarchyResponse w φ (fun s => φ s v) v ((m,q)::(pre++tail)) x +
      b*(gaussianHierarchyMean w φ (fun s => φ s v) ((m,q)::(pre++tail)) x)^2 ≤ _
    simp only [gaussianHierarchyResponse,gaussianHierarchyMean,prefixTest,
      prefixContinuation_hierarchy]
    dsimp only [ν] at hle hj hn
    simp only [gaussianHierarchyHessian,pow_two] at hle hn ⊢
    nlinarith [hle]

 theorem gaussianHierarchy_block_lower {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ)
    (pre tail : List (GaussianStep ι)) {a b : ℝ}
    (ha : OrderedSteps a (pre++tail)) (hb : ∀ st ∈ pre, b ≤ st.1) (x : ι → ℝ) :
    prefixTest pre (gaussianHierarchy w φ tail)
        (fun y => gaussianHierarchyHessian w φ tail y v v +
          b*(gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) x ≤
      gaussianHierarchyHessian w φ (pre++tail) x v v +
      b*(gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) x)^2 := by
  induction pre generalizing a x with
  | nil => exact le_rfl
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    let ν := Measure.pi fun i => gaussianReal 0 (q i)
    have hrest := ha.2.2.2
    have htail := hrest.suffix pre tail
    have hpos : ∀ st ∈ pre, 0 < st.1 := fun st hs => hrest.mem_pos st (List.mem_append_left tail hs)
    have hi := gaussianHierarchy_integrable hw φ (pre++tail) hrest m q x
    have hM := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) (pre++tail) hrest 0
    have hH := gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v (pre++tail) hrest 0
    have hM2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) y)^2) := by
      simpa only [pow_two] using hM.mul hM
    have hMt := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail htail 0
    have hHt := gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v tail htail 0
    have hMt2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) := by
      simpa only [pow_two] using hMt.mul hMt
    obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail htail 0).1
    have hP := prefixTest_smooth0 hC (hHt.add (hMt2.const_mul b)) pre hpos
    have hle := shiftedMean_mono hP (hH.add (hM2.const_mul b))
      (fun y => ih hrest (fun st hs => hb st (List.mem_cons_of_mem _ hs)) y) hi
    rw [shiftedMean_add hH (hM2.const_mul b) hi,shiftedMean_const_mul] at hle
    have hj := shiftedMean_square_sub_nonneg
      ((gaussianHierarchy_regular hw φ (pre++tail) hrest 0).1.choose_spec.continuous) hM hi
    have hmass := hb (m,q) List.mem_cons_self
    have hn := mul_nonneg (sub_nonneg.mpr hmass) hj
    change _ ≤ gaussianHierarchyResponse w φ (fun s => φ s v) v ((m,q)::(pre++tail)) x +
      b*(gaussianHierarchyMean w φ (fun s => φ s v) ((m,q)::(pre++tail)) x)^2
    simp only [gaussianHierarchyResponse,gaussianHierarchyMean,prefixTest,
      prefixContinuation_hierarchy]
    dsimp only [ν] at hle hj hn
    simp only [gaussianHierarchyHessian,pow_two] at hle hn ⊢
    nlinarith [hle]

end SKFluctuations.Hierarchy

 

 
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
 theorem prefixTest_add_const_mul {F A B : (ι → ℝ) → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (pre : List (GaussianStep ι)) (hm : ∀ st ∈ pre, 0 < st.1)
    (c : ℝ) (x : ι → ℝ) :
    prefixTest pre F (fun y => A y+c*B y) x =
      prefixTest pre F A x+c*prefixTest pre F B x := by
  induction pre generalizing x with
  | nil => rfl
  | cons st pre ih =>
    rcases st with ⟨m,q⟩
    have hp : ∀ st ∈ pre, 0 < st.1 := fun st hs => hm st (List.mem_cons_of_mem _ hs)
    have hi := (exponentialIncrement_gaussian q).integrable_shift
      (prefixContinuation_lipschitz hF pre hp) m x
    simp only [prefixTest]
    rw [show prefixTest pre F (fun y => A y+c*B y) =
      (fun y => prefixTest pre F A y+c*prefixTest pre F B y) from funext (ih hp)]
    rw [shiftedMean_add (prefixTest_smooth0 hF hA pre hp)
      ((prefixTest_smooth0 hF hB pre hp).const_mul c) hi,shiftedMean_const_mul]

 
noncomputable def hierarchyBlockVariance (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre tail : List (GaussianStep ι)) (x v : ι → ℝ) : ℝ :=
  prefixTest pre (gaussianHierarchy w φ tail)
    (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) x -
      (gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) x)^2

 
noncomputable def hierarchyBlockHessianDrop (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (pre tail : List (GaussianStep ι)) (x v : ι → ℝ) : ℝ :=
  gaussianHierarchyHessian w φ (pre++tail) x v v -
    prefixTest pre (gaussianHierarchy w φ tail)
      (fun y => gaussianHierarchyHessian w φ tail y v v) x

 theorem hierarchyBlockHessianDrop_bounds {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a b c : ℝ} (ha : OrderedSteps a (pre++tail))
    (hm : ∀ st ∈ pre, c ≤ st.1 ∧ st.1 ≤ b) (x v : ι → ℝ) :
    c*hierarchyBlockVariance w φ pre tail x v ≤ hierarchyBlockHessianDrop w φ pre tail x v ∧
    hierarchyBlockHessianDrop w φ pre tail x v ≤ b*hierarchyBlockVariance w φ pre tail x v := by
  have htail := ha.suffix pre tail
  have hp : ∀ st ∈ pre, 0 < st.1 := fun st hs => ha.mem_pos st (List.mem_append_left tail hs)
  have hM := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail htail 0
  have hH := gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v tail htail 0
  have hM2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) := by
    simpa only [pow_two] using hM.mul hM
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail htail 0).1
  have hlo := gaussianHierarchy_block_lower hw φ v pre tail ha (fun st hs => (hm st hs).1) x
  have hup := gaussianHierarchy_block_upper hw φ v pre tail ha (fun st hs => (hm st hs).2) x
  simp only [gaussianHierarchyHessian] at hlo hup
  rw [prefixTest_add_const_mul hC hH hM2 pre hp] at hlo hup
  dsimp only [hierarchyBlockVariance,hierarchyBlockHessianDrop,gaussianHierarchyHessian] at hlo hup ⊢
  constructor <;> nlinarith

 theorem hierarchyBlockHessianDrop_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x v : ι → ℝ) :
    0 ≤ hierarchyBlockHessianDrop w φ pre tail x v := by
  have hh := gaussianHierarchy_block_lower hw φ v pre tail ha (b:=0)
    (fun st hs => (ha.mem_pos st (List.mem_append_left tail hs)).le) x
  apply sub_nonneg.mpr
  simpa only [zero_mul,add_zero] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem hierarchyBlockVariance_eq_integral {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x v : ι → ℝ) :
    hierarchyBlockVariance w φ pre tail x v =
      ∫ p, (gaussianHierarchyMean w φ (fun s => φ s v) tail
        (forwardEnd pre.length (hierarchyIncrements pre) x p) -
          gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) x)^2
        ∂segmentLaw w φ tail pre x := by
  let M := gaussianHierarchyMean w φ (fun s => φ s v) tail
  let c := gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) x
  have htail := ha.suffix pre tail
  have hp : ∀ st ∈ pre, 0 < st.1 := fun st hs => ha.mem_pos st (List.mem_append_left tail hs)
  have hM := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail htail 0
  have hM2 : BddSmooth 0 (fun y => M y^2) := by simpa only [M,pow_two] using hM.mul hM
  have hD : BddSmooth 0 (fun y => (M y-c)^2) := by
    simpa only [M,pow_two] using (hM.sub (BddSmooth.const 0 c)).mul (hM.sub (BddSmooth.const 0 c))
  rw [integral_segmentLaw_test hw φ hD tail pre ha]
  have he : (fun y => (M y-c)^2) = (fun y => c^2+1*(M y^2+(-2*c)*M y)) := by
    funext y; ring
  change hierarchyBlockVariance w φ pre tail x v = prefixTest pre (gaussianHierarchy w φ tail) (fun y => (M y-c)^2) x
  rw [he]
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail htail 0).1
  rw [prefixTest_affine hC (hM2.add (hM.const_mul (-2*c))) pre hp,
    prefixTest_add_const_mul hC hM2 hM pre hp]
  dsimp only [M]
  rw [gaussianHierarchyMean_prefix]
  dsimp only [hierarchyBlockVariance,c]
  ring

 theorem hierarchyBlockVariance_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (x v : ι → ℝ) :
    0 ≤ hierarchyBlockVariance w φ pre tail x v := by
  rw [hierarchyBlockVariance_eq_integral hw φ pre tail ha]
  exact integral_nonneg fun _ => sq_nonneg _

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]

abbrev GaussianLayer (ι : Type*) := ℝ × List (GaussianStep ι)

def layerSteps (bs : List (GaussianLayer ι)) : List (GaussianStep ι) :=
  (bs.map Prod.snd).flatten

noncomputable def hierarchyLayerBound (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    : List (GaussianLayer ι) → (ι → ℝ) → (ι → ℝ) → ℝ
  | [] => fun x v => gaussianHierarchyHessian w φ [] x v v
  | (μ,pre)::bs => fun x v => μ*hierarchyBlockVariance w φ pre (layerSteps bs) x v +
      prefixTest pre (gaussianHierarchy w φ (layerSteps bs))
        (fun y => hierarchyLayerBound w φ bs y v) x

 theorem hierarchyBlockVariance_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre tail : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (v : ι → ℝ) :
    BddSmooth 0 (fun x => hierarchyBlockVariance w φ pre tail x v) := by
  have ht := ha.suffix pre tail
  have hM := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) tail ht 0
  have hN := gaussianHierarchyMean_smooth hw φ (fun s => φ s v) (pre++tail) ha 0
  have hM2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) tail y)^2) := by
    simpa only [pow_two] using hM.mul hM
  have hN2 : BddSmooth 0 (fun y => (gaussianHierarchyMean w φ (fun s => φ s v) (pre++tail) y)^2) := by
    simpa only [pow_two] using hN.mul hN
  obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ tail ht 0).1
  exact (prefixTest_smooth0 hC hM2 pre (fun st hs => ha.mem_pos st (List.mem_append_left tail hs))).sub hN2

 theorem hierarchyLayerBound_smooth {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs)) (v : ι → ℝ) :
    BddSmooth 0 (fun x => hierarchyLayerBound w φ bs x v) := by
  induction bs generalizing a with
  | nil => exact gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v [] ha 0
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change OrderedSteps a (pre++layerSteps bs) at ha
    have ht := ha.suffix pre (layerSteps bs)
    obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ (layerSteps bs) ht 0).1
    exact ((hierarchyBlockVariance_smooth hw φ pre (layerSteps bs) ha v).const_mul μ).add
      (prefixTest_smooth0 hC (ih ht) pre (fun st hs => ha.mem_pos st (List.mem_append_left _ hs)))

 theorem gaussianHierarchyHessian_le_layers {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1) (x v : ι → ℝ) :
    gaussianHierarchyHessian w φ (layerSteps bs) x v v ≤ hierarchyLayerBound w φ bs x v := by
  induction bs generalizing a x with
  | nil => exact le_rfl
  | cons B bs ih =>
    rcases B with ⟨μ,pre⟩
    change OrderedSteps a (pre++layerSteps bs) at ha
    have ht := ha.suffix pre (layerSteps bs)
    have hp : ∀ st ∈ pre, 0 < st.1 := fun st hs => ha.mem_pos st (List.mem_append_left _ hs)
    have hb := (hierarchyBlockHessianDrop_bounds hw φ pre (layerSteps bs) ha
      (c:=0) (fun st hs => ⟨(hp st hs).le,hm (μ,pre) List.mem_cons_self st hs⟩) x v).2
    obtain ⟨C,hC⟩ := (gaussianHierarchy_regular hw φ (layerSteps bs) ht 0).1
    have hh := prefixTest_mono hC
      (gaussianHierarchyResponse_smooth hw φ (fun s => φ s v) v (layerSteps bs) ht 0)
      (hierarchyLayerBound_smooth hw φ bs ht v)
      (fun y => ih ht (fun B hB => hm B (List.mem_cons_of_mem _ hB)) y) pre hp x
    change gaussianHierarchyHessian w φ (pre++layerSteps bs) x v v ≤
      μ*hierarchyBlockVariance w φ pre (layerSteps bs) x v+
        prefixTest pre (gaussianHierarchy w φ (layerSteps bs)) (fun y => hierarchyLayerBound w φ bs y v) x
    dsimp only [hierarchyBlockHessianDrop,gaussianHierarchyHessian] at hb ⊢
    linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {ι S κ : Type*} [Fintype ι] [Fintype S] [Nonempty S]

 theorem gaussianHierarchyHessian_sum_right {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x v : ι → ℝ) (s : Finset κ) (u : κ → ι → ℝ) :
    gaussianHierarchyHessian w φ steps x v (∑ i ∈ s, u i) =
      ∑ i ∈ s, gaussianHierarchyHessian w φ steps x v (u i) := by
  rw [gaussianHierarchyHessian_symm,gaussianHierarchyHessian_sum_left hw φ steps ha]
  exact Finset.sum_congr rfl fun i _ => gaussianHierarchyHessian_symm w φ steps x (u i) v

 theorem gaussianHierarchyHessian_sum_bound {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) (x : ι → ℝ) (s : Finset κ) (v : κ → ι → ℝ) :
    gaussianHierarchyHessian w φ steps x (∑ i ∈ s, v i) (∑ i ∈ s, v i) ≤
      (s.card:ℝ)*(∑ i ∈ s, gaussianHierarchyHessian w φ steps x (v i) (v i)) := by
  have hp (i j : κ) : 2*gaussianHierarchyHessian w φ steps x (v i) (v j) ≤
      gaussianHierarchyHessian w φ steps x (v i) (v i)+
        gaussianHierarchyHessian w φ steps x (v j) (v j) := by
    have hh := gaussianHierarchyHessian_block_nonneg hw φ steps ha x (v i) (v j) 1
    nlinarith
  have hh : 2*gaussianHierarchyHessian w φ steps x (∑ i ∈ s, v i) (∑ i ∈ s, v i) ≤
      2*(s.card:ℝ)*(∑ i ∈ s, gaussianHierarchyHessian w φ steps x (v i) (v i)) := by
    calc
      _ = ∑ i ∈ s, ∑ j ∈ s, 2*gaussianHierarchyHessian w φ steps x (v i) (v j) := by
        rw [gaussianHierarchyHessian_sum_left hw φ steps ha]
        simp_rw [gaussianHierarchyHessian_sum_right hw φ steps ha]
        simp only [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, (gaussianHierarchyHessian w φ steps x (v i) (v i)+
          gaussianHierarchyHessian w φ steps x (v j) (v j)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hp i j
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
        ring
  linarith

 theorem gaussianHierarchyHessian_fork_layer_bound {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (bs : List (GaussianLayer ι))
    {a : ℝ} (ha : OrderedSteps a (layerSteps bs))
    (hm : ∀ B ∈ bs, ∀ st ∈ B.2, st.1 ≤ B.1)
    (x : ι → ℝ) (s : Finset κ) (v : κ → ι → ℝ) :
    gaussianHierarchyHessian w φ (layerSteps bs) x (∑ i ∈ s, v i) (∑ i ∈ s, v i) ≤
      (s.card:ℝ)*(∑ i ∈ s, hierarchyLayerBound w φ bs x (v i)) := by
  exact (gaussianHierarchyHessian_sum_bound hw φ (layerSteps bs) ha x s v).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      gaussianHierarchyHessian_le_layers hw φ bs ha hm x (v i)) (Nat.cast_nonneg _))

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem boundedMartingale_sq_submartingale {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {X : ℕ → Ω → E} (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) :
    Submartingale (fun j ω => ‖X j ω‖^2) 𝒢 μ := by
  have hi j : Integrable (fun ω => ‖X j ω‖^2) μ := by
    apply Integrable.of_bound ((hX.stronglyAdapted j).mono (𝒢.le j) |>.norm.pow 2).aestronglyMeasurable (R^2)
    filter_upwards [hR j] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω _
  refine ⟨fun j => (hX.stronglyAdapted j).norm.pow 2, ?_, hi⟩
  intro i j hij
  have hint : Integrable (fun ω => ‖X j ω‖^(2:ℝ)) μ := by simpa only [Real.rpow_two] using hi j
  have h := Integrable.norm_condExp_rpow_le (m := 𝒢 i) (f := X j) (by norm_num : (1:ℝ) ≤ 2) hint
  filter_upwards [h,hX.condExp_ae_eq hij] with ω hω he
  simpa only [Real.rpow_two,he] using hω

 

 theorem boundedMartingale_compensator_moment {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    {X : ℕ → Ω → E} (hX : Martingale X 𝒢 μ)
    {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) {p : ℕ} (hp : 0 < p) (N : ℕ) :
    (∫ ω, finiteCompensator μ 𝒢 (fun j ω => ‖X j ω‖^2) N ω^p ∂μ) ≤
      (p:ℝ)^p*∫ ω, ‖X N ω‖^(2*p) ∂μ := by
  have h := boundedSubmartingale_compensator_moment (boundedMartingale_sq_submartingale hX hR)
    (fun j => Eventually.of_forall (fun ω => sq_nonneg ‖X j ω‖))
    (R := R^2) (fun j => ?_) hp N
  · simpa only [← pow_mul] using h
  · filter_upwards [hR j] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω _

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

 

 theorem boundedMartingale_conditional_square_increment
    {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›} {X : ℕ → Ω → E}
    (hX : Martingale X 𝒢 μ) {R : ℝ} (hR : ∀ j, ∀ᵐ ω ∂μ, ‖X j ω‖ ≤ R) (j : ℕ) :
    μ[fun ω => ‖X (j+1) ω-X j ω‖^2 | 𝒢 j] =ᵐ[μ]
      μ[(fun ω => ‖X (j+1) ω‖^2)-(fun ω => ‖X j ω‖^2) | 𝒢 j] := by
  let U : ℕ → Ω → ℝ := fun k ω => ‖X k ω‖^2
  let V : Ω → ℝ := fun ω => inner ℝ (X j ω) (X (j+1) ω)
  have hU := boundedMartingale_sq_submartingale hX hR
  have hm k := (hX.stronglyAdapted k).mono (𝒢.le k)
  have hiV : Integrable V μ := by
    apply Integrable.of_bound ((hm j).aestronglyMeasurable.inner (hm (j+1)).aestronglyMeasurable) (R^2)
    filter_upwards [hR j,hR (j+1)] with ω hω hω'
    calc
      _ ≤ ‖X j ω‖*‖X (j+1) ω‖ := norm_inner_le_norm _ _
      _ ≤ R*R := mul_le_mul hω hω' (norm_nonneg _) ((norm_nonneg _).trans hω)
      _ = R^2 := by ring
  have hpull : μ[V | 𝒢 j] =ᵐ[μ] fun ω => inner ℝ (X j ω) ((μ[X (j+1) | 𝒢 j]) ω) :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) (hX.stronglyAdapted j) hiV (hX.integrable (j+1))
  have hV : μ[V | 𝒢 j] =ᵐ[μ] U j := by
    filter_upwards [hpull,hX.condExp_ae_eq (Nat.le_succ j)] with ω he he'
    simpa only [he', real_inner_self_eq_norm_sq] using he
  have he : (fun ω => ‖X (j+1) ω-X j ω‖^2) = U (j+1)+U j-(2:ℝ) • V := by
    funext ω
    dsimp only [U,V,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [norm_sub_sq_real, real_inner_comm (X (j+1) ω)]
    ring
  rw [he]
  have hj : μ[U j | 𝒢 j] = U j :=
    condExp_of_stronglyMeasurable (𝒢.le j) ((hX.stronglyAdapted j).norm.pow 2) (hU.integrable j)
  filter_upwards [condExp_sub ((hU.integrable (j+1)).add (hU.integrable j)) (hiV.const_mul 2) (𝒢 j),
    condExp_add (hU.integrable (j+1)) (hU.integrable j) (𝒢 j),
    condExp_smul (μ := μ) (2:ℝ) V (𝒢 j), hV,
    condExp_sub (hU.integrable (j+1)) (hU.integrable j) (𝒢 j)] with ω h1 h2 h3 h4 h5
  dsimp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1 h2 h3 h5
  change (μ[U (j+1)+U j-(2:ℝ) • V | 𝒢 j]) ω =
    (μ[U (j+1)+U j | 𝒢 j]) ω-(μ[(2:ℝ) • V | 𝒢 j]) ω at h1
  change (μ[U (j+1)+U j | 𝒢 j]) ω =
    (μ[U (j+1) | 𝒢 j]) ω+(μ[U j | 𝒢 j]) ω at h2
  change (μ[U (j+1)-U j | 𝒢 j]) ω =
    (μ[U (j+1) | 𝒢 j]) ω-(μ[U j | 𝒢 j]) ω at h5
  change (μ[U (j+1)+U j-(2:ℝ) • V | 𝒢 j]) ω = (μ[U (j+1)-U j | 𝒢 j]) ω
  rw [h1,h2,h3,h4,h5,hj]
  ring

end SKFluctuations.Hierarchy

end

end OAI
