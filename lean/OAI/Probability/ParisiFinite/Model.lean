import Mathlib

namespace OAI

/-! Model. -/

noncomputable section



 

 

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma l2_mean_inner (f : Lp ℝ 2 P) :
    (∫ ω,f ω ∂P) = inner ℝ ((memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P).toLp _) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 P)] with ω hω
  simp

omit [IsProbabilityMeasure P] in
lemma l2_square_integral (f : Lp ℝ 2 P) : (∫ ω,f ω^2 ∂P)=‖f‖^2 := by
  rw [←real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp [pow_two]

lemma l2_variance (f : Lp ℝ 2 P) :
    variance f P=‖f‖^2-(∫ ω,f ω ∂P)^2 := by
  rw [variance_eq_sub (Lp.memLp f)]
  simpa only [Pi.pow_apply] using congrArg (fun x : ℝ => x-(∫ ω,f ω ∂P)^2) (l2_square_integral f)

lemma continuous_l2_mean : Continuous (fun f : Lp ℝ 2 P => ∫ ω,f ω ∂P) := by
  simp_rw [l2_mean_inner]
  fun_prop

lemma continuous_l2_variance : Continuous (fun f : Lp ℝ 2 P => variance f P) := by
  simp_rw [l2_variance]
  exact (continuous_norm.pow 2).sub (continuous_l2_mean.pow 2)

lemma hasGaussianLaw_l2_limit {f : ℕ → Lp ℝ 2 P} {g : Lp ℝ 2 P}
    (hf : ∀ n,HasGaussianLaw (f n) P) (hg : Tendsto f atTop (𝓝 g)) :
    HasGaussianLaw g P := by
  have hd := (tendstoInMeasure_of_tendsto_Lp hg).tendstoInDistribution
    (fun n => (Lp.aestronglyMeasurable (f n)).aemeasurable)
  have hc := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hd.tendsto
  have hm := continuous_l2_mean.tendsto g |>.comp hg
  have hv := continuous_l2_variance.tendsto g |>.comp hg
  have hmap : P.map g=gaussianReal (∫ ω,g ω ∂P) (variance g P).toNNReal := by
    apply Measure.ext_of_charFun
    funext t
    have ht := (((hm.ofReal.const_mul (t:ℂ)).mul_const Complex.I).sub
      ((hv.ofReal.mul_const ((t:ℂ)^2)).div_const 2)).cexp
    have he (n : ℕ) : charFun (P.map (f n)) t =
        Complex.exp ((t:ℂ)*(∫ ω,f n ω ∂P)*Complex.I-(variance (f n) P)* (t:ℂ)^2/2) := by
      rw [(hf n).map_eq_gaussianReal,charFun_gaussianReal,Real.coe_toNNReal _ (variance_nonneg _ _)]
    have ht' : Tendsto (fun n => charFun (P.map (f n)) t) atTop
        (𝓝 (Complex.exp ((t:ℂ)*(∫ ω,g ω ∂P)*Complex.I-(variance g P)*(t:ℂ)^2/2))) := by
      convert! ht using 1
      exact funext he
    rw [charFun_gaussianReal,Real.coe_toNNReal _ (variance_nonneg _ _)]
    exact tendsto_nhds_unique (hc t) ht'
  exact ⟨(Lp.aestronglyMeasurable g).aemeasurable, by rw [hmap]; infer_instance⟩

lemma isClosed_gaussian_l2 : IsClosed {f : Lp ℝ 2 P | HasGaussianLaw f P} := by
  apply isSeqClosed_iff_isClosed.mp
  intro f g hf hg
  exact hasGaussianLaw_l2_limit hf hg
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction
variable (ι : Type*)
def gaussianProduct : Measure (ι → ℝ) := Measure.infinitePi (fun _ : ι => gaussianReal 0 1)
instance : IsProbabilityMeasure (gaussianProduct ι) := by
  unfold gaussianProduct
  infer_instance
lemma gaussianCoordinate_law (i : ι) :
    HasLaw (fun ω : ι → ℝ => ω i) (gaussianReal 0 1) (gaussianProduct ι) :=
  (measurePreserving_eval_infinitePi (fun _ : ι => gaussianReal 0 1) i).hasLaw
lemma gaussianCoordinate_gaussian (i : ι) :
    HasGaussianLaw (fun ω : ι → ℝ => ω i) (gaussianProduct ι) :=
  (gaussianCoordinate_law ι i).hasGaussianLaw
lemma gaussianCoordinate_memLp (i : ι) :
    MemLp (fun ω : ι → ℝ => ω i) 2 (gaussianProduct ι) :=
  (gaussianCoordinate_gaussian ι i).memLp_two
def gaussianCoordinate (i : ι) : Lp ℝ 2 (gaussianProduct ι) :=
  (gaussianCoordinate_memLp ι i).toLp (fun ω => ω i)
lemma gaussianCoordinate_ae (i : ι) : gaussianCoordinate ι i =ᵐ[gaussianProduct ι] (fun ω => ω i) :=
  MemLp.coeFn_toLp _
lemma gaussianCoordinate_mean (i : ι) : (∫ ω,gaussianCoordinate ι i ω ∂gaussianProduct ι)=0 := by
  rw [integral_congr_ae (gaussianCoordinate_ae ι i)]
  exact (gaussianCoordinate_law ι i).integral_eq ▸ integral_id_gaussianReal
lemma gaussianCoordinates_independent :
    iIndepFun (fun i (ω : ι → ℝ) => ω i) (gaussianProduct ι) :=
  iIndepFun_infinitePi (X:=fun _ : ι => id) (fun _ => measurable_id)

lemma gaussianCoordinate_variance (i : ι) : variance (gaussianCoordinate ι i) (gaussianProduct ι)=1 := by
  have hh := ((gaussianCoordinate_law ι i).congr (gaussianCoordinate_ae ι i)).variance_eq
  simpa using hh

lemma gaussianCoordinate_inner [DecidableEq ι] (i j : ι) :
    inner ℝ (gaussianCoordinate ι i) (gaussianCoordinate ι j) = if i=j then 1 else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl,real_inner_self_eq_norm_sq]
    have hh := l2_variance (gaussianCoordinate ι i)
    rw [gaussianCoordinate_variance,gaussianCoordinate_mean] at hh
    simpa using hh.symm
  · rw [ite_eq_right hij,L2.inner_def]
    have he : (∫ ω,inner ℝ (gaussianCoordinate ι i ω) (gaussianCoordinate ι j ω) ∂gaussianProduct ι)
        =∫ ω,ω i*ω j ∂gaussianProduct ι := by
      apply integral_congr_ae
      filter_upwards [gaussianCoordinate_ae ι i,gaussianCoordinate_ae ι j] with ω hi hj
      simp [hi,hj,mul_comm]
    rw [he]
    have hind := (gaussianCoordinates_independent ι).indepFun hij
    have hh := hind.integral_mul_eq_mul_integral
      (gaussianCoordinate_memLp ι i).aestronglyMeasurable
      (gaussianCoordinate_memLp ι j).aestronglyMeasurable
    change (∫ ω,ω i*ω j ∂gaussianProduct ι)=_ at hh
    rw [hh]
    have hm (k : ι) : (∫ ω,ω k ∂gaussianProduct ι)=0 := by
      rw [←integral_congr_ae (gaussianCoordinate_ae ι k)]
      exact gaussianCoordinate_mean ι k
    simp [hm]

lemma gaussianCoordinates_orthonormal : Orthonormal ℝ (gaussianCoordinate ι) := by
  classical
  exact orthonormal_iff_ite.mpr (gaussianCoordinate_inner ι)

def gaussianLpIsometry : lp (fun _ : ι => ℝ) 2 →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct ι) :=
  (gaussianCoordinates_orthonormal ι).orthogonalFamily.linearIsometry

lemma hasSum_gaussianLpIsometry (f : lp (fun _ : ι => ℝ) 2) :
    HasSum (fun i => f i • gaussianCoordinate ι i) (gaussianLpIsometry ι f) := by
  exact (gaussianCoordinates_orthonormal ι).orthogonalFamily.hasSum_linearIsometry f

lemma gaussianCoordinates_sum_ae (s : Finset ι) (f : ι → ℝ) :
    ((∑ i∈s,f i • gaussianCoordinate ι i : Lp ℝ 2 (gaussianProduct ι)) : (ι → ℝ) → ℝ)
      =ᵐ[gaussianProduct ι] (fun ω => ∑ i∈s,f i*ω i) := by
  classical
  have ha : ∀ᵐ ω ∂gaussianProduct ι, ∀ i∈s,
      (f i • gaussianCoordinate ι i : Lp ℝ 2 (gaussianProduct ι)) ω=f i*ω i := by
    apply (ae_ball_iff s.finite_toSet.countable).mpr
    intro i hi
    filter_upwards [Lp.coeFn_smul (f i) (gaussianCoordinate ι i),gaussianCoordinate_ae ι i] with ω hs hc
    simp [hs,hc]
  filter_upwards [Lp.coeFn_finsetSum s (fun i => f i • gaussianCoordinate ι i),ha] with ω hs ha
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => ha i hi)

lemma gaussianCoordinates_sum_gaussian (s : Finset ι) (f : ι → ℝ) :
    HasGaussianLaw ((∑ i∈s,f i • gaussianCoordinate ι i : Lp ℝ 2 (gaussianProduct ι)) : (ι → ℝ) → ℝ)
      (gaussianProduct ι) := by
  classical
  have hind := (gaussianCoordinates_independent ι).precomp (g:=(Subtype.val : s → ι)) Subtype.val_injective
  have hs := hind.comp (fun i x => f i*x) (fun _ => by fun_prop)
  have hg (i : s) : HasGaussianLaw (fun ω : ι → ℝ => f i*ω i) (gaussianProduct ι) :=
    (gaussianCoordinate_gaussian ι i).fun_smul (f i)
  have hh := hs.hasGaussianLaw_fun_sum hg
  have hh' : HasGaussianLaw (fun ω : ι → ℝ => ∑ i∈s,f i*ω i) (gaussianProduct ι) := by
    convert! hh using 1
    funext ω
    exact (Finset.sum_coe_sort s (fun i => f i*ω i)).symm
  exact hh'.congr (gaussianCoordinates_sum_ae ι s f).symm

lemma gaussianLpIsometry_gaussian (f : lp (fun _ : ι => ℝ) 2) :
    HasGaussianLaw (gaussianLpIsometry ι f) (gaussianProduct ι) := by
  apply isClosed_gaussian_l2.mem_of_tendsto (hasSum_gaussianLpIsometry ι f)
  exact Eventually.of_forall (fun s => gaussianCoordinates_sum_gaussian ι s f)

lemma gaussianLpIsometry_mean (f : lp (fun _ : ι => ℝ) 2) :
    (∫ ω,gaussianLpIsometry ι f ω ∂gaussianProduct ι)=0 := by
  have ht := continuous_l2_mean.tendsto (gaussianLpIsometry ι f) |>.comp (hasSum_gaussianLpIsometry ι f)
  have hs (s : Finset ι) : (∫ ω,(∑ i∈s,f i • gaussianCoordinate ι i : Lp ℝ 2 (gaussianProduct ι)) ω
      ∂gaussianProduct ι)=0 := by
    rw [integral_congr_ae (gaussianCoordinates_sum_ae ι s f)]
    rw [integral_finsetSum _ (fun i hi => (gaussianCoordinate_memLp ι i).integrable (by norm_num) |>.const_mul (f i))]
    apply Finset.sum_eq_zero
    intro i hi
    rw [integral_const_mul,←integral_congr_ae (gaussianCoordinate_ae ι i),gaussianCoordinate_mean,mul_zero]
  change Tendsto (fun s : Finset ι => ∫ ω,(∑ i∈s,f i • gaussianCoordinate ι i : Lp ℝ 2 (gaussianProduct ι)) ω ∂gaussianProduct ι) atTop _ at ht
  simp only [hs] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*}
def gaussianHilbertMap (b : HilbertBasis ι ℝ H) : H →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProduct ι) :=
  (gaussianLpIsometry ι).comp b.repr.toLinearIsometry
lemma gaussianHilbertMap_gaussian (b : HilbertBasis ι ℝ H) (x : H) :
    HasGaussianLaw (gaussianHilbertMap b x) (gaussianProduct ι) :=
  gaussianLpIsometry_gaussian ι (b.repr x)
lemma gaussianHilbertMap_mean (b : HilbertBasis ι ℝ H) (x : H) :
    (∫ ω,gaussianHilbertMap b x ω ∂gaussianProduct ι)=0 :=
  gaussianLpIsometry_mean ι (b.repr x)

lemma linear_apply_pi {J : Type*} [Fintype J] [DecidableEq J] (L : (J → ℝ) →L[ℝ] ℝ) (x : J → ℝ) :
    L x=∑ i,x i*L (Pi.single i 1) := by
  classical
  have h : (∑ i,x i • Pi.single i (1:ℝ))=x := by
    ext j
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
  conv_lhs => rw [←h]
  rw [map_sum]
  simp

lemma gaussianHilbertMap_sum_ae {J : Type*} [Fintype J]
    (b : HilbertBasis ι ℝ H) (x : J → H) (c : J → ℝ) :
    gaussianHilbertMap b (∑ i,c i • x i) =ᵐ[gaussianProduct ι]
      (fun ω => ∑ i,c i*gaussianHilbertMap b (x i) ω) := by
  classical
  rw [map_sum]
  simp only [map_smul]
  have he : ∀ᵐ ω ∂gaussianProduct ι,∀ i,
      (c i • gaussianHilbertMap b (x i) : Lp ℝ 2 (gaussianProduct ι)) ω =
        c i*gaussianHilbertMap b (x i) ω :=
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (gaussianHilbertMap b (x i)))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => c i • gaussianHilbertMap b (x i)),he] with ω hs he
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => he i)

lemma gaussianHilbertMap_joint_gaussian {J : Type*} [Fintype J]
    (b : HilbertBasis ι ℝ H) (x : J → H) :
    HasGaussianLaw (fun ω i => gaussianHilbertMap b (x i) ω) (gaussianProduct ι) := by
  classical
  have hm : AEMeasurable (fun ω i => gaussianHilbertMap b (x i) ω) (gaussianProduct ι) :=
    AEMeasurable.of_eval (fun i => (Lp.aestronglyMeasurable _).aemeasurable)
  refine ⟨hm, isGaussian_of_isGaussian_map (fun L => ?_)⟩
  rw [AEMeasurable.map_map_of_aemeasurable L.measurable.aemeasurable hm]
  have ha : gaussianHilbertMap b (∑ i,L (Pi.single i 1) • x i) =ᵐ[gaussianProduct ι]
      L ∘ (fun ω i => gaussianHilbertMap b (x i) ω) := by
    filter_upwards [gaussianHilbertMap_sum_ae b x (fun i => L (Pi.single i 1))] with ω hω
    rw [hω]
    change (∑ i,L (Pi.single i 1)*gaussianHilbertMap b (x i) ω) = L (fun i => gaussianHilbertMap b (x i) ω)
    rw [linear_apply_pi L]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  exact ((gaussianHilbertMap_gaussian b _).congr ha).isGaussian_map

lemma gaussianHilbertMap_covariance (b : HilbertBasis ι ℝ H) (x y : H) :
    cov[gaussianHilbertMap b x,gaussianHilbertMap b y;gaussianProduct ι]=inner ℝ x y := by
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),gaussianHilbertMap_mean,gaussianHilbertMap_mean]
  simp only [zero_mul,sub_zero]
  rw [←(gaussianHilbertMap b).inner_map_map,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp [mul_comm]
end BrownianConstruction

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction

def initialIndicator (t : ℝ≥0) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (s:=Icc (0:ℝ) (t:ℝ)) measurableSet_Icc isCompact_Icc.measure_ne_top (1:ℝ)

lemma initialIndicator_inner (s t : ℝ≥0) :
    inner ℝ (initialIndicator s) (initialIndicator t)=(min s t : ℝ≥0) := by
  rw [initialIndicator,initialIndicator,L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    measurableSet_Icc measurableSet_Icc isCompact_Icc.measure_ne_top isCompact_Icc.measure_ne_top]
  simp [Icc_inter_Icc,Real.volume_real_Icc_of_le (show 0 ≤ min (s:ℝ) t by positivity)]

variable {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure ℝ)))
def preBrownian (t : ℝ≥0) : (ι → ℝ) → ℝ := gaussianHilbertMap b (initialIndicator t)

lemma preBrownian_gaussian : IsGaussianProcess (preBrownian b) (gaussianProduct ι) where
  hasGaussianLaw I := gaussianHilbertMap_joint_gaussian b (fun i : I => initialIndicator i)
lemma preBrownian_mean (t : ℝ≥0) : (∫ ω,preBrownian b t ω ∂gaussianProduct ι)=0 :=
  gaussianHilbertMap_mean b (initialIndicator t)
lemma preBrownian_covariance (s t : ℝ≥0) :
    cov[preBrownian b s,preBrownian b t;gaussianProduct ι]=(min s t : ℝ≥0) := by
  rw [preBrownian,preBrownian,gaussianHilbertMap_covariance,initialIndicator_inner]
lemma preBrownian_isPreBrownian : IsPreBrownianReal (preBrownian b) (gaussianProduct ι) :=
  (preBrownian_gaussian b).isPreBrownianReal_of_covariance (preBrownian_mean b)
    (fun s t hst => by rw [preBrownian_covariance,min_eq_left hst])
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction

def gaussianFourth : ℝ := ∫ z : ℝ,|z|^4 ∂gaussianReal 0 1
lemma gaussianFourth_nonneg : 0≤gaussianFourth := integral_nonneg (fun _ => by positivity)
lemma gaussian_abs_fourth_integrable (v : ℝ≥0) : Integrable (fun z : ℝ => |z|^4) (gaussianReal 0 v) := by
  simpa only [Real.norm_eq_abs,id_eq] using
    (memLp_id_gaussianReal' (μ:=0) (v:=v) 4 (by norm_num)).integrable_norm_pow (by norm_num : (4:ℕ)≠0)
lemma gaussian_abs_fourth (v : ℝ≥0) :
    (∫ z : ℝ,|z|^4 ∂gaussianReal 0 v)=gaussianFourth*(v:ℝ)^2 := by
  have hm : (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt v*z)=gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      change (Real.sqrt v)^2 * 1 = (v:ℝ)
      rw [Real.sq_sqrt v.coe_nonneg,mul_one]
  rw [←hm,integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul,mul_pow,abs_of_nonneg (Real.sqrt_nonneg _),integral_const_mul]
  have hv : (Real.sqrt v)^4=(v:ℝ)^2 := by rw [show (Real.sqrt v)^4=((Real.sqrt v)^2)^2 by ring,Real.sq_sqrt v.coe_nonneg]
  rw [hv,mul_comm]
  rfl

lemma fourth_tail_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) {ε : ℝ} (hε : 0<ε) :
    P {ω | ε < |X ω|}≤ENNReal.ofReal (gaussianFourth*(v:ℝ)^2/ε^4) := by
  have hi : Integrable (fun ω => |X ω|^4) P := by
    simpa only [Real.norm_eq_abs] using
      (hX.hasGaussianLaw.memLp (p:=4) (by norm_num)).integrable_norm_pow (by norm_num : (4:ℕ)≠0)
  have he : (∫ ω,|X ω|^4 ∂P)=gaussianFourth*(v:ℝ)^2 := by
    rw [←gaussian_abs_fourth]
    exact hX.integral_comp (f:=fun z : ℝ => |z|^4) (by fun_prop)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (fun ω =>
    show 0≤|X ω|^4 by positivity)) hi (ε^4)
  rw [he] at hmark
  have hsub : {ω | ε < |X ω|}⊆{ω | ε^4 ≤ |X ω|^4} := by
    intro ω hω
    exact pow_le_pow_left₀ hε.le hω.le 4
  have hr : P.real {ω | ε < |X ω|}≤gaussianFourth*(v:ℝ)^2/ε^4 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hm := measureReal_mono (μ:=P) hsub
    nlinarith [pow_pos hε 4]
  simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hr
end BrownianConstruction

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction

def dyadicPoint (n k : ℕ) : ℝ≥0 := (k:ℝ≥0)/(2:ℝ≥0)^n
def dyadicIndex (n : ℕ) (t : ℝ≥0) : ℕ := ⌊(2:ℝ≥0)^n*t⌋₊
def dyadicRound (n : ℕ) (t : ℝ≥0) : ℝ≥0 := dyadicPoint n (dyadicIndex n t)

lemma dyadicPoint_mono (n : ℕ) : Monotone (dyadicPoint n) := by
  intro j k hjk
  exact div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)
lemma dyadicPoint_succ (n k : ℕ) :
    (dyadicPoint n (k+1):ℝ)-(dyadicPoint n k:ℝ)=(1/2:ℝ)^n := by
  simp only [dyadicPoint,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast,NNReal.coe_ofNat]
  push_cast
  rw [one_div_pow]
  ring
lemma dyadicRound_le (n : ℕ) (t : ℝ≥0) : dyadicRound n t≤t := by
  rw [dyadicRound,dyadicPoint,div_le_iff₀ (by positivity)]
  simpa only [dyadicIndex,mul_comm] using Nat.floor_le (show 0≤(2:ℝ≥0)^n*t from bot_le)
lemma lt_dyadicRound_add (n : ℕ) (t : ℝ≥0) :
    t<dyadicRound n t+(1/2:ℝ≥0)^n := by
  have h := Nat.lt_floor_add_one ((2:ℝ≥0)^n*t)
  rw [dyadicRound,dyadicPoint,one_div_pow,←add_div,lt_div_iff₀ (by positivity)]
  simpa only [dyadicIndex,mul_comm] using h
lemma dyadicIndex_le (n N : ℕ) {t : ℝ≥0} (ht : t≤N) : dyadicIndex n t≤N*2^n := by
  apply Nat.floor_le_of_le
  push_cast
  exact (mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (mul_comm _ _)
lemma dyadicIndex_succ_div (n : ℕ) (t : ℝ≥0) : dyadicIndex (n+1) t/2=dyadicIndex n t := by
  unfold dyadicIndex
  rw [pow_succ,mul_right_comm]
  exact Nat.mul_cast_floor_div_cancel (by norm_num : (2:ℕ)≠0) ((2:ℝ≥0)^n*t)
lemma dyadicPoint_double (n k : ℕ) : dyadicPoint (n+1) (2*k)=dyadicPoint n k := by
  apply NNReal.coe_injective
  simp only [dyadicPoint,NNReal.coe_div,NNReal.coe_pow,NNReal.coe_natCast,NNReal.coe_ofNat]
  push_cast
  rw [pow_succ]
  field_simp

lemma dyadicRound_successor_cases (n : ℕ) (t : ℝ≥0) :
    dyadicRound (n+1) t=dyadicRound n t ∨
      dyadicRound (n+1) t=dyadicPoint (n+1) (2*dyadicIndex n t+1) := by
  have h := dyadicIndex_succ_div n t
  have hk : dyadicIndex (n+1) t=2*dyadicIndex n t ∨ dyadicIndex (n+1) t=2*dyadicIndex n t+1 := by omega
  rcases hk with hk|hk
  · left
    simp only [dyadicRound,hk,dyadicPoint_double]
  · right
    simp only [dyadicRound,hk]
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction

def DyadicGood (r : ℝ) (X : ℝ≥0 → ℝ) : Prop :=
  ∀ N : ℕ, ∃ n₀ : ℕ, ∀ n≥n₀, ∀ k<N*2^n,
    dist (X (dyadicPoint n (k+1))) (X (dyadicPoint n k)) ≤ r^n

lemma round_step_bound {r : ℝ} {X : ℝ≥0 → ℝ} {N n : ℕ}
    (hg : ∀ k<N*2^(n+1), dist (X (dyadicPoint (n+1) (k+1)))
      (X (dyadicPoint (n+1) k))≤r^(n+1)) (hr : 0≤r) {t : ℝ≥0} (ht : t<N) :
    dist (X (dyadicRound (n+1) t)) (X (dyadicRound n t))≤r^(n+1) := by
  rcases dyadicRound_successor_cases n t with he|he
  · rw [he,dist_self]
    positivity
  · rw [he,dyadicRound,←dyadicPoint_double n (dyadicIndex n t)]
    apply hg
    have hi : dyadicIndex n t<N*2^n := by
      apply (Nat.floor_lt (show 0 ≤ (2:ℝ≥0)^n*t from bot_le)).mpr
      simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using
        mul_lt_mul_of_pos_left ht (show 0<(2:ℝ≥0)^n by positivity)
    rw [pow_succ,←Nat.mul_assoc]
    omega

lemma dyadicRound_cauchy {r : ℝ} (hr : 0≤r) (hr1 : r<1)
    {X : ℝ≥0 → ℝ} (hg : DyadicGood r X) (t : ℝ≥0) :
    CauchySeq (fun n => X (dyadicRound n t)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt t
  obtain ⟨n₀,hn₀⟩ := hg N
  apply (cauchySeq_shift n₀).mp
  apply cauchySeq_of_le_geometric r (r^(n₀+1)) hr1
  intro n
  have hh := round_step_bound (hn₀ (n+n₀+1) (by omega)) hr hN
  rw [dist_comm]
  convert hh using 1 <;> simp only [Nat.add_assoc,pow_add] <;> ring_nf

def dyadicLimit (X : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := limUnder atTop (fun n => X (dyadicRound n t))
lemma tendsto_dyadicLimit {r : ℝ} (hr : 0≤r) (hr1 : r<1)
    {X : ℝ≥0 → ℝ} (hg : DyadicGood r X) (t : ℝ≥0) :
    Tendsto (fun n => X (dyadicRound n t)) atTop (𝓝 (dyadicLimit X t)) :=
  (dyadicRound_cauchy hr hr1 hg t).tendsto_limUnder

lemma dyadicLimit_error {r : ℝ} (hr : 0≤r) (hr1 : r<1)
    {X : ℝ≥0 → ℝ} (hg : DyadicGood r X) {N n : ℕ}
    (hn : ∀ m≥n, ∀ k<N*2^m, dist (X (dyadicPoint m (k+1)))
      (X (dyadicPoint m k)) ≤ r^m) {t : ℝ≥0} (ht : t<N) :
    dist (X (dyadicRound n t)) (dyadicLimit X t)≤r^n/(1-r) := by
  have hs : ∀ m, dist (X (dyadicRound (m+1+n) t)) (X (dyadicRound (m+n) t)) ≤ r^n*r^m := by
    intro m
    have hh := round_step_bound (hn (m+n+1) (by omega)) hr ht
    have hh' : r^(m+n+1)≤r^n*r^m := by
      rw [pow_succ,pow_add]
      nlinarith [pow_nonneg hr m,pow_nonneg hr n,mul_nonneg (pow_nonneg hr m) (pow_nonneg hr n)]
    have hh₀ : dist (X (dyadicRound (m+1+n) t)) (X (dyadicRound (m+n) t))≤r^(m+n+1) := by
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    exact hh₀.trans hh'
  have hlim := (tendsto_dyadicLimit hr hr1 hg t).comp (tendsto_add_atTop_nat n)
  simpa using dist_le_of_le_geometric_of_tendsto₀ r (r^n) hr1 (fun m => by simpa only [comp_apply,dist_comm] using hs m) hlim
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ}

lemma dyadic_increment_tail (hX : IsPreBrownianReal X P) (n k : ℕ) {ε : ℝ} (hε : 0<ε) :
    P {ω | ε < dist (X (dyadicPoint n (k+1)) ω) (X (dyadicPoint n k) ω)} ≤
      ENNReal.ofReal (gaussianFourth*((1/2:ℝ)^n)^2/ε^4) := by
  have hv : nndist (dyadicPoint n (k+1)).1 (dyadicPoint n k).1=(1/2:ℝ≥0)^n := by
    apply NNReal.coe_injective
    rw [coe_nndist,Real.dist_eq,abs_of_nonneg]
    · exact dyadicPoint_succ n k
    · exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (dyadicPoint_mono n (Nat.le_succ k)))
  have hl := hX.hasLaw_sub (dyadicPoint n (k+1)) (dyadicPoint n k)
  rw [hv] at hl
  simpa only [Pi.sub_apply,Real.dist_eq,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
    NNReal.coe_ofNat] using fourth_tail_bound hl hε

def dyadicBad (X : ℝ≥0 → Ω → ℝ) (N n : ℕ) : Set Ω :=
  {ω | ∃ k<N*2^n, (9/10:ℝ)^n < dist (X (dyadicPoint n (k+1)) ω) (X (dyadicPoint n k) ω)}

lemma dyadicBad_measure (hX : IsPreBrownianReal X P) (N n : ℕ) :
    P (dyadicBad X N n) ≤ ENNReal.ofReal (gaussianFourth*N) * ENNReal.ofReal (5000/6561:ℝ)^n := by
  classical
  have he : dyadicBad X N n=⋃ k∈Finset.range (N*2^n),
      {ω | (9/10:ℝ)^n < dist (X (dyadicPoint n (k+1)) ω) (X (dyadicPoint n k) ω)} := by
    ext ω
    simp [dyadicBad]
  rw [he]
  apply (measure_biUnion_finset_le _ _).trans
  calc
    (∑ k∈Finset.range (N*2^n), P {ω | (9/10:ℝ)^n <
      dist (X (dyadicPoint n (k+1)) ω) (X (dyadicPoint n k) ω)}) ≤
        ∑ _k∈Finset.range (N*2^n), ENNReal.ofReal (gaussianFourth*((1/2:ℝ)^n)^2/((9/10:ℝ)^n)^4) := by
      exact Finset.sum_le_sum (fun k _ => dyadic_increment_tail hX n k (by positivity))
    _ = ENNReal.ofReal (gaussianFourth*N) * ENNReal.ofReal (5000/6561:ℝ)^n := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      rw [←ENNReal.ofReal_pow (by norm_num),←ENNReal.ofReal_mul (mul_nonneg gaussianFourth_nonneg (Nat.cast_nonneg N)),
        ←ENNReal.ofReal_natCast (N*2^n),←ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      rw [←pow_mul,←pow_mul,show n*2=2*n from Nat.mul_comm _ _,
        show n*4=4*n from Nat.mul_comm _ _,pow_mul,pow_mul]
      have halg (a b c d e : ℝ) : d*a^n*(c*b^n/e^n)=c*d*(a*(b/e))^n := by
        rw [mul_pow,div_pow]
        ring
      convert halg 2 ((1/2:ℝ)^2) gaussianFourth N ((9/10:ℝ)^4) using 1; norm_num

lemma ae_dyadicGood (hX : IsPreBrownianReal X P) :
    ∀ᵐ ω ∂P, DyadicGood (9/10:ℝ) (fun t => X t ω) := by
  have hN (N : ℕ) : ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n≥n₀, ω∉dyadicBad X N n := by
    apply (ae_eventually_notMem (s:=dyadicBad X N) ?_).mono
    · intro ω hω
      exact eventually_atTop.mp hω
    · apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum (dyadicBad_measure hX N))
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (tsum_geometric_lt_top.mpr (by norm_num)).ne
  filter_upwards [ae_all_iff.mpr hN] with ω hω
  intro N
  obtain ⟨n₀,hn₀⟩ := hω N
  refine ⟨n₀,fun n hn k hk => ?_⟩
  exact le_of_not_gt (fun h => hn₀ n hn ⟨k,hk,h⟩)
end BrownianConstruction

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology ENNReal NNReal
namespace BrownianConstruction

lemma dyadicIndex_neighbors (n : ℕ) {s t : ℝ≥0}
    (hst : dist s t<(1/2:ℝ)^n) :
    dyadicIndex n s≤dyadicIndex n t+1 ∧ dyadicIndex n t≤dyadicIndex n s+1 := by
  have one {s t : ℝ≥0} (h : dist s t<(1/2:ℝ)^n) : dyadicIndex n s≤dyadicIndex n t+1 := by
    have ht := lt_dyadicRound_add n t
    have hs : (s:ℝ)<(dyadicRound n t:ℝ)+2*(1/2:ℝ)^n := by
      have hh : |(s:ℝ)-t|<(1/2:ℝ)^n := h
      have ht' : (t:ℝ)<(dyadicRound n t:ℝ)+(1/2:ℝ)^n := by exact_mod_cast ht
      linarith [(abs_lt.mp hh).2]
    have hh : (2:ℝ≥0)^n*s < (dyadicIndex n t:ℝ≥0)+2 := by
      apply NNReal.coe_lt_coe.mp
      change (2:ℝ)^n*(s:ℝ)<(dyadicIndex n t:ℝ)+2
      have hp : (0:ℝ)<2^n := by positivity
      have hh := mul_lt_mul_of_pos_left hs hp
      have he : (2:ℝ)^n*((dyadicRound n t:ℝ)+2*(1/2:ℝ)^n)=(dyadicIndex n t:ℝ)+2 := by
        simp only [dyadicRound,dyadicPoint,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_pow,
          NNReal.coe_ofNat,one_div_pow]
        field_simp
      rwa [he] at hh
    have hi : dyadicIndex n s<dyadicIndex n t+2 := (Nat.floor_lt (show 0 ≤ (2:ℝ≥0)^n*s from bot_le)).mpr (by exact_mod_cast hh)
    omega
  exact ⟨one hst,one (by simpa only [dist_comm] using hst)⟩

lemma nearby_round_bound {r : ℝ} (hr : 0≤r) {X : ℝ≥0 → ℝ} {N n : ℕ}
    (hg : ∀ k<N*2^n, dist (X (dyadicPoint n (k+1))) (X (dyadicPoint n k))≤r^n)
    {s t : ℝ≥0} (hs : s<N) (ht : t<N) (hst : dist s t<(1/2:ℝ)^n) :
    dist (X (dyadicRound n s)) (X (dyadicRound n t))≤r^n := by
  have hn := dyadicIndex_neighbors n hst
  have hi (s : ℝ≥0) (hs : s<N) : dyadicIndex n s<N*2^n := by
    apply (Nat.floor_lt (show 0 ≤ (2:ℝ≥0)^n*s from bot_le)).mpr
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_comm] using
      mul_lt_mul_of_pos_left hs (show 0<(2:ℝ≥0)^n by positivity)
  have cases : dyadicIndex n s=dyadicIndex n t ∨ dyadicIndex n s=dyadicIndex n t+1 ∨
      dyadicIndex n t=dyadicIndex n s+1 := by omega
  rcases cases with h|h|h
  · simp only [dyadicRound,h,dist_self]
    positivity
  · simp only [dyadicRound,h]
    exact hg _ (hi t ht)
  · simp only [dyadicRound,h]
    exact (by simpa only [dist_comm] using hg _ (hi s hs))

lemma continuous_dyadicLimit {r : ℝ} (hr : 0≤r) (hr1 : r<1)
    {X : ℝ≥0 → ℝ} (hg : DyadicGood r X) : Continuous (dyadicLimit X) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨N,hN⟩ := exists_nat_gt ((t:ℝ)+1)
  obtain ⟨n₀,hn₀⟩ := hg N
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hseq : Tendsto (fun n : ℕ => (2/(1-r)+1)*r^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul (2/(1-r)+1)
  obtain ⟨n,hn,he⟩ := ((eventually_ge_atTop n₀).and (hseq.eventually (gt_mem_nhds hε))).exists
  refine ⟨min 1 ((1/2:ℝ)^n),lt_min (by norm_num) (by positivity),?_⟩
  intro s hs
  have htN : t<(N:ℝ≥0) := by exact_mod_cast (by linarith : (t:ℝ)<N)
  have hsN : s<(N:ℝ≥0) := by
    have hh : |(s:ℝ)-t|<1 := hs.trans_le (min_le_left _ _)
    exact_mod_cast (by linarith [(abs_lt.mp hh).2] : (s:ℝ)<N)
  have htail := fun m (hm : m≥n) => hn₀ m (hn.trans hm)
  have h1 := dyadicLimit_error hr hr1 hg htail hsN
  have h2 := dyadicLimit_error hr hr1 hg htail htN
  have h3 := nearby_round_bound hr (hn₀ n hn) hsN htN (hs.trans_le (min_le_right _ _))
  have htriangle := dist_triangle4 (dyadicLimit X s) (X (dyadicRound n s))
    (X (dyadicRound n t)) (dyadicLimit X t)
  rw [dist_comm (dyadicLimit X s) (X (dyadicRound n s))] at htriangle
  calc
    dist (dyadicLimit X s) (dyadicLimit X t) ≤ r^n/(1-r)+r^n+r^n/(1-r) := by linarith
    _ = (2/(1-r)+1)*r^n := by ring
    _ < ε := he
end BrownianConstruction

end

end OAI
