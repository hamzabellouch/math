import Mathlib
import OAI.Probability.SKSupport.Foundations.Taylor1Bound
import OAI.Probability.SKSupport.Control.GridApprox

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open WeakIto Heat Nonuniform

def approxMesh (n : ℕ) : ℝ≥0 := ((n+1:ℕ):ℝ≥0)⁻¹

lemma approxMesh_pos (n : ℕ) : 0 < approxMesh n := by unfold approxMesh; positivity

lemma approxMesh_horizon (n : ℕ) : ((n+1:ℕ):ℝ)*approxMesh n = 1 := by
  simp only [approxMesh,NNReal.coe_inv,NNReal.coe_natCast]
  exact mul_inv_cancel₀ (by positivity)

lemma approxMesh_limit : Tendsto (fun n => (approxMesh n:ℝ)) atTop (𝓝 0) := by
  simpa only [approxMesh,NNReal.coe_inv,NNReal.coe_natCast,Nat.cast_add,Nat.cast_one,NNReal.coe_add,NNReal.coe_one,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma sample_mem (n j : ℕ) (hj : j < n+1) : (j:ℝ)*approxMesh n ∈ Ico (0:ℝ) 1 := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) (approxMesh n).coe_nonneg,?_⟩
  rw [← approxMesh_horizon n]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hj) (by exact_mod_cast approxMesh_pos n)

def approxCoeff (γ : OrderParameter) (n j : ℕ) : ℝ≥0 :=
  if hj : j < n+1 then
    Real.toNNReal (γ.val ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩) else 0

def approxGamma (γ : OrderParameter) (n : ℕ) : ℝ → ℝ :=
  finiteCoeff (approxCoeff γ n) (approxMesh n) (n+1) 0

lemma approxCoeff_eq (γ : OrderParameter) (n j : ℕ) (hj : j < n+1) :
    (approxCoeff γ n j:ℝ) = γ.val ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩ := by
  unfold approxCoeff
  rw [dite_eq_left hj,Real.coe_toNNReal _ (γ.nonneg _)]

lemma approxGamma_samples (γ : OrderParameter) (n : ℕ) (t : Time) :
    ∃ (j : ℕ) (hj : j < n+1), approxGamma γ n t = γ.val ⟨(j:ℝ)*approxMesh n,sample_mem n j hj⟩ ∧
      (j:ℝ)*approxMesh n ≤ t ∧ (t:ℝ) ≤ ((j+1:ℕ):ℝ)*approxMesh n := by
  obtain ⟨j,hj,he,hl,hu⟩ := finiteCoeff_sample (approxCoeff γ n) (approxMesh_pos n)
    (n+1) 0 t.property.1 (by rw [approxMesh_horizon]; exact t.property.2.le) (by omega)
  refine ⟨j,hj,?_,hl,hu⟩
  simpa only [approxGamma,Nat.zero_add,approxCoeff_eq γ n j hj] using he

lemma approxGamma_bounds (γ : OrderParameter) (n : ℕ) (t : Time) :
    0 ≤ approxGamma γ n t ∧ approxGamma γ n t ≤ γ.val t := by
  obtain ⟨j,hj,he,hl,hu⟩ := approxGamma_samples γ n t
  rw [he]
  exact ⟨γ.nonneg _,γ.monotone hl⟩

lemma approxGamma_tendsto (γ : OrderParameter) (t : Time) (ht : ContinuousAt γ.val t) :
    Tendsto (fun n => approxGamma γ n t) atTop (𝓝 (γ.val t)) := by
  choose j hj he hl hu using fun n => approxGamma_samples γ n t
  let q (n : ℕ) : Time := ⟨(j n:ℝ)*approxMesh n,sample_mem n (j n) (hj n)⟩
  have hq : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 (t:ℝ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => (t:ℝ)-(approxMesh n:ℝ)) atTop (𝓝 (t:ℝ)) by
        simpa only [sub_zero] using tendsto_const_nhds.sub approxMesh_limit)
      tendsto_const_nhds
    · intro n
      have hh := hu n
      push_cast at hh
      dsimp only [q]
      nlinarith
    · exact hl
  have hqt : Tendsto q atTop (𝓝 t) := tendsto_subtype_rng.mpr hq
  have hh := ht.tendsto.comp hqt
  convert hh using 1
  funext n
  exact he n

lemma OrderParameter.ae_continuous (γ : OrderParameter) :
    ∀ᵐ s : ℝ, ∀ hs : s ∈ Ico (0:ℝ) 1, ContinuousAt γ.val ⟨s,hs⟩ := by
  have hc := γ.monotone.countable_not_continuousAt.image (fun t : Time => (t:ℝ))
  have hz := hc.measure_zero volume
  have ha : ∀ᵐ s : ℝ, s ∉ (fun t : Time => (t:ℝ)) '' {t | ¬ContinuousAt γ.val t} :=
    (ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hz))
  filter_upwards [ha] with s hs hmem
  by_contra hn
  exact hs ⟨⟨s,hmem⟩,hn,rfl⟩

lemma approxGamma_L1 (γ : OrderParameter) :
    Tendsto (fun n => ∫ s in (0:ℝ)..1, |approxGamma γ n s-extend γ.val s|)
      atTop (𝓝 0) := by
  have hint : ∀ n, AEStronglyMeasurable (fun s => |approxGamma γ n s-extend γ.val s|)
      (volume.restrict (Ioo (0:ℝ) 1)) := fun n =>
    ((measurable_finiteCoeff _ _ _ _).sub γ.measurable_extend).abs.aestronglyMeasurable
  have hb : ∀ n, ∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖|approxGamma γ n s-extend γ.val s|‖ ≤ extend γ.val s := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hm : s ∈ Ico (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
    have hh := approxGamma_bounds γ n ⟨s,hm⟩
    rw [Real.norm_eq_abs,abs_abs,show extend γ.val s = γ.val ⟨s,hm⟩ by simp [extend,hm]]
    rw [abs_of_nonpos (sub_nonpos.mpr hh.2)]
    linarith [hh.1]
  have hlim : ∀ᵐ s ∂volume.restrict (Ioo (0:ℝ) 1),
      Tendsto (fun n => |approxGamma γ n s-extend γ.val s|) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      (γ.ae_continuous).filter_mono (ae_mono Measure.restrict_le_self)] with s hs hc
    have hm : s ∈ Ico (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
    have hh := (approxGamma_tendsto γ ⟨s,hm⟩ (hc hm)).sub (tendsto_const_nhds (x := γ.val ⟨s,hm⟩))
    have he : extend γ.val s = γ.val ⟨s,hm⟩ := by simp [extend,hm]
    simpa only [he,sub_self,abs_zero] using hh.abs
  have hh := tendsto_integral_of_dominated_convergence (extend γ.val) hint
    γ.integrable.integrableOn hb hlim
  simp only [integral_zero] at hh
  convert hh using 1
  funext n
  exact intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1) |>.trans
    (integral_Ioc_eq_integral_Ioo)

end ZeroTemperatureSK

end
end
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
namespace ZeroTemperatureSK.Heat

lemma uniformCauchySeq_deriv_of_bound {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 2 (f n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, |deriv (deriv (f n)) x| ≤ C)
    (hlim : TendstoUniformly f g atTop) :
    UniformCauchySeqOn (fun n => deriv (f n)) atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  rw [Metric.tendstoUniformly_iff] at hlim
  intro ε hε
  let h : ℝ := ε / (2*C+1)
  have hh : 0 < h := div_pos hε (by positivity)
  have hδ : 0 < ε*h/8 := by positivity
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim (ε*h/8) hδ)
  refine ⟨N,fun m hm n hn x _ => ?_⟩
  have hA : ∀ y, |(f m-f n) y| ≤ 2*(ε*h/8) := by
    intro y
    have hm' := hN m hm y
    have hn' := hN n hn y
    simp only [Real.dist_eq] at hm' hn'
    calc
      _ = |(g y-f n y)-(g y-f m y)| := by simp only [Pi.sub_apply]; congr 1; ring
      _ ≤ |g y-f n y|+|g y-f m y| := abs_sub _ _
      _ ≤ _ := by linarith
  have hd (y : ℝ) : deriv (f m-f n) y = deriv (f m) y-deriv (f n) y :=
    deriv_sub ((hf m).differentiable (by norm_num) y) ((hf n).differentiable (by norm_num) y)
  have hdd (y : ℝ) : deriv (deriv (f m-f n)) y =
      deriv (deriv (f m)) y-deriv (deriv (f n)) y := by
    rw [show deriv (f m-f n) = deriv (f m)-deriv (f n) from funext hd]
    exact deriv_sub
      (by simpa only [iteratedDeriv_one] using (hf m).differentiable_iteratedDeriv 1 (by norm_num) y)
      (by simpa only [iteratedDeriv_one] using (hf n).differentiable_iteratedDeriv 1 (by norm_num) y)
  have hdC : ∀ y, |deriv (deriv (f m-f n)) y| ≤ 2*C := by
    intro y
    rw [hdd]
    exact (abs_sub _ _).trans (by linarith [hb m y,hb n y])
  have hi := derivative_interpolation ((hf m).sub (hf n)) hA hdC hh x
  have hc : h*(2*C) < ε := by
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*C+1)).mpr
    nlinarith
  have he : 2*(2*(ε*h/8))/h = ε/2 := by field_simp; ring
  change |deriv (f m-f n) x| ≤ 2*(2*(ε*h/8))/h+h*(2*C)/2 at hi
  rw [he,hd] at hi
  rw [Real.dist_eq]
  linarith

theorem tendstoUniformly_deriv_of_bound {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 2 (f n)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, |deriv (deriv (f n)) x| ≤ C)
    (hlim : TendstoUniformly f g atTop) :
    Differentiable ℝ g ∧
      TendstoUniformly (fun n => deriv (f n)) (deriv g) atTop := by
  have hc := uniformCauchySeq_deriv_of_bound hf hC hb hlim
  let d : ℝ → ℝ := fun x => atTop.limUnder (fun n => deriv (f n) x)
  have hd : TendstoUniformly (fun n => deriv (f n)) d atTop := by
    rw [← tendstoUniformlyOn_univ]
    exact hc.tendstoUniformlyOn_of_tendsto (fun x _ => (hc.cauchySeq (mem_univ x)).tendsto_limUnder)
  have hg (x : ℝ) : HasDerivAt g (d x) x :=
    hasDerivAt_of_tendstoUniformly hd (Filter.Eventually.of_forall
      (fun n x => ((hf n).differentiable (by norm_num) x).hasDerivAt)) hlim.tendsto_at x
  refine ⟨fun x => (hg x).differentiableAt, ?_⟩
  have he : deriv g = d := funext (fun x => (hg x).deriv)
  rwa [he]

lemma contDiff_iteratedDeriv_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m f) := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

theorem smooth_limit_of_uniform_derivative_bounds {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, |iteratedDeriv (m+2) (f n) x| ≤ C)
    (hlim : TendstoUniformly f g atTop) :
    ContDiff ℝ ∞ g ∧
      ∀ m : ℕ, TendstoUniformly (fun n => iteratedDeriv m (f n)) (iteratedDeriv m g) atTop := by
  have hconv (m : ℕ) :
      TendstoUniformly (fun n => iteratedDeriv m (f n)) (iteratedDeriv m g) atTop := by
    induction m with
    | zero => simpa only [iteratedDeriv_zero] using hlim
    | succ m ih =>
      obtain ⟨C,hC,hbC⟩ := hb m
      have hh := tendstoUniformly_deriv_of_bound
        (fun n => (contDiff_iteratedDeriv_infty (hf n) m).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
        hC (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbC) ih
      simpa only [iteratedDeriv_succ] using hh.2
  refine ⟨?_,hconv⟩
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _hm
  obtain ⟨C,hC,hbC⟩ := hb m
  exact (tendstoUniformly_deriv_of_bound
    (fun n => (contDiff_iteratedDeriv_infty (hf n) m).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    hC (by simpa only [show m+2=(m+1)+1 by omega,iteratedDeriv_succ] using hbC) (hconv m)).1

lemma iteratedDeriv_limit_bound {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} (m : ℕ) {C : ℝ}
    (hconv : TendstoUniformly (fun n => iteratedDeriv m (f n)) (iteratedDeriv m g) atTop)
    (hb : ∀ n x, |iteratedDeriv m (f n) x| ≤ C) (x : ℝ) :
    |iteratedDeriv m g x| ≤ C := by
  exact le_of_tendsto (hconv.tendsto_at x).abs (Filter.Eventually.of_forall (fun n => hb n x))

end ZeroTemperatureSK.Heat

end
end

end OAI
