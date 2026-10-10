import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityVelocity

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

lemma integral_abs_center_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ z, |f z-∫ w,f w ∂μ| ∂μ) ≤ Real.sqrt (Var[f;μ]) := by
  have hm := (hf.sub (memLp_const (∫ w,f w ∂μ))).norm
  have hh := integral_mul_sq_le hm (memLp_const (1:ℝ) (μ:=μ))
  simp only [Pi.sub_apply,Real.norm_eq_abs,mul_one,one_pow,integral_const,
    probReal_univ,smul_eq_mul,sq_abs] at hh
  rw [← variance_eq_integral hf.aemeasurable] at hh
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _)) (variance_nonneg f μ)).2 hh

lemma poincare_integral_norm_center {d : ℕ} {μ : Measure (Point d)}
    [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0≤β) (hP : HasPoincare μ β)
    (hm : Appell.HasMoments μ) :
    (∫ z, ‖z-∫ w,w ∂μ‖ ∂μ) ≤ (d:ℝ)*Real.sqrt β := by
  classical
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  have hi : Integrable (fun z : Point d => z) μ :=
    (Appell.HasGrowth.linear (ContinuousLinearMap.id ℝ (Point d))).integrable
      continuous_id.aestronglyMeasurable hm
  have hei (i : Fin d) : Integrable (fun z => |inner ℝ (b i) (z-∫ w,w ∂μ)|) μ :=
    ((innerSL ℝ (b i)).integrable_comp (hi.sub (integrable_const _))).norm
  have hv (i : Fin d) : (∫ z, |inner ℝ (b i) (z-∫ w,w ∂μ)| ∂μ) ≤ Real.sqrt β := by
    have hmi : MemLp (fun z => inner ℝ (b i) z) 2 μ :=
      (Appell.HasGrowth.linear (innerSL ℝ (b i))).memLp (by fun_prop) hm
    have hp := hP.lipschitz_variance hβ (innerSL ℝ (b i)).contDiff
      (innerSL ℝ (b i)).lipschitzWith hmi
    simp only [coe_nnnorm,innerSL_apply_norm,b.norm_eq_one,one_pow,mul_one] at hp
    have hh := (integral_abs_center_le_sqrt hmi).trans (Real.sqrt_le_sqrt hp)
    simpa only [inner_sub_right,integral_inner hi] using hh
  calc
    _ ≤ ∫ z, ∑ i : Fin d, |inner ℝ (b i) (z-∫ w,w ∂μ)| ∂μ := by
      apply integral_mono (hi.sub (integrable_const _)).norm (integrable_finsetSum _ (fun i _ => hei i))
      intro z
      change ‖z-∫ w,w ∂μ‖ ≤ _
      calc
        _ = ‖∑ i : Fin d, inner ℝ (b i) (z-∫ w,w ∂μ) • b i‖ := by
          exact congrArg norm (by simpa only [b.repr_apply_apply] using (b.sum_repr (z-∫ w,w ∂μ)).symm)
        _ ≤ ∑ i : Fin d, ‖inner ℝ (b i) (z-∫ w,w ∂μ) • b i‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_smul,b.norm_eq_one,mul_one,Real.norm_eq_abs]
    _ = ∑ i : Fin d, ∫ z, |inner ℝ (b i) (z-∫ w,w ∂μ)| ∂μ := integral_finsetSum _ (fun i _ => hei i)
    _ ≤ ∑ _i : Fin d, Real.sqrt β := Finset.sum_le_sum (fun i _ => hv i)
    _ = _ := by simp

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

lemma norm_integral_sub_map_mean_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure (Point d)} [IsProbabilityMeasure μ]
    {f : Point d → E} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hi : Integrable (fun z : Point d => z) μ) :
    ‖(∫ z,f z ∂μ)-f (∫ z,z ∂μ)‖ ≤ (L:ℝ)*(∫ z,‖z-∫ w,w ∂μ‖ ∂μ) := by
  have hfi : Integrable f μ := integrable_lipschitz_comp_of_integrable hi hf
  have hd := hi.sub (integrable_const (∫ w,w ∂μ))
  have he : (∫ z,f z-f (∫ w,w ∂μ) ∂μ)=(∫ z,f z ∂μ)-f (∫ w,w ∂μ) := by
    rw [integral_sub hfi (integrable_const _),integral_const,probReal_univ,one_smul]
  rw [← he]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono (hfi.sub (integrable_const _)).norm (hd.norm.const_mul _)
  intro z
  simpa only [dist_eq_norm,Pi.sub_apply] using hf.dist_le_mul z (∫ w,w ∂μ)

lemma conditionalFieldMean_center_error {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r
      (ρ • y-((1-ρ^2)*r) • conditionalFieldMean F x r ρ y)‖ ≤
      ((lam:ℝ)*r)*((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2))) := by
  let := conditionalLaw_probability hF x hr hl hρ0 hρ1 y
  have hh := norm_integral_sub_map_mean_le (primitiveField_lipschitz hF x hr)
    (conditional_identity_integrable hF x hr hl hρ0 hρ1 y)
  have hb := poincare_integral_norm_center
    (mul_nonneg (by positivity) (probability_time hρ0 hρ1).1.le)
    (conditionalLaw_hasPoincare hF x hr hl hρ0 hρ1 y)
    (conditionalLaw_hasExpMoments hF x hr hl hρ0 hρ1 y).hasMoments
  have hg := hh.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg lam.coe_nonneg hr))
  simpa only [conditional_mean_identity hF x hr hl hρ0 hρ1 y,NNReal.coe_mul,NNReal.coe_mk,conditionalFieldMean] using hg

lemma conditionalFieldMean_error {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r y‖ ≤
      ((lam:ℝ)*r)*((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+
      ((lam:ℝ)*r)*((1-ρ)*‖y‖+((1-ρ^2)*r)*‖conditionalFieldMean F x r ρ y‖) := by
  let M := conditionalFieldMean F x r ρ y
  let z := ρ • y-((1-ρ^2)*r) • M
  have he := conditionalFieldMean_center_error hF x hr hl hρ0 hρ1 y
  have hh := (primitiveField_lipschitz hF x hr).dist_le_mul z y
  rw [dist_eq_norm,dist_eq_norm] at hh
  have hb : ‖z-y‖≤(1-ρ)*‖y‖+((1-ρ^2)*r)*‖M‖ := by
    have hz : z-y=-( (1-ρ) • y+((1-ρ^2)*r) • M) := by
      dsimp [z]; simp only [sub_smul,one_smul]; abel
    rw [hz,norm_neg]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul,norm_smul,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_nonneg (by linarith),abs_of_nonneg
        (mul_nonneg (probability_time hρ0 hρ1).1.le hr)])
  calc
    _ ≤ ‖M-primitiveField F x r z‖+‖primitiveField F x r z-primitiveField F x r y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add he (hh.trans (mul_le_mul_of_nonneg_left hb (mul_nonneg lam.coe_nonneg hr)))

end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory

lemma conditionalFieldMean_norm_bound {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y‖ ≤
      2*(‖primitiveField F x r y‖+((lam:ℝ)*r)*
        ((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+((lam:ℝ)*r)*(1-ρ)*‖y‖) := by
  have hh := conditionalFieldMean_error hF x hr hl hρ0 hρ1 y
  have ht := norm_le_norm_add_norm_sub' (conditionalFieldMean F x r ρ y) (primitiveField F x r y)
  have hc : ((lam:ℝ)*r)*((1-ρ^2)*r)≤1/2 := by
    have hb := mul_le_mul_of_nonneg_left (probability_time hρ0 hρ1).2
      (mul_nonneg lam.coe_nonneg (sq_nonneg r))
    nlinarith
  have hb := mul_le_mul_of_nonneg_right hc (norm_nonneg (conditionalFieldMean F x r ρ y))
  nlinarith

lemma conditionalFieldMean_endpoint_error {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    ‖conditionalFieldMean F x r ρ y-primitiveField F x r y‖ ≤
      ((lam:ℝ)*r)*((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+
      ((lam:ℝ)*r)*((1-ρ)*‖y‖+((1-ρ^2)*r)*
        (2*(‖primitiveField F x r y‖+((lam:ℝ)*r)*
          ((d:ℝ)*Real.sqrt ((Real.pi^2/2)*(1-ρ^2)))+((lam:ℝ)*r)*(1-ρ)*‖y‖))) := by
  apply (conditionalFieldMean_error hF x hr hl hρ0 hρ1 y).trans
  gcongr
  · exact mul_nonneg (probability_time hρ0 hρ1).1.le hr
  · exact conditionalFieldMean_norm_bound hF x hr hl hρ0 hρ1 y
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory Filter
open scoped Topology

lemma conditionalFieldMean_tendsto_endpoint {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) {ι : Type*} {l : Filter ι} {ρ : ι → ℝ}
    {y : ι → Point d} {y₀ : Point d} (ht : Tendsto ρ l (𝓝 1)) (hy : Tendsto y l (𝓝 y₀))
    (hρ : ∀ᶠ i in l,0≤ρ i ∧ ρ i<1) :
    Tendsto (fun i => conditionalFieldMean F x r (ρ i) (y i)) l (𝓝 (primitiveField F x r y₀)) := by
  have hg := (primitiveField_contDiff hF x r).continuous.continuousAt.tendsto.comp hy
  have he : Tendsto (fun i => conditionalFieldMean F x r (ρ i) (y i)-primitiveField F x r (y i)) l (𝓝 0) := by
    apply squeeze_zero_norm' (hρ.mono (fun i hi => conditionalFieldMean_endpoint_error hF x hr hl hi.1 hi.2 (y i)))
    have hsq : Tendsto (fun i => 1-ρ i^2) l (𝓝 0) := by
      simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (ht.pow 2)
    have hs : Tendsto (fun i => Real.sqrt ((Real.pi^2/2)*(1-ρ i^2))) l (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hsq).sqrt
    convert! ((tendsto_const_nhds.mul (tendsto_const_nhds.mul hs)).add
      (tendsto_const_nhds.mul (((tendsto_const_nhds.sub ht).mul hy.norm).add
        ((hsq.mul tendsto_const_nhds).mul
          (tendsto_const_nhds.mul ((hg.norm.add
            (tendsto_const_nhds.mul (tendsto_const_nhds.mul hs))).add
              ((tendsto_const_nhds.mul (tendsto_const_nhds.sub ht)).mul hy.norm))))))) using 1; simp
  simpa only [Function.comp_apply,sub_add_cancel,zero_add] using he.add hg
end LogConcaveSampling
namespace LogConcaveSampling
open Set Filter Function
open scoped Topology

def closedFieldMean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) : Point d :=
  if ρ<1 then conditionalFieldMean F x r ρ y else primitiveField F x r y

lemma closedFieldMean_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) :
    Continuous (fun p : Icc (0:ℝ) 1 × Point d => closedFieldMean F x r p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have ht : Continuous (fun p : Icc (0:ℝ) 1 × Point d => (p.1:ℝ)) := continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun p : Icc (0:ℝ) 1 × Point d => p.2) := continuous_snd
  by_cases hp : (p.1:ℝ)<1
  · have hs := (conditionalFieldMean_joint_smooth hF x hr (by linarith) ((p.1:ℝ),p.2)
      (by have ha := (probability_time p.1.2.1 hp).1; linarith)).continuousAt
    have he : (fun q : Icc (0:ℝ) 1 × Point d => closedFieldMean F x r q.1 q.2) =ᶠ[𝓝 p]
        (fun q => conditionalFieldMean F x r q.1 q.2) := by
      filter_upwards [ht.continuousAt (eventually_lt_nhds hp)] with q hq
      change (q.1:ℝ)<1 at hq
      simp only [closedFieldMean,ite_eq_left hq]
    exact ((hs.comp (f:=fun q : Icc (0:ℝ) 1 × Point d => ((q.1:ℝ),q.2)) (ht.continuousAt.prodMk hy.continuousAt))).congr_of_eventuallyEq he
  · have hp1 : (p.1:ℝ)=1 := le_antisymm p.1.2.2 (le_of_not_gt hp)
    change Tendsto _ (𝓝 p) (𝓝 (closedFieldMean F x r p.1 p.2))
    rw [closedFieldMean,ite_eq_right hp]
    apply Filter.Tendsto.if
    · apply conditionalFieldMean_tendsto_endpoint hF x hr hl
      · simpa only [hp1] using (ht.continuousAt (x:=p)).tendsto.mono_left inf_le_left
      · exact hy.continuousAt.tendsto.mono_left inf_le_left
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact ⟨q.1.2.1,hq⟩
    · exact ((primitiveField_contDiff hF x r).continuous.comp hy).continuousAt.tendsto.mono_left inf_le_left

def fullProbabilityVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r t : ℝ)
    (z : Point d) : Point d :=
  -r • closedFieldMean F x r (projIcc 0 1 (by norm_num) t) z

lemma fullProbabilityVelocity_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) : Continuous (uncurry (fullProbabilityVelocity F x r)) := by
  have ht : Continuous (fun p : ℝ × Point d => projIcc (0:ℝ) 1 (by norm_num) p.1) :=
    continuous_projIcc.comp continuous_fst
  exact (continuous_const (y:=(-r:ℝ))).smul ((closedFieldMean_continuous hF x hr hl).comp
    (ht.prodMk continuous_snd))

lemma fullProbabilityVelocity_eq {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ)
    {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) (z : Point d) :
    fullProbabilityVelocity F x r t z=probabilityVelocity F x r t z := by
  simp only [fullProbabilityVelocity,projIcc_of_mem _ ⟨ht0,ht1.le⟩,closedFieldMean,ite_eq_left ht1,probabilityVelocity]

lemma fullProbabilityVelocity_endpoint {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r : ℝ) (z : Point d) : fullProbabilityVelocity F x r 1 z= -r • primitiveField F x r z := by
  simp [fullProbabilityVelocity,closedFieldMean]

lemma fullProbabilityVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (t : ℝ) :
    LipschitzWith ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩ (fullProbabilityVelocity F x r t) := by
  let s := projIcc 0 1 (by norm_num) t
  by_cases hs : (s:ℝ)<1
  · have he : fullProbabilityVelocity F x r t=probabilityVelocity F x r s := by
      funext z
      simp only [fullProbabilityVelocity,closedFieldMean,probabilityVelocity,s,ite_eq_left hs]
    rw [he]
    exact probabilityVelocity_lipschitz hF x hr hl ⟨s.2.1,le_rfl⟩ hs
  · have he : fullProbabilityVelocity F x r t=fun z => -r • primitiveField F x r z := by
      funext z
      simp only [fullProbabilityVelocity,closedFieldMean,s,ite_eq_right hs]
    rw [he]
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr]
    have hh := (primitiveField_lipschitz hF x hr).dist_le_mul u v
    rw [dist_eq_norm] at hh
    calc
      _ ≤ r*((lam:ℝ)*r*dist u v) := mul_le_mul_of_nonneg_left hh hr
      _ ≤ ((Real.pi^2/2)*(lam:ℝ)*r^2)*dist u v := by
        have hp : 1≤Real.pi^2/2 := by nlinarith [Real.pi_gt_three]
        have hnon : 0≤(lam:ℝ)*r^2*dist u v := by positivity
        nlinarith
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
