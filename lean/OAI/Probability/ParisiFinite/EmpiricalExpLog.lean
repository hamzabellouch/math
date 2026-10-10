import Mathlib
import OAI.Probability.ParisiFinite.HierarchyNumeratorNonneg

namespace OAI

/-! Empirical Exp Log. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def empiricalExpLog {r : ℕ} (u : Fin r → ℝ) : ℝ :=
  Real.log ((∑ i,Real.exp (u i))/(r:ℝ))

lemma empiricalExpLog_eq {r : ℕ} (hr : 0<r) (u : Fin r → ℝ) :
    empiricalExpLog u=logPartition u-Real.log (r:ℝ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  rw [empiricalExpLog,Real.log_div (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
    (Nat.cast_ne_zero.mpr hr.ne')]
  rfl

lemma integrable_empiricalExpLog {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {r : ℕ} (hr : 0<r) {f : Ω → Fin r → ℝ}
    (hf : ∀ i,Integrable (fun sample => f sample i) ν) :
    Integrable (fun sample => empiricalExpLog (f sample)) ν := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [empiricalExpLog_eq hr]
  exact (integrable_logPartition hf).sub (integrable_const _)

lemma empiricalExpLog_error {r : ℕ} (hr : 0<r) (u v : Fin r → ℝ) {t : ℝ} (ht : 0<t) :
    |empiricalExpLog u-empiricalExpLog v|≤
      t*((∑ i,(Real.exp (u i)-Real.exp (v i))^2)/(r:ℝ))+
      (((∑ i,Real.exp (-2*u i))/(r:ℝ))+((∑ i,Real.exp (-2*v i))/(r:ℝ)))/(2*t) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have hpos (w : Fin r → ℝ) : 0<(∑ i,Real.exp (w i))/(r:ℝ) :=
    div_pos (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty) (Nat.cast_pos.mpr hr)
  have hs : (((∑ i,Real.exp (u i))/(r:ℝ))-((∑ i,Real.exp (v i))/(r:ℝ)))^2≤
      (∑ i,(Real.exp (u i)-Real.exp (v i))^2)/(r:ℝ) := by
    rw [← sub_div,← Finset.sum_sub_distrib]
    simpa using (sum_div_card_sq_le_sum_sq_div_card (s:=Finset.univ)
      (f:=fun i : Fin r => Real.exp (u i)-Real.exp (v i)))
  have hinv (w : Fin r → ℝ) : ((∑ i,Real.exp (w i))/(r:ℝ))⁻¹^2≤
      (∑ i,Real.exp (-2*w i))/(r:ℝ) := by
    have hh := empiricalMean_inv_sq hr (fun i : Fin r => Real.exp (w i)) (fun i => Real.exp_pos _) id
    have he (i : Fin r) : (Real.exp (w i))⁻¹^2=Real.exp (-2*w i) := by
      rw [← Real.exp_neg,← Real.exp_nat_mul]
      congr 1
      ring
    simpa only [empiricalMean,id_eq,he] using hh
  exact (log_error_young (hpos u) (hpos v) ht).trans
    (add_le_add (mul_le_mul_of_nonneg_left hs ht.le)
      (div_le_div_of_nonneg_right (add_le_add (hinv u) (hinv v)) (by positivity)))

lemma integral_empiricalExpLog_error {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {r : ℕ} (hr : 0<r) {f g : Ω → Fin r → ℝ}
    (hf : ∀ i,Integrable (fun sample => f sample i) ν)
    (hg : ∀ i,Integrable (fun sample => g sample i) ν)
    (hd : ∀ i,Integrable (fun sample => (Real.exp (f sample i)-Real.exp (g sample i))^2) ν)
    (hfi : ∀ i,Integrable (fun sample => Real.exp (-2*f sample i)) ν)
    (hgi : ∀ i,Integrable (fun sample => Real.exp (-2*g sample i)) ν)
    {t : ℝ} (ht : 0<t) :
    |(∫ sample,empiricalExpLog (f sample) ∂ν)-(∫ sample,empiricalExpLog (g sample) ∂ν)|≤
      t*((∑ i,∫ sample,(Real.exp (f sample i)-Real.exp (g sample i))^2 ∂ν)/(r:ℝ))+
      (((∑ i,∫ sample,Real.exp (-2*f sample i) ∂ν)/(r:ℝ))+
       ((∑ i,∫ sample,Real.exp (-2*g sample i) ∂ν)/(r:ℝ)))/(2*t) := by
  rw [← integral_sub (integrable_empiricalExpLog hr hf) (integrable_empiricalExpLog hr hg)]
  have hnorm := norm_integral_le_integral_norm (fun sample => empiricalExpLog (f sample)-empiricalExpLog (g sample)) (μ:=ν)
  rw [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  have hd' := (integrable_finsetSum Finset.univ (fun i _ => hd i)).div_const (r:ℝ)
  have hf' := (integrable_finsetSum Finset.univ (fun i _ => hfi i)).div_const (r:ℝ)
  have hg' := (integrable_finsetSum Finset.univ (fun i _ => hgi i)).div_const (r:ℝ)
  have h := integral_mono
    ((integrable_empiricalExpLog hr hf).sub (integrable_empiricalExpLog hr hg)).norm
    ((hd'.const_mul t).add ((hf'.add hg').div_const (2*t)))
    (fun sample => by simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.sub_apply] using empiricalExpLog_error hr (f sample) (g sample) ht)
  simp only [Pi.add_apply,Pi.sub_apply] at h
  apply h.trans_eq
  rw [integral_add]
  · rw [integral_const_mul,integral_div,integral_div,integral_add hf' hg',integral_div,integral_div]
    simp_rw [integral_finsetSum _ (fun i _ => hd i),integral_finsetSum _ (fun i _ => hfi i),
      integral_finsetSum _ (fun i _ => hgi i)]
  · exact hd'.const_mul t
  · exact (hf'.add hg').div_const (2*t)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def clipField (M x : ℝ) : ℝ := max (-M) (min M x)

lemma clipField_abs_le {M : ℝ} (hM : 0≤M) (x : ℝ) : |clipField M x|≤|x| := by
  rw [abs_le]
  constructor
  · exact (le_min (by linarith [abs_nonneg x]) (neg_abs_le x)).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

lemma clipField_bounded {M : ℝ} (hM : 0≤M) (x : ℝ) : |clipField M x|≤M := by
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩

lemma continuous_clipField (M : ℝ) : Continuous (clipField M) := by
  unfold clipField
  fun_prop

lemma exp_clip_diff_sq_le {M : ℝ} (hM : 0≤M) (x : ℝ) :
    (Real.exp x-Real.exp (clipField M x))^2≤Real.exp (2* |x|) := by
  have h1 := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 := Real.exp_le_exp.mpr ((le_abs_self (clipField M x)).trans (clipField_abs_le hM x))
  have hab : |Real.exp x-Real.exp (clipField M x)|≤Real.exp |x| := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos x,Real.exp_pos (clipField M x)]
  have hs := sq_le_sq₀ (abs_nonneg _) (Real.exp_pos _).le |>.mpr hab
  rw [sq_abs,← Real.exp_nat_mul] at hs
  simpa using hs

lemma exp_neg_clip_le {M : ℝ} (hM : 0≤M) (x : ℝ) :
    Real.exp (-2*clipField M x)≤Real.exp (2* |x|) := by
  apply Real.exp_le_exp.mpr
  have hh := (abs_le.mp (clipField_abs_le hM x)).1
  linarith

lemma integrable_clip_exp_diff_sq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (he : Integrable (fun sample => Real.exp (2* |f sample|)) ν)
    {M : ℝ} (hM : 0≤M) :
    Integrable (fun sample => (Real.exp (f sample)-Real.exp (clipField M (f sample)))^2) ν := by
  apply he.mono' (by unfold clipField; exact ((Real.measurable_exp.comp hf).sub (Real.measurable_exp.comp ((measurable_const.max (measurable_const.min hf))))).pow_const 2 |>.aestronglyMeasurable)
  exact ae_of_all _ fun sample => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact exp_clip_diff_sq_le hM _

lemma integrable_neg_clip_exp {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (he : Integrable (fun sample => Real.exp (2* |f sample|)) ν)
    {M : ℝ} (hM : 0≤M) :
    Integrable (fun sample => Real.exp (-2*clipField M (f sample))) ν := by
  apply he.mono' (Real.measurable_exp.comp (((continuous_clipField M).measurable.comp hf).const_mul (-2))).aestronglyMeasurable
  exact ae_of_all _ fun sample => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact exp_neg_clip_le hM _

lemma clipped_exp_L2_tendsto {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (he : Integrable (fun sample => Real.exp (2* |f sample|)) ν) :
    Tendsto (fun m : ℕ => ∫ sample,(Real.exp (f sample)-Real.exp (clipField m (f sample)))^2 ∂ν)
      atTop (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun m : ℕ => ∫ sample,(Real.exp (f sample)-Real.exp (clipField m (f sample)))^2 ∂ν)
      atTop (𝓝 (∫ _ : Ω,(0:ℝ) ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun sample => Real.exp (2* |f sample|))
    · intro m; exact (integrable_clip_exp_diff_sq hf he (Nat.cast_nonneg m)).aestronglyMeasurable
    · exact he
    · intro m
      exact ae_of_all _ fun sample => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact exp_clip_diff_sq_le (Nat.cast_nonneg m) _
    · exact ae_of_all _ fun sample => by
        have hh := Real.continuous_exp.continuousAt.tendsto.comp (clip_tendsto (f sample))
        simpa only [Function.comp_apply,clipField,sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using ((tendsto_const_nhds (x:=Real.exp (f sample))).sub hh).pow 2
  simpa using ht

lemma integrable_exp_abs_field {d : ℕ} (s : Fin d → ℝ) (c : ℝ) :
    Integrable (fun z => Real.exp (c* |∑ k,s k*z k|)) (gaussianLaw (Fin d)) := by
  let A : Unit → Fin d → ℝ := fun _ => s
  apply ((integrable_exp_field A c ()).add (integrable_exp_field A (-c) ())).mono' (show Continuous (fun z : Fin d → ℝ => Real.exp (c* |∑ k,s k*z k|)) by fun_prop).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    change _≤Real.exp (c*(∑ k,s k*z k))+Real.exp (-c*(∑ k,s k*z k))
    rcases le_total 0 (∑ k,s k*z k) with hz | hz
    · rw [abs_of_nonneg hz]; exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hz]
      have hh : c*(-(∑ k,s k*z k))= -c*(∑ k,s k*z k) := by ring
      rw [hh]; exact le_add_of_nonneg_left (Real.exp_pos _).le

 

lemma integrable_exp_abs_lipschitz_field {d : ℕ} (s : Fin d → ℝ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (x c : ℝ) :
    Integrable (fun z => Real.exp (c* |f (x+∑ k,s k*z k)|)) (gaussianLaw (Fin d)) := by
  apply ((integrable_exp_abs_field s (|c| *(L:ℝ))).const_mul (Real.exp (|c| * |f x|))).mono'
    (Real.continuous_exp.comp ((hf.continuous.comp (by fun_prop)).abs.const_mul c)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := shift_norm_le hf x 1 (∑ k,s k*z k)
    simp only [one_mul,abs_one,mul_one] at hh
    have hh' := mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg (f (x+∑ k,s k*z k)))
    nlinarith [abs_nonneg c]

lemma integrable_lipschitz_field {d : ℕ} (s : Fin d → ℝ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (x : ℝ) :
    Integrable (fun z => f (x+∑ k,s k*z k)) (gaussianLaw (Fin d)) := by
  let A : Unit → Fin d → ℝ := fun _ => s
  have hi := (integrable_field A ()).abs.const_mul (L:ℝ)
  apply ((integrable_const |f x|).add hi).mono'
    (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    simp only [Function.comp_apply,Real.norm_eq_abs]
    have hh := shift_norm_le hf x 1 (∑ k,s k*z k)
    simpa only [one_mul,abs_one,mul_one,field,A,Pi.add_apply] using hh

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma scalarHierarchy_schedule {d : ℕ} (a v : Fin d → ℝ≥0) (β x : ℝ) :
    scalarHierarchy (fun k => (a k:ℝ)) (fun k => Real.sqrt (v k)) (terminal β) x=
      recursion β (List.ofFn (fun k => (a k,v k))) x := by
  induction d generalizing x with
  | zero => simp [scalarHierarchy,recursion]
  | succ d ih =>
    rw [List.ofFn_succ,recursion]
    change step _ _ _ x=step _ _ _ x
    congr 1
    funext y
    exact ih (fun k => a k.succ) (fun k => v k.succ) y

lemma gaussianHierarchy_cosh_schedule {d : ℕ} (a v : Fin d → ℝ≥0) {β : ℝ} (hβ : 0<β) (x : ℝ) :
    gaussianHierarchyRisk (fun k => (a k:ℝ))
      (fun z => Real.log (2*Real.cosh (β*(x+∑ k,Real.sqrt (v k)*z k))))=
    β*recursion β (List.ofFn (fun k => (a k*Real.toNNReal β,v k))) x := by
  have he (y : ℝ) : Real.log (2*Real.cosh (β*y))=β*terminal β y := by
    unfold terminal
    field_simp
  simp_rw [he]
  rw [gaussianHierarchyRisk_sum _ _ (fun y => β*terminal β y),scalarHierarchy_mul_const _ _ hβ.ne']
  congr 1
  simpa only [NNReal.coe_mul,Real.coe_toNNReal β hβ.le] using scalarHierarchy_schedule (fun k => a k*Real.toNNReal β) v β x

lemma step_affine (a s c b x : ℝ) :
    step a s (fun y => c*y+b) x=c*x+b+a*c^2*s^2/2 := by
  by_cases ha : a=0
  · simp only [step,ha,logMean_zero,zero_mul,zero_div,add_zero]
    have he (z : ℝ) : c*(x+s*z)+b=(c*x+b)+(c*s)*z := by ring
    simp_rw [he]
    have hi : Integrable (fun z : ℝ => z) (gaussianReal 0 1) :=
      MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ:=0) (v:=1) 1)
    rw [integral_add (integrable_const _) (hi.const_mul _),integral_const_mul]
    simp [integral_id_gaussianReal]
  · have he (z : ℝ) : a*(c*(x+s*z)+b)=a*(c*x+b)+(a*c*s)*z := by ring
    simp only [step,logMean,ha,↓reduceIte]
    simp_rw [he,Real.exp_add]
    rw [integral_const_mul,integral_exp_linear,← Real.exp_add,Real.log_exp]
    field_simp

lemma scalarHierarchy_affine {d : ℕ} (a s : Fin d → ℝ) (c b x : ℝ) :
    scalarHierarchy a s (fun y => c*y+b) x=c*x+b+c^2/2*(∑ k,a k*(s k)^2) := by
  induction d generalizing b x with
  | zero => simp [scalarHierarchy]
  | succ d ih =>
    change step (a 0) (s 0) _ x=_
    have he : scalarHierarchy (fun k => a k.succ) (fun k => s k.succ) (fun y => c*y+b)=
        (fun y => c*y+(b+c^2/2*(∑ k : Fin d,a k.succ*(s k.succ)^2))) := by
      funext y
      rw [ih]
      ring
    rw [he,step_affine,Fin.sum_univ_succ]
    ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def hierarchyFieldValue {d : ℕ} (μ : ProbabilityMeasure OverlapArray) (q : Fin (d+2) → ℝ)
    (r : ℕ) (f : (Fin (d+1) → ℝ) → ℝ) : ℝ :=
  ∫ sample,empiricalExpLog (fun i : Fin r => f (sample i)) ∂hierarchySampleLaw μ q r

lemma hierarchyField_clip_error {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {r : ℕ} (hr : 0<r)
    {f : (Fin (d+1) → ℝ) → ℝ} (hf : Measurable f) (hfi : Integrable f (gaussianLaw (Fin (d+1))))
    (he : Integrable (fun z => Real.exp (2* |f z|)) (gaussianLaw (Fin (d+1))))
    {M t : ℝ} (hM : 0≤M) (ht : 0<t) :
    |hierarchyFieldValue μ q r f-hierarchyFieldValue μ q r (fun z => clipField M (f z))|≤
      t*(∫ z,(Real.exp (f z)-Real.exp (clipField M (f z)))^2 ∂gaussianLaw (Fin (d+1)))+
      (∫ z,Real.exp (2* |f z|) ∂gaussianLaw (Fin (d+1)))/t := by
  let := hierarchySampleLaw_probability hG hgg hu q hq h0 h1 hr
  have hgc : Measurable (fun z => clipField M (f z)) := (continuous_clipField M).measurable.comp hf
  have hgi : Integrable (fun z => clipField M (f z)) (gaussianLaw (Fin (d+1))) := by
    apply hfi.abs.mono' hgc.aestronglyMeasurable
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using clipField_abs_le hM (f z)
  have hd := integrable_clip_exp_diff_sq hf he hM
  have hneg : Integrable (fun z => Real.exp (-2*f z)) (gaussianLaw (Fin (d+1))) := by
    apply he.mono' (Real.measurable_exp.comp (hf.const_mul (-2))).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      simp only [Function.comp_apply,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (f z)])
  have hnegg := integrable_neg_clip_exp hf he hM
  have hh := integral_empiricalExpLog_error hr
    (fun i => hierarchySampleLaw_integrable_coordinate hG hgg hu q hq h0 h1 i hfi)
    (fun i => hierarchySampleLaw_integrable_coordinate hG hgg hu q hq h0 h1 i hgi)
    (fun i => hierarchySampleLaw_integrable_coordinate hG hgg hu q hq h0 h1 i hd)
    (fun i => hierarchySampleLaw_integrable_coordinate hG hgg hu q hq h0 h1 i hneg)
    (fun i => hierarchySampleLaw_integrable_coordinate hG hgg hu q hq h0 h1 i hnegg) ht
  have hdm : Measurable (fun z => (Real.exp (f z)-Real.exp (clipField M (f z)))^2) :=
    ((Real.measurable_exp.comp hf).sub (Real.measurable_exp.comp hgc)).pow_const 2
  have hc1 (i : Fin r) := hierarchySampleLaw_integral_coordinate hG hgg hu q hq h0 h1 i
    (show Measurable (fun z => Real.exp (-2*f z)) from Real.measurable_exp.comp (hf.const_mul (-2)))
  have hc2 (i : Fin r) := hierarchySampleLaw_integral_coordinate hG hgg hu q hq h0 h1 i
    (show Measurable (fun z => Real.exp (-2*clipField M (f z))) from Real.measurable_exp.comp (hgc.const_mul (-2)))
  simp only [hierarchySampleLaw_integral_coordinate hG hgg hu q hq h0 h1 _ hdm,hc1,hc2] at hh
  have hr0 : (r:ℝ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_div_cancel_left₀ _ hr0] at hh
  apply hh.trans
  apply add_le_add le_rfl
  have hn : (∫ z,Real.exp (-2*f z) ∂gaussianLaw (Fin (d+1)))≤
      ∫ z,Real.exp (2* |f z|) ∂gaussianLaw (Fin (d+1)) := by
    exact integral_mono hneg he (fun z => Real.exp_le_exp.mpr (by linarith [neg_abs_le (f z)]))
  have hng : (∫ z,Real.exp (-2*clipField M (f z)) ∂gaussianLaw (Fin (d+1)))≤
      ∫ z,Real.exp (2* |f z|) ∂gaussianLaw (Fin (d+1)) :=
    integral_mono hnegg he (fun z => exp_neg_clip_le hM (f z))
  apply (div_le_div_iff₀ (by positivity : 0<2*t) ht).mpr
  nlinarith

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

 

theorem hierarchyField_lipschitz_tendsto {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (s : Fin (d+1) → ℝ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (x : ℝ) :
    Tendsto (fun r => hierarchyFieldValue μ q (r+1) (fun z => f (x+∑ k,s k*z k))) atTop
      (𝓝 (scalarHierarchy (fun k => overlapDiscount μ (q k.succ)) s f x)) := by
  let F (z : Fin (d+1) → ℝ) := f (x+∑ k,s k*z k)
  let a (k : Fin (d+1)) := overlapDiscount μ (q k.succ)
  have ha (k : Fin (d+1)) : 0≤a k := measureReal_nonneg
  have hF : Continuous F := hf.continuous.comp (by fun_prop)
  have hFi : Integrable F (gaussianLaw (Fin (d+1))) := integrable_lipschitz_field s hf x
  have hE : Integrable (fun z => Real.exp (2* |F z|)) (gaussianLaw (Fin (d+1))) :=
    integrable_exp_abs_lipschitz_field s hf x 2
  let D (m : ℕ) : ℝ := ∫ z,(Real.exp (F z)-Real.exp (clipField m (F z)))^2 ∂gaussianLaw (Fin (d+1))
  let K : ℝ := ∫ z,Real.exp (2* |F z|) ∂gaussianLaw (Fin (d+1))
  have hK : 0≤K := integral_nonneg fun z => (Real.exp_pos _).le
  have hD : Tendsto D atTop (𝓝 (0:ℝ)) := clipped_exp_L2_tendsto hF.measurable hE
  let V (m : ℕ) := scalarHierarchy a s (fun y => clipField m (f y)) x
  have hV : Tendsto V atTop (𝓝 (scalarHierarchy a s f x)) := scalarHierarchy_clip_tendsto ha hf x
  have hB (m : ℕ) : Tendsto (fun r => hierarchyFieldValue μ q (r+1) (fun z => clipField m (F z))) atTop
      (𝓝 (V m)) := by
    let y (z : Fin (d+1) → ℝ) := Real.exp (clipField m (F z))
    have hy : Continuous y := Real.continuous_exp.comp ((continuous_clipField m).comp hF)
    have hl : 0<Real.exp (-(m:ℝ)) := Real.exp_pos _
    have hlb : Real.exp (-(m:ℝ))<Real.exp (m:ℝ)+1 := by
      have hh := Real.exp_le_exp.mpr (show -(m:ℝ)≤(m:ℝ) from le_trans (neg_nonpos.mpr (Nat.cast_nonneg m)) (Nat.cast_nonneg m))
      linarith
    have hb (z : Fin (d+1) → ℝ) : Real.exp (-(m:ℝ))≤y z ∧ y z≤Real.exp (m:ℝ)+1 := by
      have hc := abs_le.mp (clipField_bounded (Nat.cast_nonneg m) (F z))
      exact ⟨Real.exp_le_exp.mpr hc.1,(Real.exp_le_exp.mpr hc.2).trans (by linarith)⟩
    have hh := hierarchy_empirical_positive_tendsto_all hG hgg hu hex q hq h0 h1 hy hl hlb hb
    simp only [y,Real.log_exp] at hh
    have he : gaussianHierarchyRisk a (fun z => clipField m (F z))=V m :=
      gaussianHierarchyRisk_sum a s (fun y => clipField m (f y)) x
    rw [show (fun k => overlapDiscount μ (q k.succ))=a from rfl,he] at hh
    exact hh
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let t := 4*(K+1)/ε
  have ht : 0<t := div_pos (by linarith) hε
  have hKt : K/t<ε/4 := by
    apply (div_lt_iff₀ ht).mpr
    have he : ε/4*t=K+1 := by dsimp [t]; field_simp
    rw [he]
    linarith
  have hDt : Tendsto (fun m => t*D m) atTop (𝓝 (0:ℝ)) := by simpa using hD.const_mul t
  obtain ⟨m₁,hm₁⟩ := Metric.tendsto_atTop.mp hDt (ε/4) (by positivity)
  obtain ⟨m₂,hm₂⟩ := Metric.tendsto_atTop.mp hV (ε/4) (by positivity)
  let m := max m₁ m₂
  have hdm : t*D m<ε/4 := (le_abs_self _).trans_lt (by simpa only [Real.dist_eq,sub_zero] using hm₁ m (le_max_left _ _))
  have hvm : |V m-scalarHierarchy a s f x|<ε/4 := by simpa only [Real.dist_eq] using hm₂ m (le_max_right _ _)
  obtain ⟨R,hR⟩ := Metric.tendsto_atTop.mp (hB m) (ε/4) (by positivity)
  refine ⟨R,fun r hr => ?_⟩
  have hb := hR r hr
  simp only [Real.dist_eq] at hb ⊢
  have herr := hierarchyField_clip_error hG hgg hu q hq h0 h1 (Nat.succ_pos r)
    hF.measurable hFi hE (Nat.cast_nonneg m) ht
  have htri := abs_sub_le (hierarchyFieldValue μ q (r+1) F)
    (hierarchyFieldValue μ q (r+1) (fun z => clipField m (F z))) (scalarHierarchy a s f x)
  have htri' := abs_sub_le (hierarchyFieldValue μ q (r+1) (fun z => clipField m (F z)))
    (V m) (scalarHierarchy a s f x)
  change |hierarchyFieldValue μ q (r+1) F-scalarHierarchy a s f x|<ε
  change |hierarchyFieldValue μ q (r+1) F-hierarchyFieldValue μ q (r+1) (fun z => clipField m (F z))|≤t*D m+K/t at herr
  linarith

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma initial_segment_square {d : ℕ} (p : Fin d → Prop) [DecidablePred p]
    (hp : ∀ i j,i≤j → p j → p i) :
    (∑ k,if p k then (1:ℝ) else 0)^2=∑ k,if p k then 2*(k.val:ℝ)+1 else 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hi := ih (fun k : Fin d => p k.castSucc) (fun i j hij => hp _ _ (Fin.castSucc_le_castSucc_iff.mpr hij))
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc]
    rw [← hi]
    by_cases h : p (Fin.last d)
    · have he (k : Fin d) : p k.castSucc := hp _ _ (Fin.le_last _) h
      have hs : (∑ k : Fin d,if p k.castSucc then (1:ℝ) else 0)=(d:ℝ) := by simp [he]
      rw [hs]
      simp only [h,ite_true,Fin.val_last]
      ring
    · simp [h]

 

def gridZVariance (m : ℕ) (_ : Fin (m+1)) : ℝ := 1/(m+1:ℕ)
def gridYVariance (m : ℕ) (k : Fin (m+1)) : ℝ := (2*(k.val:ℝ)+1)/(2*(m+1:ℕ)^2)

lemma gridZVariance_nonneg (m : ℕ) (k : Fin (m+1)) : 0≤gridZVariance m k := by unfold gridZVariance; positivity
lemma gridYVariance_nonneg (m : ℕ) (k : Fin (m+1)) : 0≤gridYVariance m k := by unfold gridYVariance; positivity

lemma grid_tree_z_kernel {m r : ℕ} (T : PartitionTree (m+1) r) (i j : Fin r) :
    kernel (treeGaussianCoeff T (gridZVariance m)) i j=
      ((codeGramBlock (treeCodes T) (cavityGridVariance m)
        (cavityGridVariance_nonneg m) (cavityGridVariance_sum m)).val i j:ℝ) := by
  rw [kernel_treeGaussianCoeff _ _ (gridZVariance_nonneg m),codeGramBlock_entry]
  conv_rhs => rw [Fin.sum_univ_succ]
  simp only [cavityGridVariance,Fin.cons_zero,Fin.cons_succ,ite_self,zero_add,gridZVariance]

lemma grid_tree_y_kernel {m r : ℕ} (T : PartitionTree (m+1) r) (i j : Fin r) :
    kernel (treeGaussianCoeff T (gridYVariance m)) i j=
      ((codeGramBlock (treeCodes T) (cavityGridVariance m)
        (cavityGridVariance_nonneg m) (cavityGridVariance_sum m)).val i j:ℝ)^2/2 := by
  rw [kernel_treeGaussianCoeff _ _ (gridYVariance_nonneg m),← grid_tree_z_kernel T,
    kernel_treeGaussianCoeff _ _ (gridZVariance_nonneg m)]
  let p (k : Fin (m+1)) := treeCodes T k.succ i=treeCodes T k.succ j
  have hp : ∀ k l : Fin (m+1),k≤l → p l → p k := by
    intro k l hkl
    exact treeCodes_nested T k.succ l.succ (Fin.succ_le_succ_iff.mpr hkl) i j
  have he (k : Fin (m+1)) : (if p k then gridZVariance m k else 0)=(if p k then (1:ℝ) else 0)/(m+1:ℕ) := by
    split <;> simp_all [gridZVariance]
  have he' (k : Fin (m+1)) : (if p k then gridYVariance m k else 0)=(if p k then 2*(k.val:ℝ)+1 else 0)/(2*(m+1:ℕ)^2) := by
    split <;> simp_all [gridYVariance]
  change (∑ k,if p k then gridYVariance m k else 0)=(∑ k,if p k then gridZVariance m k else 0)^2/2
  simp_rw [he,he',← Finset.sum_div,div_pow,initial_segment_square p hp]
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma continuous_empiricalExpLog {r : ℕ} : Continuous (empiricalExpLog : (Fin r → ℝ) → ℝ) := by
  change Continuous (fun u : Fin r → ℝ => empiricalExpLog u)
  by_cases hr : 0<r
  · let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
    simp_rw [empiricalExpLog_eq hr]
    exact continuous_logPartition.sub continuous_const
  · obtain rfl : r=0 := by omega
    simp only [empiricalExpLog,Finset.univ_eq_empty,Finset.sum_empty,Nat.cast_zero,zero_div,Real.log_zero]
    exact continuous_const

lemma empiricalExpLog_cosh {r : ℕ} (hr : 0<r) (u : Fin r → ℝ) :
    empiricalExpLog (fun i => Real.log (2*Real.cosh (u i)))=
      logPartition (fun s : Fin r×Bool => signBool s.2*u s.1)-Real.log (r:ℝ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  have he := empirical_log_cosh hr u id
  simpa only [empiricalExpLog,empiricalMean,id_eq,Real.exp_log (by positivity : 0<2*Real.cosh _)] using he

lemma expected_empiricalExpLog {κ : Type*} [Fintype κ] {r : ℕ} (hr : 0<r)
    (A : Fin r → κ → ℝ) :
    (∫ z,empiricalExpLog (field A z) ∂gaussianLaw κ)=expected A-Real.log (r:ℝ) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  simp_rw [empiricalExpLog_eq hr]
  rw [integral_sub (integrable_logPartition (integrable_field A)) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,expected]

lemma coshGramPressure_field {κ : Type*} [Fintype κ] {r : ℕ} (hr : 0<r)
    (G : GramBlock r) (A : Fin r → κ → ℝ) (hA : ∀ i j,kernel A i j=(G.val i j:ℝ)) (β : ℝ) :
    coshGramPressure G β=
      ∫ z,empiricalExpLog (fun i => Real.log (2*Real.cosh (β*field A z i))) ∂gaussianLaw κ := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let B : Fin r×Bool → κ → ℝ := fun s k => signBool s.2*β*A s.1 k
  have hk : kernel (coshGramCoeff G β)=kernel B := by
    funext s t
    rw [kernel_coshGramCoeff,← hA]
    unfold kernel B
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have he := integral_field_eq_of_kernel (coshGramCoeff G β) B hk logPartition continuous_logPartition.measurable
  change expected (coshGramCoeff G β)=expected B at he
  have hf (z : κ → ℝ) : (fun s : Fin r×Bool => signBool s.2*(β*field A z s.1))=field B z := by
    funext s
    simp only [field,B,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [empiricalExpLog_cosh hr,hf]
  rw [integral_sub (integrable_logPartition (integrable_field B)) (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul,coshGramPressure,expected] at he ⊢
  rw [he]

lemma squareGramPressure_field {κ : Type*} [Fintype κ] {r : ℕ} (hr : 0<r)
    (G : GramBlock r) (A : Fin r → κ → ℝ) (hA : ∀ i j,kernel A i j=(G.val i j:ℝ)^2/2) (β : ℝ) :
    squareGramPressure G β=
      ∫ z,empiricalExpLog (fun i => β*field A z i) ∂gaussianLaw κ := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let B : Fin r → κ → ℝ := fun i k => β*A i k
  have hk : kernel (squareGramCoeff G β)=kernel B := by
    funext i j
    rw [kernel_squareGramCoeff]
    have hh : kernel B i j=β^2*kernel A i j := by
      unfold kernel B
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hh,hA]
    ring
  have he := integral_field_eq_of_kernel (squareGramCoeff G β) B hk logPartition continuous_logPartition.measurable
  change expected (squareGramCoeff G β)=expected B at he
  have hf (z : κ → ℝ) : (fun i => β*field A z i)=field B z := by
    funext i
    simp only [field,B,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hf]
  rw [expected_empiricalExpLog hr B,squareGramPressure,he]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma hierarchyFieldValue_sum {d : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+2) → ℝ) {r : ℕ} (hr : 0<r)
    {f : (Fin (d+1) → ℝ) → ℝ} (hf : Measurable f) (hfi : Integrable f (gaussianLaw (Fin (d+1)))) :
    hierarchyFieldValue μ q r f=
      ∑ T : PartitionTree (d+1) r,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q)*
        ∫ z,empiricalExpLog (fun i => f (treePathVector T z i)) ∂gaussianLaw (TreeNode T) := by
  have hi (T : PartitionTree (d+1) r) :
      Integrable (fun sample => empiricalExpLog (fun i => f (sample i))) (treePathLaw T) := by
    apply integrable_empiricalExpLog hr
    intro i
    have hh := hfi
    rw [← treePathLaw_coordinate T i] at hh
    exact hh.comp_measurable (by fun_prop)
  have hm : Measurable (fun sample : Fin r → Fin (d+1) → ℝ => empiricalExpLog (fun i => f (sample i))) :=
    continuous_empiricalExpLog.measurable.comp (Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i)))
  unfold hierarchyFieldValue hierarchySampleLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,smul_eq_mul,Measure.real,integral_treePathLaw _ _ hm]
  · intro T _
    exact (hi T).smul_measure (measure_ne_top _ _)

lemma lipschitz_log_cosh {β : ℝ} (hβ : 0<β) :
    LipschitzWith (Real.toNNReal β) (fun x => Real.log (2*Real.cosh (β*x))) := by
  have hm : LipschitzWith (Real.toNNReal β) (fun x : ℝ => β*x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos hβ,Real.coe_toNNReal β hβ.le]
    exact le_rfl
  have hf := hm.comp (terminal_lipschitz hβ)
  have he : (fun x => β*terminal β x)=(fun x => Real.log (2*Real.cosh (β*x))) := by
    funext x
    unfold terminal
    field_simp
  simp only [Function.comp_def] at hf
  rw [he] at hf
  simpa only [mul_one,Function.comp_def] using hf

 

theorem gridCavityMixture_fields (μ : ProbabilityMeasure OverlapArray) (m : ℕ)
    {r : ℕ} (hr : 0<r) {β : ℝ} (hβ : 0<β) :
    gridCavityMixture μ m r β=
      hierarchyFieldValue μ (cavityGrid m) r
        (fun z => Real.log (2*Real.cosh (β*(∑ k,Real.sqrt (gridZVariance m k)*z k))))-
      hierarchyFieldValue μ (cavityGrid m) r
        (fun z => β*(∑ k,Real.sqrt (gridYVariance m k)*z k)) := by
  have hc := lipschitz_log_cosh hβ
  have ha : LipschitzWith (Real.toNNReal β) (fun x : ℝ => β*x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos hβ,Real.coe_toNNReal β hβ.le]
    exact le_rfl
  have hci : Integrable (fun z => Real.log (2*Real.cosh (β*(∑ k,Real.sqrt (gridZVariance m k)*z k))))
      (gaussianLaw (Fin (m+1))) := by
    simpa only [zero_add] using integrable_lipschitz_field (fun k => Real.sqrt (gridZVariance m k)) hc 0
  have hai : Integrable (fun z => β*(∑ k,Real.sqrt (gridYVariance m k)*z k))
      (gaussianLaw (Fin (m+1))) := by
    simpa only [zero_add] using integrable_lipschitz_field (fun k => Real.sqrt (gridYVariance m k)) ha 0
  rw [hierarchyFieldValue_sum μ (cavityGrid m) hr (by fun_prop) hci,
    hierarchyFieldValue_sum μ (cavityGrid m) hr (by fun_prop) hai,← Finset.sum_sub_distrib]
  unfold gridCavityMixture
  apply Finset.sum_congr rfl
  intro T _
  rw [← mul_sub,cavityGramObservable,
    coshGramPressure_field hr _ (treeGaussianCoeff T (gridZVariance m)) (grid_tree_z_kernel T) β,
    squareGramPressure_field hr _ (treeGaussianCoeff T (gridYVariance m)) (grid_tree_y_kernel T) β]
  have hz (z : TreeNode T → ℝ) (i : Fin r) := field_treeGaussianCoeff T (gridZVariance m) z i
  have hy (z : TreeNode T → ℝ) (i : Fin r) := field_treeGaussianCoeff T (gridYVariance m) z i
  simp only [hz,hy,treePathVector]

end SKCavity

end

end OAI
