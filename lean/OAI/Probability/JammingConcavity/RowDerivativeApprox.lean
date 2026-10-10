import Mathlib
import OAI.Probability.JammingConcavity.RowParameterData

namespace OAI

/-! Row Derivative Approx. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open Set Filter
open scoped Topology NNReal

namespace MicroscopicJamming
namespace Parameter

lemma second_remainder_representation {F : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (h0 : (0:ℝ)∈I)
    {M₂ M₃ : ℝ} (hM₂ : 0≤M₂) (hM₃ : 0≤M₃)
    (hb₂ : ∀ a∈I,∀ b∈I,∀ c∈I,a≠b → a≠c → b≠c → |dd2 F a b c|≤M₂)
    (hb₃ : ∀ a∈I,∀ b∈I,∀ c∈I,∀ d∈I,
      a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → |dd3 F a b c d|≤M₃) :
    ∃ g : ℝ → ℝ, LipschitzWith ⟨M₃,hM₃⟩ g ∧
      (∀ k∈I, F k=F 0+deriv F 0*k+g k*k^2) ∧ deriv (deriv F) 0=2*g 0 := by
  have hd := differentiable_of_dd2_bound hI hM₂ hb₂
  obtain ⟨g,hg,he⟩ := (second_remainder_lipschitz hI h0 (hd 0 h0) hM₃ hb₃).extend_real
  have hgm (k : ℝ) (hk : k∈I\{0}) :
      g k=(dd1 F 0 k-deriv F 0)/k := (he hk).symm
  have hgd (k : ℝ) (hk : k∈I\{0}) : DifferentiableAt ℝ g k := by
    have hk0 : k≠0 := hk.2
    have hr : DifferentiableAt ℝ (fun k => (dd1 F 0 k-deriv F 0)/k) k := by
      unfold dd1
      exact ((((hd k hk.1).sub_const _).div (differentiableAt_id.sub_const _) (by simpa using hk0)).sub_const _).div
        differentiableAt_id hk0
    apply hr.congr_of_eventuallyEq
    filter_upwards [(hI.sdiff isClosed_singleton).mem_nhds hk] with y hy
    exact hgm y hy
  have hrepr (k : ℝ) (hk : k∈I\{0}) : F k=F 0+deriv F 0*k+g k*k^2 := by
    rw [hgm k hk]
    unfold dd1
    have hk0 : k≠0 := hk.2
    simp only [sub_zero]
    field_simp
    ring
  have hder (k : ℝ) (hk : k∈I\{0}) :
      deriv F k=deriv F 0+deriv g k*k^2+g k*(2*k) := by
    have hh := ((hasDerivAt_const k (F 0)).add ((hasDerivAt_id k).const_mul (deriv F 0))).add
      ((hgd k hk).hasDerivAt.mul ((hasDerivAt_id k).pow 2))
    change HasDerivAt (fun y => F 0+deriv F 0*y+g y*y^2)
      (0+deriv F 0*1+(deriv g k*k^2+g k*(2*k^(2-1)*1))) k at hh
    norm_num only [Nat.reduceSub,pow_one,mul_one,zero_add] at hh
    have hhe : HasDerivAt F (deriv F 0+deriv g k*k^2+g k*(2*k)) k := by
      have ha : deriv F 0+(deriv g k*k^2+g k*(2*k))=deriv F 0+deriv g k*k^2+g k*(2*k) := by ring
      rw [ha] at hh
      apply hh.congr_of_eventuallyEq
      filter_upwards [(hI.sdiff isClosed_singleton).mem_nhds hk] with y hy
      exact hrepr y hy
    exact hhe.deriv
  have hb (k : ℝ) : |deriv g k|≤M₃ := by
    have hh := (norm_deriv_le_of_lipschitz hg : ‖deriv g k‖≤(⟨M₃,hM₃⟩:ℝ≥0))
    change |deriv g k|≤M₃ at hh
    exact hh
  have hv : Tendsto (fun k : ℝ => deriv g k*k) (𝓝 0) (𝓝 0) := by
    have hbound (k : ℝ) : ‖deriv g k*k‖≤M₃*|k| := by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_right (hb k) (abs_nonneg _)
    have hh : Tendsto (fun k : ℝ => M₃*|k|) (𝓝 0) (𝓝 0) := by
      have hc := (((continuous_const : Continuous (fun _ : ℝ => M₃)).mul continuous_abs).continuousAt (x:= (0:ℝ))).tendsto
      change Tendsto (fun k : ℝ => M₃*|k|) (𝓝 0) (𝓝 (M₃*|0|)) at hc
      simpa only [abs_zero,mul_zero] using hc
    exact squeeze_zero_norm hbound hh
  have hsl : Tendsto (slope (deriv F) 0) (𝓝[≠] 0) (𝓝 (2*g 0)) := by
    have hh : Tendsto (fun k : ℝ => deriv g k*k+2*g k) (𝓝[≠] 0) (𝓝 (0+2*g 0)) := (hv.mono_left nhdsWithin_le_nhds).add
      ((hg.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_mul 2)
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hI.mem_nhds h0),self_mem_nhdsWithin] with k hk hk0
    rw [slope_def_field,hder k ⟨hk,hk0⟩]
    have hkne : k≠0 := hk0
    simp only [sub_zero]
    field_simp
    ring
  refine ⟨g,hg,?_,(hasDerivAt_iff_tendsto_slope.mpr hsl).deriv⟩
  intro k hk
  by_cases hk0 : k=0
  · simp [hk0]
  · exact hrepr k ⟨hk,hk0⟩

lemma first_derivative_error {F : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (h0 : (0:ℝ)∈I)
    {M : ℝ} (hM : 0≤M)
    (hb : ∀ a∈I,∀ b∈I,∀ c∈I,a≠b → a≠c → b≠c → |dd2 F a b c|≤M)
    {h : ℝ} (hh : h∈I) (hh0 : h≠0) : |dd1 F 0 h-deriv F 0|≤M*|h| := by
  have hd := differentiable_of_dd2_bound hI hM hb 0 h0
  have ht : Tendsto (fun k => |dd1 F 0 h-dd1 F 0 k|) (𝓝[≠] 0) (𝓝 |dd1 F 0 h-deriv F 0|) := by
    have he : (fun k => dd1 F 0 k)=slope F 0 := funext (fun k => (slope_def_field F 0 k).symm)
    have hh1 : Tendsto (fun k => dd1 F 0 k) (𝓝[≠] 0) (𝓝 (deriv F 0)) := by
      rw [he]; exact hd.hasDerivAt.tendsto_slope
    exact (tendsto_const_nhds.sub hh1).abs
  have hr : Tendsto (fun k : ℝ => M*|h-k|) (𝓝[≠] 0) (𝓝 (M*|h|)) := by
    simpa using ((tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).abs.const_mul M :
      Tendsto (fun k : ℝ => M*|h-k|) (𝓝[≠] 0) (𝓝 (M*|h-0|)))
  apply le_of_tendsto_of_tendsto ht hr
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds (hI.mem_nhds h0),self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hh0.symm)] with k hk hk0 hkh
  rw [dd1_sub_slope F hh0.symm (show (0:ℝ)≠k from (show k≠0 from hk0).symm) hkh.symm,abs_mul]
  calc
    |h-k| *|dd2 F 0 h k|≤|h-k| *M := mul_le_mul_of_nonneg_left
      (hb 0 h0 h hh k hk hh0.symm (show (0:ℝ)≠k from (show k≠0 from hk0).symm) hkh.symm) (abs_nonneg _)
    _ = M*|h-k| := mul_comm _ _

lemma second_derivative_error {F : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) (h0 : (0:ℝ)∈I)
    {M₂ M₃ : ℝ} (hM₂ : 0≤M₂) (hM₃ : 0≤M₃)
    (hb₂ : ∀ a∈I,∀ b∈I,∀ c∈I,a≠b → a≠c → b≠c → |dd2 F a b c|≤M₂)
    (hb₃ : ∀ a∈I,∀ b∈I,∀ c∈I,∀ d∈I,
      a≠b → a≠c → a≠d → b≠c → b≠d → c≠d → |dd3 F a b c d|≤M₃)
    {h : ℝ} (hh : h∈I) (hh2 : 2*h∈I) (hh0 : h≠0) :
    |dd2 F 0 h (2*h)-deriv (deriv F) 0/2|≤5*M₃*|h| := by
  obtain ⟨g,hg,he,hd⟩ := second_remainder_representation hI h0 hM₂ hM₃ hb₂ hb₃
  have hid : dd2 F 0 h (2*h)=2*g (2*h)-g h := by
    unfold dd2 dd1
    rw [he h hh,he (2*h) hh2]
    field_simp
    ring
  rw [hid,hd]
  have h1 := hg.dist_le_mul h 0
  have h2 := hg.dist_le_mul (2*h) 0
  change |g h-g 0|≤M₃*|h-0| at h1
  change |g (2*h)-g 0|≤M₃*|2*h-0| at h2
  simp only [sub_zero,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h1 h2
  calc
    |2*g (2*h)-g h-2*g 0/2|=|2*(g (2*h)-g 0)-(g h-g 0)| := by congr 1; ring
    _ ≤ |2*(g (2*h)-g 0)|+|g h-g 0| := abs_sub _ _
    _ = 2*|g (2*h)-g 0|+|g h-g 0| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ 5*M₃*|h| := by linarith
end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
open Higher
lemma cylinder_of_poly_error {S : Set ℝ} {f : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) {d : ℕ} {C : ℝ} (_hC : 0≤C)
    (hbd : ∀ n t,t∈S → ∀ x,|f n t x-F t x|≤e n*C*(1+|x|)^d) :
    CylinderConvergence f F S := by
  intro R hR
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : Tendsto (fun n => e n*C*(1+R)^d) atTop (𝓝 0) := by
    simpa using (he.mul_const C).mul_const ((1+R)^d)
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with n hn p hp
  rw [Real.dist_eq,abs_sub_comm]
  have hx : |p.2|≤R := abs_le.mpr hp.2
  have hepos : 0≤e n*C := by
    have hh := (abs_nonneg _).trans (hbd n p.1 hp.1 0)
    simpa using hh
  exact ((hbd n p.1 hp.1 p.2).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith) d) hepos)).trans_lt hn

lemma smooth_limit_of_all_jet_convergence {S : Set ℝ} {f : ℕ → ℝ → ℝ → ℝ}
    {G : ℕ → ℝ → ℝ → ℝ} (hs : ∀ n,JointSpatialSmooth S (f n))
    (hv : ∀ k,CylinderConvergence (fun n t => iteratedDeriv k (f n t)) (G k) S) :
    JointSpatialSmooth S (G 0) ∧ ∀ k t,t∈S → iteratedDeriv k (G 0 t)=G k t := by
  have hd (k : ℕ) : ∀ t∈S,∀ x,HasDerivAt (G k t) (G (k+1) t x) x := by
    apply cylinder_limit_hasDerivAt (hv k)
      (by simpa only [← iteratedDeriv_succ] using hv (k+1))
    intro n t ht
    exact (contDiff_iff_iteratedDeriv.mp ((hs n).1 t ht)).2 k (by simp)
  have hj : ∀ k t,t∈S → iteratedDeriv k (G 0 t)=G k t := by
    intro k
    induction k with
    | zero => intro t ht; rfl
    | succ k ih =>
      intro t ht
      rw [iteratedDeriv_succ,ih t ht]
      exact funext (fun x => (hd k t ht x).deriv)
  refine ⟨⟨?_,?_⟩,hj⟩
  · intro t ht
    apply contDiff_of_differentiable_iteratedDeriv
    intro k _
    rw [hj k t ht]
    exact fun x => (hd k t ht x).differentiableAt
  · intro k
    apply (cylinder_limit_continuous (f:=fun n t => iteratedDeriv k (f n t)) (F:=G k) (fun n => (hs n).2 k) (hv k)).congr
    intro p hp
    exact congrFun (hj k p.1 hp.1) p.2

lemma growth_limit {S : Set ℝ} {f : ℕ → ℝ → ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    (hf : FamilyGrowth (fun _ : ℕ => True) S f)
    (hv : ∀ t∈S,∀ x,Tendsto (fun n => f n t x) atTop (𝓝 (F t x))) :
    ∃ d : ℕ,∃ C : ℝ,0≤C ∧ ∀ t∈S,∀ x,|F t x|≤C*(1+|x|)^d := by
  obtain ⟨d,C,hC,hb⟩ := hf
  exact ⟨d,C,hC,fun t ht x => le_of_tendsto (hv t ht x).abs (Eventually.of_forall (fun n => hb n trivial t ht x))⟩
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

def pjet (F : ℝ → ℝ → ℝ → ℝ) (k : ℕ) (t x : ℝ) : ℝ :=
  deriv (fun e => iteratedDeriv k (F e t) x) 0

def pjet2 (F : ℝ → ℝ → ℝ → ℝ) (k : ℕ) (t x : ℝ) : ℝ :=
  deriv (deriv (fun e => iteratedDeriv k (F e t) x)) 0/2

def paramSeq (r : ℝ) (n : ℕ) : ℝ := (r/4)*(1/((n:ℝ)+1))

lemma paramSeq_pos {r : ℝ} (hr : 0<r) (n : ℕ) : 0<paramSeq r n := by unfold paramSeq; positivity
lemma paramSeq_bound {r : ℝ} (hr : 0<r) (n : ℕ) : paramSeq r n≤r/4 := by
  unfold paramSeq
  apply mul_le_of_le_one_right (by positivity)
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
lemma paramSeq_tendsto (r : ℝ) : Tendsto (paramSeq r) atTop (𝓝 0) := by
  unfold paramSeq
  simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r/4)
lemma paramSeq_mem {r : ℝ} (hr : 0<r) (n : ℕ) : paramSeq r n∈Ioo (-r) r :=
  ⟨by linarith [paramSeq_pos hr n],by linarith [paramSeq_bound hr n]⟩
lemma twice_paramSeq_mem {r : ℝ} (hr : 0<r) (n : ℕ) : 2*paramSeq r n∈Ioo (-r) r :=
  ⟨by linarith [paramSeq_pos hr n],by linarith [paramSeq_bound hr n]⟩

def seqNodes2 {r : ℝ} (hr : 0<r) (n : ℕ) : Nodes2 (Ioo (-r) r) :=
  ⟨0,paramSeq r n,⟨by linarith,hr⟩,paramSeq_mem hr n,(paramSeq_pos hr n).ne⟩
def seqNodes3 {r : ℝ} (hr : 0<r) (n : ℕ) : Nodes3 (Ioo (-r) r) :=
  ⟨seqNodes2 hr n,2*paramSeq r n,twice_paramSeq_mem hr n,by dsimp [seqNodes2]; linarith [paramSeq_pos hr n],by dsimp [seqNodes2]; linarith [paramSeq_pos hr n]⟩

lemma RankFamilyData.bound_dd2 {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (k : ℕ) :
    ∃ d : ℕ,∃ C : ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) 1,∀ x,
      ∀ a∈I,∀ b∈I,∀ c∈I,a≠b → a≠c → b≠c →
        |dd2 (fun e => iteratedDeriv k (F e t) x) a b c|≤C*(1+|x|)^d := by
  obtain ⟨d,C,hC,hb⟩ := (field2_poly hf).bounds k
  refine ⟨d,C,hC,?_⟩
  intro t ht x a ha b hb' c hc hab hac hbc
  let p : Nodes3 I := ⟨⟨a,b,ha,hb',hab⟩,c,hc,hac,hbc⟩
  have hh := hb p trivial t ht x
  dsimp only at hh
  rw [field2_jet hf.smooth p k ht x] at hh
  exact hh

lemma RankFamilyData.bound_dd3 {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) (k : ℕ) :
    ∃ d : ℕ,∃ C : ℝ,0≤C ∧ ∀ t∈Icc (0:ℝ) 1,∀ x,
      ∀ a∈I,∀ b∈I,∀ c∈I,∀ z∈I,a≠b → a≠c → a≠z → b≠c → b≠z → c≠z →
        |dd3 (fun e => iteratedDeriv k (F e t) x) a b c z|≤C*(1+|x|)^d := by
  obtain ⟨d,C,hC,hb⟩ := (field3_poly hf).bounds k
  refine ⟨d,C,hC,?_⟩
  intro t ht x a ha b hb' c hc e he hab hac hae hbc hbe hce
  let p : Nodes4 I := ⟨⟨⟨a,b,ha,hb',hab⟩,c,hc,hac,hbc⟩,e,he,hae,hbe,hce⟩
  have hh := hb p trivial t ht x
  dsimp only at hh
  rw [field3_jet hf.smooth p k ht x] at hh
  exact hh

lemma RankFamilyData.first_jet_limit {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) (k : ℕ) :
    CylinderConvergence (fun n t => iteratedDeriv k (field1 F 0 (paramSeq r n) t)) (pjet F k) (Icc 0 1) := by
  obtain ⟨d,C,hC,hb⟩ := hf.bound_dd2 k
  apply cylinder_of_poly_error (d:=d) (paramSeq_tendsto r) hC
  intro n t ht x
  have hj := field1_jet hf.smooth (seqNodes2 hr n) k ht x
  dsimp only [seqNodes2] at hj
  rw [hj]
  have hh := first_derivative_error isOpen_Ioo (show (0:ℝ)∈Ioo (-r) r from ⟨by linarith,hr⟩)
    (show 0≤C*(1+|x|)^d by positivity) (hb t ht x) (paramSeq_mem hr n) (paramSeq_pos hr n).ne'
  rw [abs_of_pos (paramSeq_pos hr n)] at hh
  have he : C*(1+|x|)^d*paramSeq r n=paramSeq r n*C*(1+|x|)^d := by ring
  exact he ▸ hh

lemma RankFamilyData.second_jet_limit {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) (k : ℕ) :
    CylinderConvergence (fun n t => iteratedDeriv k (field2 F 0 (paramSeq r n) (2*paramSeq r n) t)) (pjet2 F k) (Icc 0 1) := by
  obtain ⟨d₂,C₂,hC₂,hb₂⟩ := hf.bound_dd2 k
  obtain ⟨d₃,C₃,hC₃,hb₃⟩ := hf.bound_dd3 k
  apply cylinder_of_poly_error (d:=d₃) (paramSeq_tendsto r) (show 0≤5*C₃ by positivity)
  intro n t ht x
  have hj := field2_jet hf.smooth (seqNodes3 hr n) k ht x
  dsimp only [seqNodes3,seqNodes2] at hj
  rw [hj]
  have hh := second_derivative_error isOpen_Ioo (show (0:ℝ)∈Ioo (-r) r from ⟨by linarith,hr⟩)
    (show 0≤C₂*(1+|x|)^d₂ by positivity) (show 0≤C₃*(1+|x|)^d₃ by positivity)
    (hb₂ t ht x) (hb₃ t ht x) (paramSeq_mem hr n) (twice_paramSeq_mem hr n) (paramSeq_pos hr n).ne'
  rw [abs_of_pos (paramSeq_pos hr n)] at hh
  have he : 5*(C₃*(1+|x|)^d₃)*paramSeq r n=paramSeq r n*(5*C₃)*(1+|x|)^d₃ := by ring
  exact he ▸ hh

lemma RankFamilyData.parameter_jets {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) :
    (JointSpatialSmooth (Icc 0 1) (pjet F 0) ∧ ∀ k t,t∈Icc (0:ℝ) 1 → iteratedDeriv k (pjet F 0 t)=pjet F k t) ∧
    (JointSpatialSmooth (Icc 0 1) (pjet2 F 0) ∧ ∀ k t,t∈Icc (0:ℝ) 1 → iteratedDeriv k (pjet2 F 0 t)=pjet2 F k t) := by
  constructor
  · exact smooth_limit_of_all_jet_convergence (fun n => field1_smooth hf.smooth (seqNodes2 hr n)) (hf.first_jet_limit hr)
  · exact smooth_limit_of_all_jet_convergence (fun n => field2_smooth hf.smooth (seqNodes3 hr n)) (hf.second_jet_limit hr)
end Parameter
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

def endpointRhs {ι : Type*} (A B : ℝ → ℝ) (F : ℝ → ℝ → ℝ → ℝ)
    (l r : ι → ℝ) (U H : ι → ℝ → ℝ → ℝ) (i : ι) (t x : ℝ) : ℝ :=
  H i t x-(A t+l i*B t)*iteratedDeriv 2 (U i t) x-
    ((A t+l i*B t)*t*(iteratedDeriv 1 (F (l i) t) x+iteratedDeriv 1 (F (r i) t) x))*iteratedDeriv 1 (U i t) x

lemma RankFamilyData.endpoint_rhs_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) {ι : Type*} (l r : ι → ℝ) (hl : ∀ i,l i∈I) (hr : ∀ i,r i∈I)
    {U H : ι → ℝ → ℝ → ℝ}
    (hU : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) U)
    (hH : PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) H) :
    PolynomialJetFamily (fun _ : ι => True) (Icc 0 1) (endpointRhs A B F l r U H) := by
  obtain ⟨D,hD,ha,hB⟩ := hf.coeff
  have hd := (hU.jet 2).coeff_mul (fun i _ => hf.diffusion_cont (l i)) hD
    (fun i _ t ht => by rw [abs_of_nonneg (ha (l i) (hl i) t ht).1]; exact (ha (l i) (hl i) t ht).2)
  have hlp := hf.poly.comp (R:=fun _ => True) l (fun i _ => hl i)
  have hrp := hf.poly.comp (R:=fun _ => True) r (fun i _ => hr i)
  have hb := hf.mul_at l hl ((((hlp.jet 1).add (hrp.jet 1))).mul (hU.jet 1))
  convert (hH.sub hd).sub hb using 1
  funext i t x
  dsimp only [endpointRhs]
  ring

def rhs1 {I : Set ℝ} (F : ℝ → ℝ → ℝ → ℝ) (A B : ℝ → ℝ) :=
  endpointRhs A B F (fun p : Nodes2 I => p.a) (fun p => p.b)
    (fun p => field1 F p.a p.b) (source1 F B)
def rhs2 {I : Set ℝ} (F : ℝ → ℝ → ℝ → ℝ) (A B : ℝ → ℝ) :=
  endpointRhs A B F (fun p : Nodes3 I => p.a) (fun p => p.c)
    (fun p => field2 F p.a p.b p.c) (source2 F A B)

lemma rhs1_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) : PolynomialJetFamily (fun _ : Nodes2 I => True) (Icc 0 1) (rhs1 F A B) :=
  hf.endpoint_rhs_poly (fun p : Nodes2 I => p.a) (fun p => p.b) (fun p => p.ha) (fun p => p.hb) (field1_poly hf) (source1_poly hf)
lemma rhs2_poly {I : Set ℝ} {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData I A B F) : PolynomialJetFamily (fun _ : Nodes3 I => True) (Icc 0 1) (rhs2 F A B) :=
  hf.endpoint_rhs_poly (fun p : Nodes3 I => p.a) (fun p => p.c) (fun p => p.ha) (fun p => p.hc) (field2_poly hf) (source2_poly hf)
end Parameter
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming

lemma time_derivative_limit_dominated {f g : ℕ → ℝ → ℝ} {F G : ℝ → ℝ} {C : ℝ}
    (hfc : ∀ n,ContinuousOn (f n) (Icc 0 1))
    (hgc : ∀ n,ContinuousOn (g n) (Icc 0 1))
    (hG : ContinuousOn G (Icc 0 1))
    (hd : ∀ n t,t∈Ioo (0:ℝ) 1 → HasDerivAt (f n) (g n t) t)
    (hfv : ∀ t∈Icc (0:ℝ) 1,Tendsto (fun n => f n t) atTop (𝓝 (F t)))
    (hgv : ∀ t∈Icc (0:ℝ) 1,Tendsto (fun n => g n t) atTop (𝓝 (G t)))
    (hgb : ∀ n t,t∈Icc (0:ℝ) 1 → |g n t|≤C) :
    ∀ t∈Ioo (0:ℝ) 1,HasDerivAt F (G t) t := by
  have hsub (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : uIcc t 1⊆Icc 0 1 := by
    rw [uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl
  have hrepr (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : F t=F 1-∫ s in t..1,G s := by
    have hi : Tendsto (fun n => ∫ s in t..1,g n s) atTop (𝓝 (∫ s in t..1,G s)) := by
      apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      · exact Eventually.of_forall (fun n => (((hgc n).mono (hsub t ht)).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc)
      · exact Eventually.of_forall (fun n => Eventually.of_forall (fun s hs => by
          simpa only [Real.norm_eq_abs] using hgb n s (hsub t ht (uIoc_subset_uIcc hs))))
      · exact intervalIntegrable_const
      · exact Eventually.of_forall (fun s hs => hgv s (hsub t ht (uIoc_subset_uIcc hs)))
    have he (n : ℕ) : (∫ s in t..1,g n s)=f n 1-f n t := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.2
      · exact (hfc n).mono (Icc_subset_Icc ht.1 le_rfl)
      · exact fun s hs => hd n s ⟨lt_of_le_of_lt ht.1 hs.1,hs.2⟩
      · exact ((hgc n).mono (hsub t ht)).intervalIntegrable
    have hh := tendsto_nhds_unique hi ((hfv 1 ⟨by norm_num,le_rfl⟩).sub (hfv t ht) |>.congr (fun n => (he n).symm))
    linarith
  let E : ℝ → ℝ := fun t => G (projIcc 0 1 (by norm_num) t)
  have hE : Continuous E := (continuousOn_iff_continuous_domRestrict.mp hG).comp continuous_projIcc
  have hEe (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : E t=G t := by
    dsimp only [E]; rw [projIcc_of_mem (by norm_num) ht]
  intro t ht
  have hh := (intervalIntegral.integral_hasDerivAt_left (hE.intervalIntegrable t 1)
    hE.aestronglyMeasurable.stronglyMeasurableAtFilter hE.continuousAt).const_sub (F 1)
  simp only [neg_neg,hEe t ⟨ht.1.le,ht.2.le⟩] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [hrepr s ⟨hs.1.le,hs.2.le⟩]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  exact (hEe y (hsub s ⟨hs.1.le,hs.2.le⟩ hy)).symm
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
namespace Parameter
open Higher

lemma RankFamilyData.base_jet_limit {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) (k : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x c : ℝ) :
    Tendsto (fun n => iteratedDeriv k (F (c*paramSeq r n) t) x) atTop (𝓝 (iteratedDeriv k (F 0 t) x)) := by
  have hc := (MicroscopicJamming.RankFamilyData.parameter_C2 hf isOpen_Ioo ⟨by linarith,hr⟩ k t ht x).1.continuousAt
  exact hc.tendsto.comp (by simpa only [mul_zero] using (paramSeq_tendsto r).const_mul c)

lemma RankFamilyData.offaxis_jet_limit {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) (k : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    Tendsto (fun n => iteratedDeriv k (field1 F (paramSeq r n) (2*paramSeq r n) t) x)
      atTop (𝓝 (pjet F k t x)) := by
  have h0 := (hf.first_jet_limit hr k).tendsto_at ht x
  have h2 := (hf.second_jet_limit hr k).tendsto_at ht x
  have he (n : ℕ) : iteratedDeriv k (field1 F (paramSeq r n) (2*paramSeq r n) t) x=
      iteratedDeriv k (field1 F 0 (paramSeq r n) t) x+
      (2*paramSeq r n)*iteratedDeriv k (field2 F 0 (paramSeq r n) (2*paramSeq r n) t) x := by
    have ha := field1_jet hf.smooth (seqNodes3 hr n).bc k ht x
    have hb := field1_jet hf.smooth (seqNodes2 hr n) k ht x
    have hc := field2_jet hf.smooth (seqNodes3 hr n) k ht x
    dsimp only [seqNodes2,seqNodes3,Nodes3.bc] at ha hb hc
    rw [ha,hb,hc]
    unfold dd2
    have hn := (paramSeq_pos hr n).ne'
    field_simp
    ring
  have hh := h0.add (((paramSeq_tendsto r).const_mul 2).mul h2)
  simpa only [mul_zero,zero_mul,add_zero,← he] using hh

def linearRhs (A B : ℝ → ℝ) (f v : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -B t*(iteratedDeriv 2 (f t) x+t*(iteratedDeriv 1 (f t) x)^2)-
  A t*iteratedDeriv 2 (v t) x-2*A t*t*iteratedDeriv 1 (f t) x*iteratedDeriv 1 (v t) x

def quadraticRhs (A B : ℝ → ℝ) (f v g : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  -A t*t*(iteratedDeriv 1 (v t) x)^2-
  B t*(iteratedDeriv 2 (v t) x+2*t*iteratedDeriv 1 (f t) x*iteratedDeriv 1 (v t) x)-
  A t*iteratedDeriv 2 (g t) x-2*A t*t*iteratedDeriv 1 (f t) x*iteratedDeriv 1 (g t) x

lemma linearRhs_smooth {A B : ℝ → ℝ} {f v : ℝ → ℝ → ℝ}
    (hA : ContinuousOn A (Icc 0 1)) (hB : ContinuousOn B (Icc 0 1))
    (hf : JointSpatialSmooth (Icc 0 1) f) (hv : JointSpatialSmooth (Icc 0 1) v) :
    JointSpatialSmooth (Icc 0 1) (linearRhs A B f v) := by
  have hh := (((hf.jet 2).add (((hf.jet 1).mul (hf.jet 1)).coeff_mul continuousOn_id)).coeff_mul hB.neg).sub
    ((hv.jet 2).coeff_mul hA) |>.sub ((((hf.jet 1).mul (hv.jet 1)).coeff_mul
      (((continuousOn_const (c:=(2:ℝ))).mul hA).mul continuousOn_id)))
  convert hh using 1
  funext t x
  dsimp only [linearRhs,Pi.mul_apply,Pi.neg_apply,id_eq]
  ring

lemma quadraticRhs_smooth {A B : ℝ → ℝ} {f v g : ℝ → ℝ → ℝ}
    (hA : ContinuousOn A (Icc 0 1)) (hB : ContinuousOn B (Icc 0 1))
    (hf : JointSpatialSmooth (Icc 0 1) f) (hv : JointSpatialSmooth (Icc 0 1) v)
    (hg : JointSpatialSmooth (Icc 0 1) g) :
    JointSpatialSmooth (Icc 0 1) (quadraticRhs A B f v g) := by
  have hh := (((hv.jet 1).mul (hv.jet 1)).coeff_mul (hA.neg.mul continuousOn_id)).sub
    (((hv.jet 2).add (((hf.jet 1).mul (hv.jet 1)).coeff_mul ((continuousOn_const (c:=(2:ℝ))).mul continuousOn_id))).coeff_mul hB) |>.sub
    ((hg.jet 2).coeff_mul hA) |>.sub ((((hf.jet 1).mul (hg.jet 1)).coeff_mul
      (((continuousOn_const (c:=(2:ℝ))).mul hA).mul continuousOn_id)))
  convert hh using 1
  funext t x
  dsimp only [quadraticRhs,Pi.mul_apply,Pi.neg_apply,id_eq]
  ring

lemma RankFamilyData.rhs1_limit {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    Tendsto (fun n => rhs1 F A B (seqNodes2 hr n) t x) atTop
      (𝓝 (linearRhs A B (F 0) (pjet F 0) t x)) := by
  have hb (k) := hf.base_jet_limit hr k ht x 1
  simp only [one_mul] at hb
  have hv (k) := (hf.first_jet_limit hr k).tendsto_at ht x
  have hj := (hf.parameter_jets hr).1.2
  have hh := (((hb 2).add (((hb 1).pow 2).const_mul t)).const_mul (-B t)).sub
    ((hv 2).const_mul (A t)) |>.sub ((((tendsto_const_nhds (x:=iteratedDeriv 1 (F 0 t) x)).add (hb 1)).mul (hv 1)).const_mul (A t*t))
  convert hh using 1
  · funext n; dsimp [rhs1,endpointRhs,source1,seqNodes2]; ring
  · dsimp only [linearRhs,Pi.mul_apply,Pi.neg_apply,id_eq]; rw [hj 2 t ht,hj 1 t ht]; ring_nf

lemma RankFamilyData.rhs2_limit {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : ℝ) :
    Tendsto (fun n => rhs2 F A B (seqNodes3 hr n) t x) atTop
      (𝓝 (quadraticRhs A B (F 0) (pjet F 0) (pjet2 F 0) t x)) := by
  have hb (k) := hf.base_jet_limit hr k ht x 1
  simp only [one_mul] at hb
  have hc (k) := hf.base_jet_limit hr k ht x 2
  have hv (k) := (hf.first_jet_limit hr k).tendsto_at ht x
  have hw (k) := hf.offaxis_jet_limit hr k ht x
  have hg (k) := (hf.second_jet_limit hr k).tendsto_at ht x
  have hj := hf.parameter_jets hr
  have hh := (((hv 1).mul (hw 1)).const_mul (-A t*t)).sub
    (((hw 2).add ((((hb 1).add (hc 1)).mul (hw 1)).const_mul t)).const_mul (B t)) |>.sub
    ((hg 2).const_mul (A t)) |>.sub ((((tendsto_const_nhds (x:=iteratedDeriv 1 (F 0 t) x)).add (hc 1)).mul (hg 1)).const_mul (A t*t))
  convert hh using 1
  · funext n; dsimp [rhs2,endpointRhs,source2,seqNodes2,seqNodes3]; ring
  · dsimp only [quadraticRhs,Pi.mul_apply,Pi.neg_apply,id_eq]; rw [hj.1.2 2 t ht,hj.1.2 1 t ht,hj.2.2 2 t ht,hj.2.2 1 t ht]; ring_nf

lemma RankFamilyData.parameter_equations {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) :
    (∀ t∈Ioo (0:ℝ) 1,∀ x,HasDerivAt (fun s => pjet F 0 s x)
      (linearRhs A B (F 0) (pjet F 0) t x) t) ∧
    (∀ t∈Ioo (0:ℝ) 1,∀ x,HasDerivAt (fun s => pjet2 F 0 s x)
      (quadraticRhs A B (F 0) (pjet F 0) (pjet2 F 0) t x) t) := by
  have hj := hf.parameter_jets hr
  have h0 : (0:ℝ)∈Ioo (-r) r := ⟨by linarith,hr⟩
  constructor
  · intro t ht x
    obtain ⟨d,C,hC,hb⟩ := (rhs1_poly hf).bounds 0
    apply time_derivative_limit_dominated (C:=C*(1+|x|)^d)
      (fun n => ((field1_smooth hf.smooth (seqNodes2 hr n)).2 0).comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩))
      (fun n => ((rhs1_poly hf).smooth (seqNodes2 hr n) trivial).2 0 |>.comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩))
      ((linearRhs_smooth hf.Acont hf.Bcont (hf.smooth 0 h0) hj.1.1).2 0 |>.comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩))
      (fun n s hs => field1_equation hf (seqNodes2 hr n) hs x)
      (fun s hs => (hf.first_jet_limit hr 0).tendsto_at hs x)
      (fun s hs => hf.rhs1_limit hr hs x)
      (fun n s hs => hb (seqNodes2 hr n) trivial s hs x) t ht
  · intro t ht x
    obtain ⟨d,C,hC,hb⟩ := (rhs2_poly hf).bounds 0
    apply time_derivative_limit_dominated (C:=C*(1+|x|)^d)
      (fun n => ((field2_smooth hf.smooth (seqNodes3 hr n)).2 0).comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩))
      (fun n => ((rhs2_poly hf).smooth (seqNodes3 hr n) trivial).2 0 |>.comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩))
      ((quadraticRhs_smooth hf.Acont hf.Bcont (hf.smooth 0 h0) hj.1.1 hj.2.1).2 0 |>.comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs,mem_univ _⟩))
      (fun n s hs => field2_equation hf (seqNodes3 hr n) hs x)
      (fun s hs => (hf.second_jet_limit hr 0).tendsto_at hs x)
      (fun s hs => hf.rhs2_limit hr hs x)
      (fun n s hs => hb (seqNodes3 hr n) trivial s hs x) t ht
end Parameter
end MicroscopicJamming

 
open Set

namespace MicroscopicJamming
namespace Hessian
 
structure Jet (u ux uxx ut : ℝ → ℝ → ℝ) : Prop where
  x : ∀ t∈Icc (0:ℝ) 1,∀ z,HasDerivAt (u t) (ux t z) z
  xx : ∀ t∈Icc (0:ℝ) 1,∀ z,HasDerivAt (ux t) (uxx t z) z
  time : ∀ t∈Ico (0:ℝ) 1,∀ z,HasDerivWithinAt (fun s => u s z) (ut t z) (Ici t) t
lemma Jet.spatial_deriv {u ux uxx ut : ℝ → ℝ → ℝ} (h : Jet u ux uxx ut) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : deriv (u t)=ux t :=
  funext (fun z => (h.x t ht z).deriv)
lemma Jet.spatial_deriv2 {u ux uxx ut : ℝ → ℝ → ℝ} (h : Jet u ux uxx ut) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) : deriv (deriv (u t))=uxx t := by
  rw [h.spatial_deriv ht]; exact funext (fun z => (h.xx t ht z).deriv)
lemma Jet.add {u ux uxx ut v vx vxx vt : ℝ → ℝ → ℝ}
    (h : Jet u ux uxx ut) (k : Jet v vx vxx vt) :
    Jet (fun t z => u t z+v t z) (fun t z => ux t z+vx t z)
      (fun t z => uxx t z+vxx t z) (fun t z => ut t z+vt t z) :=
  ⟨fun t ht z => (h.x t ht z).add (k.x t ht z),fun t ht z => (h.xx t ht z).add (k.xx t ht z),
    fun t ht z => (h.time t ht z).add (k.time t ht z)⟩
lemma Jet.neg {u ux uxx ut : ℝ → ℝ → ℝ} (h : Jet u ux uxx ut) :
    Jet (fun t z => -u t z) (fun t z => -ux t z) (fun t z => -uxx t z) (fun t z => -ut t z) :=
  ⟨fun t ht z => (h.x t ht z).neg,fun t ht z => (h.xx t ht z).neg,fun t ht z => (h.time t ht z).neg⟩
lemma Jet.mul {u ux uxx ut v vx vxx vt : ℝ → ℝ → ℝ}
    (h : Jet u ux uxx ut) (k : Jet v vx vxx vt) :
    Jet (fun t z => u t z*v t z) (fun t z => ux t z*v t z+u t z*vx t z)
      (fun t z => uxx t z*v t z+2*ux t z*vx t z+u t z*vxx t z)
      (fun t z => ut t z*v t z+u t z*vt t z) := by
  refine ⟨fun t ht z => (h.x t ht z).mul (k.x t ht z),fun t ht z => ?_,
    fun t ht z => (h.time t ht z).mul (k.time t ht z)⟩
  exact (((h.xx t ht z).mul (k.x t ht z)).add ((h.x t ht z).mul (k.xx t ht z))).congr_deriv (by ring)
lemma Jet.const (c : ℝ) : Jet (fun _ _ => c) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) :=
  ⟨fun _ _ z => hasDerivAt_const z c,fun _ _ z => hasDerivAt_const z 0,
    fun t _ _ => (hasDerivAt_const t c).hasDerivWithinAt⟩
lemma Jet.rank : Jet (fun t _ : ℝ => t) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) :=
  ⟨fun t _ z => hasDerivAt_const z t,fun _ _ z => hasDerivAt_const z 0,
    fun t _ _ => (hasDerivAt_id t).hasDerivWithinAt⟩
lemma Jet.coeff {a da : ℝ → ℝ} (ha : ∀ t∈Ico (0:ℝ) 1,HasDerivWithinAt a (da t) (Ici t) t) :
    Jet (fun t _ => a t) (fun _ _ => 0) (fun _ _ => 0) (fun t _ => da t) :=
  ⟨fun t _ z => hasDerivAt_const z (a t),fun _ _ z => hasDerivAt_const z 0,fun t ht _ => ha t ht⟩
lemma Jet.inv {u ux uxx ut : ℝ → ℝ → ℝ} (h : Jet u ux uxx ut)
    (hn : ∀ t∈Icc (0:ℝ) 1,∀ z,u t z≠0) :
    Jet (fun t z => (u t z)⁻¹) (fun t z => -ux t z/(u t z)^2)
      (fun t z => 2*(ux t z)^2/(u t z)^3-uxx t z/(u t z)^2)
      (fun t z => -ut t z/(u t z)^2) := by
  refine ⟨fun t ht z => (h.x t ht z).inv (hn t ht z),fun t ht z => ?_,
    fun t ht z => (h.time t ht z).inv (hn t ⟨ht.1,ht.2.le⟩ z)⟩
  exact ((h.xx t ht z).neg.div ((h.x t ht z).pow 2) (pow_ne_zero 2 (hn t ht z))).congr_deriv (by simp only [Pi.pow_apply,Pi.neg_apply]; field_simp [hn t ht z]; ring)
end Hessian
end MicroscopicJamming

 
open Set Filter
open scoped Topology BigOperators

namespace MicroscopicJamming
namespace Parameter
open Higher
lemma RankFamilyData.parameter_growth {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) :
    (∀ k,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv k (pjet F 0 t))) ∧
    (∀ k,UniformPolynomialGrowth (Icc 0 1) (fun t => iteratedDeriv k (pjet2 F 0 t))) := by
  have hj := hf.parameter_jets hr
  constructor
  · intro k
    obtain ⟨d,C,hC,hb⟩ := growth_limit (((field1_poly hf).bounds k).comp (seqNodes2 hr) (fun _ _ => trivial))
      (fun t ht x => (hf.first_jet_limit hr k).tendsto_at ht x)
    exact ⟨d,C,hC,fun t ht x => by dsimp only; rw [hj.1.2 k t ht]; exact hb t ht x⟩
  · intro k
    obtain ⟨d,C,hC,hb⟩ := growth_limit (((field2_poly hf).bounds k).comp (seqNodes3 hr) (fun _ _ => trivial))
      (fun t ht x => (hf.second_jet_limit hr k).tendsto_at ht x)
    exact ⟨d,C,hC,fun t ht x => by dsimp only; rw [hj.2.2 k t ht]; exact hb t ht x⟩

lemma RankFamilyData.parameter_terminal {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) :
    (∀ x,pjet F 0 1 x=0) ∧ (∀ x,pjet2 F 0 1 x=0) := by
  have h0 : (0:ℝ)∈Ioo (-r) r := ⟨by linarith,hr⟩
  constructor
  · intro x
    apply tendsto_nhds_unique ((hf.first_jet_limit hr 0).tendsto_at (by norm_num : (1:ℝ)∈Icc 0 1) x)
    convert tendsto_const_nhds (x:=(0:ℝ)) using 1
    funext n
    simp only [iteratedDeriv_zero,field1,dd1,hf.terminal _ (paramSeq_mem hr n) 0 h0 x,sub_self,zero_div]
  · intro x
    apply tendsto_nhds_unique ((hf.second_jet_limit hr 0).tendsto_at (by norm_num : (1:ℝ)∈Icc 0 1) x)
    convert tendsto_const_nhds (x:=(0:ℝ)) using 1
    funext n
    simp only [iteratedDeriv_zero,field2,dd2,dd1,hf.terminal _ (paramSeq_mem hr n) 0 h0 x,
      hf.terminal _ (twice_paramSeq_mem hr n) 0 h0 x,sub_self,zero_div]

lemma RankFamilyData.parameter_time_jets {r : ℝ} (hr : 0<r) {A B : ℝ → ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hf : RankFamilyData (Ioo (-r) r) A B F) :
    (∀ n,∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (pjet F 0 s) x)
      (iteratedDeriv n (linearRhs A B (F 0) (pjet F 0) t) x) (Ici t) t) ∧
    (∀ n,∀ t∈Ico (0:ℝ) 1,∀ x,HasDerivWithinAt (fun s => iteratedDeriv n (pjet2 F 0 s) x)
      (iteratedDeriv n (quadraticRhs A B (F 0) (pjet F 0) (pjet2 F 0) t) x) (Ici t) t) := by
  have hj := hf.parameter_jets hr
  have hd := hf.parameter_equations hr
  have h0 : (0:ℝ)∈Ioo (-r) r := ⟨by linarith,hr⟩
  have hG := linearRhs_smooth hf.Acont hf.Bcont (hf.smooth 0 h0) hj.1.1
  have hH := quadraticRhs_smooth hf.Acont hf.Bcont (hf.smooth 0 h0) hj.1.1 hj.2.1
  exact ⟨evolution_all_jets (by norm_num) (hj.1.1.2 0) hG.2 hj.1.1.1 hG.1 hd.1,
    evolution_all_jets (by norm_num) (hj.2.1.2 0) hH.2 hj.2.1.1 hH.1 hd.2⟩
end Parameter
end MicroscopicJamming

 
open Set
open scoped BigOperators

namespace MicroscopicJamming
namespace Hessian
open Higher Parameter

lemma smooth_jet {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iteratedDeriv n f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  simpa only [iteratedDeriv_iteratedDeriv] using (contDiff_iff_iteratedDeriv.mp hf).2 (k+n) (by simp)

def ftime (A t : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  -A*(f (n+2)+t*∑ i∈Finset.range (n+1),(n.choose i:ℝ)*f (i+1)*f (n-i+1))
def vtime (A B t : ℝ) (f v : ℕ → ℝ) (n : ℕ) : ℝ :=
  -B*(f (n+2)+t*∑ i∈Finset.range (n+1),(n.choose i:ℝ)*f (i+1)*f (n-i+1))-
  A*v (n+2)-2*A*t*∑ i∈Finset.range (n+1),(n.choose i:ℝ)*f (i+1)*v (n-i+1)
def gtime (A B t : ℝ) (f v g : ℕ → ℝ) : ℝ :=
  -A*t*(v 1)^2-B*(v 2+2*t*f 1*v 1)-A*g 2-2*A*t*f 1*g 1

lemma iterated_rhs (A t : ℝ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => -A*(iteratedDeriv 2 f y+t*(iteratedDeriv 1 f y)^2)) x=
    ftime A t (fun k => iteratedDeriv k f x) n := by
  have hc (k : ℕ) : ContDiff ℝ (n:WithTop ℕ∞) (iteratedDeriv k f) :=
    smooth_jet hf k |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_fun_add (hc 2).contDiffAt (contDiff_const.mul ((hc 1).pow 2)).contDiffAt]
  rw [iteratedDeriv_const_mul_field]
  simp only [pow_two]
  rw [iteratedDeriv_fun_mul (hc 1).contDiffAt (hc 1).contDiffAt]
  simp only [iteratedDeriv_iteratedDeriv,ftime]

lemma iterated_linearRhs {A B : ℝ → ℝ} {f v : ℝ → ℝ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f t))
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v t)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (linearRhs A B f v t) x=
      vtime (A t) (B t) t (fun k => iteratedDeriv k (f t) x) (fun k => iteratedDeriv k (v t) x) n := by
  have hc (k : ℕ) : ContDiff ℝ (n:WithTop ℕ∞) (iteratedDeriv k (f t)) :=
    smooth_jet hf k |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  have hd (k : ℕ) : ContDiff ℝ (n:WithTop ℕ∞) (iteratedDeriv k (v t)) :=
    smooth_jet hv k |>.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  have hbase := (contDiff_const (c:= -B t)).mul ((hc 2).add ((contDiff_const (c:=t)).mul ((hc 1).pow 2)))
  have hU := (contDiff_const (c:=A t)).mul (hd 2)
  have hV := ((contDiff_const (c:=2*A t*t)).mul (hc 1)).mul (hd 1)
  unfold linearRhs
  rw [iteratedDeriv_fun_sub (hbase.sub hU).contDiffAt hV.contDiffAt,
    iteratedDeriv_fun_sub hbase.contDiffAt hU.contDiffAt]
  rw [iterated_rhs (B t) t hf n x,iteratedDeriv_const_mul_field]
  have he : (fun y => 2*A t*t*iteratedDeriv 1 (f t) y*iteratedDeriv 1 (v t) y)=
      fun y => (2*A t*t)*(iteratedDeriv 1 (f t) y*iteratedDeriv 1 (v t) y) := by funext y; ring
  rw [he,iteratedDeriv_const_mul_field,iteratedDeriv_fun_mul (hc 1).contDiffAt (hd 1).contDiffAt]
  simp only [ftime,vtime,iteratedDeriv_iteratedDeriv]
end Hessian
end MicroscopicJamming

end

end OAI
