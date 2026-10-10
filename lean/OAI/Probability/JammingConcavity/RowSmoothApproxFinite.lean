import Mathlib
import OAI.Probability.JammingConcavity.RowFiniteDiagonalRowDirectionPairingTendsto
import OAI.Probability.JammingConcavity.RowProfileAnalytic

namespace OAI

/-! Row Smooth Approx Finite. -/

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
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory ProbabilityTheory
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming

def rowTransitionStep (a δ s : ℝ) : ℝ := Real.smoothTransition ((s-a)/(δ*(1-a)))

lemma rowTransitionStep_smooth (a δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rowTransitionStep a δ) := by
  unfold rowTransitionStep
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma rowTransitionStep_mono {a δ : ℝ} (ha : a<1) (hδ : 0<δ) :
    Monotone (rowTransitionStep a δ) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (sub_le_sub_right hst a) (mul_nonneg hδ.le (sub_nonneg.mpr ha.le))

lemma rowTransitionStep_endpoints {a δ : ℝ} (ha : 0≤a) (ha1 : a<1)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    rowTransitionStep a δ 0=0 ∧ rowTransitionStep a δ 1=1 := by
  constructor
  · apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · apply Real.smoothTransition.one_of_one_le
    apply (one_le_div (by positivity : 0<δ*(1-a))).mpr
    nlinarith

lemma rowTransitionStep_limit {a s : ℝ} (ha : a<1) (hs : s≠a) :
    Tendsto (fun n : ℕ => rowTransitionStep a (1/((n:ℝ)+2)) s) atTop
      (𝓝 (if a ≤ s then (1:ℝ) else 0)) := by
  by_cases hsa : s≤a
  · have hval (n : ℕ) : rowTransitionStep a (1/((n:ℝ)+2)) s=0 := by
      apply Real.smoothTransition.zero_of_nonpos
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsa) (by positivity)
    simp only [hval]
    rw [ite_eq_right (not_le.mpr (lt_of_le_of_ne hsa hs))]
    exact tendsto_const_nhds
  · have hpos : 0<s-a := by linarith
    have hev := (tendsto_atTop.mp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)) ((1-a)/(s-a))
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    rw [ite_eq_left (by linarith : a ≤ s)]
    apply Eq.symm
    apply Real.smoothTransition.one_of_one_le
    apply (one_le_div (by positivity : 0<(1/((n:ℝ)+2))*(1-a))).mpr
    have hh : 1-a≤(n:ℝ)*(s-a) := (div_le_iff₀ hpos).mp hn
    calc
      _ = (1-a)/((n:ℝ)+2) := by ring
      _ ≤ s-a := (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).mpr (by nlinarith)
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace MicroscopicJamming

def rowFiniteSmoothBase {k : ℕ} (a w : Fin k → ℝ) (r d δ s : ℝ) : ℝ :=
  r*rowTransitionStep 0 δ s+(∑ j, w j*rowTransitionStep (a j) δ s)+
    d*rowTransitionStep (1-δ) δ s

def rowFiniteSmooth {k : ℕ} (a w : Fin k → ℝ) (r d Q δ s : ℝ) : ℝ :=
  δ*(Q*s)+(1-δ)*rowFiniteSmoothBase a w r d δ s

lemma rowFiniteSmoothBase_smooth {k : ℕ} (a w : Fin k → ℝ) (r d δ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (rowFiniteSmoothBase a w r d δ) := by
  unfold rowFiniteSmoothBase
  exact ((contDiff_const.mul (rowTransitionStep_smooth 0 δ)).add
    (ContDiff.sum (fun j _ => contDiff_const.mul (rowTransitionStep_smooth (a j) δ)))).add
      (contDiff_const.mul (rowTransitionStep_smooth (1-δ) δ))

lemma rowFiniteSmoothBase_mono {k : ℕ} {a w : Fin k → ℝ} {r d δ : ℝ}
    (ha : ∀ j, a j<1) (hw : ∀ j, 0≤w j) (hr : 0≤r) (hd : 0≤d)
    (hδ : 0<δ) : Monotone (rowFiniteSmoothBase a w r d δ) := by
  intro s t hst
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_left (rowTransitionStep_mono (by norm_num) hδ hst) hr
    · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (rowTransitionStep_mono (ha j) hδ hst) (hw j))
  · exact mul_le_mul_of_nonneg_left (rowTransitionStep_mono (by linarith) hδ hst) hd

lemma rowFiniteSmooth_profile {k : ℕ} {a w : Fin k → ℝ} {r d Q δ : ℝ}
    (ha : ∀ j, 0≤a j ∧ a j<1) (hw : ∀ j, 0≤w j) (hr : 0≤r) (hd : 0≤d)
    (hQ : 0<Q) (htotal : r+(∑ j,w j)+d=Q) (hδ : 0<δ) (hδ1 : δ≤1) :
    RowSmoothProfile Q (rowFiniteSmooth a w r d Q δ) := by
  have hb := rowFiniteSmoothBase_smooth a w r d δ
  have hm := rowFiniteSmoothBase_mono (fun j => (ha j).2) hw hr hd hδ
  have h0 := rowTransitionStep_endpoints (a:=0) (by norm_num) (by norm_num) hδ hδ1
  have hj := fun j => rowTransitionStep_endpoints (ha j).1 (ha j).2 hδ hδ1
  have h1 := rowTransitionStep_endpoints (a:=1-δ) (by linarith) (by linarith) hδ hδ1
  refine ⟨((contDiff_const.mul (contDiff_const.mul contDiff_id)).add (contDiff_const.mul hb)),?_,?_,?_⟩
  · simp only [rowFiniteSmooth,rowFiniteSmoothBase,h0.1,h1.1,fun j => (hj j).1,
      mul_zero,Finset.sum_const_zero,add_zero]
  · simp only [rowFiniteSmooth,rowFiniteSmoothBase,h0.2,h1.2,fun j => (hj j).2,mul_one]
    rw [htotal]; ring
  · intro s hs
    have dh := (((hasDerivAt_id s).const_mul Q).const_mul δ).add
      ((hb.differentiable (by simp) s).hasDerivAt.const_mul (1-δ))
    change HasDerivAt (rowFiniteSmooth a w r d Q δ) _ s at dh
    rw [dh.deriv]
    have hn : 0≤deriv (rowFiniteSmoothBase a w r d δ) s := hm.deriv_nonneg
    nlinarith [mul_pos hδ hQ,mul_nonneg (sub_nonneg.mpr hδ1) hn]
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace MicroscopicJamming
lemma rowDelta_tendsto : Tendsto (fun n : ℕ => 1/((n:ℝ)+2)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

lemma rowTransitionTail_limit {s : ℝ} (hs : s<1) :
    Tendsto (fun n : ℕ => rowTransitionStep (1-1/((n:ℝ)+2)) (1/((n:ℝ)+2)) s) atTop (𝓝 0) := by
  have hev := rowDelta_tendsto.eventually (gt_mem_nhds (show (0:ℝ)<1-s by linarith))
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with n hn
  symm
  apply Real.smoothTransition.zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  have hp : 0<(1:ℝ)/((n:ℝ)+2) := by positivity
  exact mul_nonneg hp.le (by linarith)

lemma rowFiniteSmooth_limit {k : ℕ} {a w : Fin k → ℝ} {r d Q s : ℝ}
    (ha : ∀ j, a j<1) (hs : s∈Set.Ioo (0:ℝ) 1) (hne : ∀ j,s≠a j) :
    Tendsto (fun n : ℕ => rowFiniteSmooth a w r d Q (1/((n:ℝ)+2)) s) atTop
      (𝓝 (r+∑ j, w j*(if a j ≤ s then (1:ℝ) else 0))) := by
  have h0 := rowTransitionStep_limit (a:=0) (by norm_num) (ne_of_gt hs.1)
  simp only [ite_eq_left hs.1.le] at h0
  have hb := (((tendsto_const_nhds (x:=r)).mul h0).add
    (tendsto_finsetSum Finset.univ (fun j _ => (tendsto_const_nhds (x:=w j)).mul (rowTransitionStep_limit (ha j) (hne j))))).add
      ((tendsto_const_nhds (x:=d)).mul (rowTransitionTail_limit hs.2))
  have hh := (rowDelta_tendsto.mul (tendsto_const_nhds (x:=Q*s))).add
    (((tendsto_const_nhds (x:=(1:ℝ))).sub rowDelta_tendsto).mul hb)
  simpa only [rowFiniteSmooth,rowFiniteSmoothBase,mul_one,mul_zero,zero_mul,one_mul,sub_zero,add_zero,zero_add] using hh

lemma rowFiniteSmooth_L1 {k : ℕ} {a w : Fin k → ℝ} {r d Q : ℝ}
    (ha : ∀ j, 0 ≤ a j ∧ a j<1) (hw : ∀ j, 0 ≤ w j) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hQ : 0<Q) (htotal : r+(∑ j,w j)+d=Q) :
    Tendsto (fun n : ℕ => ∫ s in (0:ℝ)..1,
      |rowFiniteSmooth a w r d Q (1/((n:ℝ)+2)) s-(r+∑ j, w j*(if a j ≤ s then (1:ℝ) else 0))|)
      atTop (𝓝 0) := by
  let f : ℝ → ℝ := fun s => r+∑ j, w j*(if a j ≤ s then (1:ℝ) else 0)
  have hf : Measurable f := by
    dsimp [f]
    have hm (j : Fin k) : Measurable (fun s : ℝ => if a j ≤ s then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const
    fun_prop
  have hp (n : ℕ) : RowSmoothProfile Q (rowFiniteSmooth a w r d Q (1/((n:ℝ)+2))) :=
    rowFiniteSmooth_profile ha hw hr hd hQ htotal (by positivity) (by
      apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+2)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hfb (s : ℝ) : 0 ≤ f s ∧ f s ≤ Q := by
    have hsum0 : 0 ≤ ∑ j, w j*(if a j ≤ s then (1:ℝ) else 0) := Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (by split_ifs <;> norm_num))
    have hsum1 : (∑ j, w j*(if a j ≤ s then (1:ℝ) else 0)) ≤ ∑ j,w j := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs <;> simp [hw j]
    dsimp [f]; constructor <;> linarith
  have hconv : ∀ᵐ s ∂volume.restrict (Set.Ioc (0:ℝ) 1),
      Tendsto (fun n : ℕ => |rowFiniteSmooth a w r d Q (1/((n:ℝ)+2)) s-f s|) atTop (𝓝 0) := by
    have hfinite : ∀ᵐ s ∂volume, ∀ j : Fin k,s≠a j := by
      simpa only [ae_all_iff] using (fun j => (show ∀ᵐ s : ℝ ∂volume,s≠a j from by rw [ae_iff]; simp))
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (show ∀ᵐ s : ℝ ∂volume,s≠1 from by rw [ae_iff]; simp),ae_restrict_of_ae hfinite] with s hs hs1 hj
    have hh := (rowFiniteSmooth_limit (w:=w) (r:=r) (d:=d) (Q:=Q) (fun j => (ha j).2) ⟨hs.1,lt_of_le_of_ne hs.2 hs1⟩ hj).sub (tendsto_const_nhds (x:=f s))
    simpa only [f,sub_self,abs_zero] using hh.abs
  have hlim := tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Set.Ioc (0:ℝ) 1)) (f:=fun _ : ℝ => (0:ℝ)) (bound:=fun _ : ℝ => Q)
    (fun n => ((hp n).1.continuous.measurable.sub hf).abs.aestronglyMeasurable)
    (integrable_const Q)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs,abs_abs]
      have hb := (hp n).mapsTo (show s∈Set.Icc (0:ℝ) 1 from ⟨hs.1.le,hs.2⟩)
      simp only [Pi.sub_apply]
      exact abs_le.mpr ⟨by linarith [(hfb s).1,(hfb s).2,hb.1,hb.2],by linarith [(hfb s).1,(hfb s).2,hb.1,hb.2]⟩)
    hconv
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),integral_zero,Pi.sub_apply,f] using hlim
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology BigOperators NNReal

namespace MicroscopicJamming
def rowSmoothProfile {Q : ℝ} {f : ℝ → ℝ} (hf : RowSmoothProfile Q f) : SphericalProfile where
  val := f
  mono := hf.strictMonoOn.monotoneOn
  nonneg := fun _s hs => (hf.mapsTo hs).1
lemma RowFiniteProfile.smoothApprox {Q : ℝ} (hQ : 0<Q) (P : RowFiniteProfile Q) :
    ∃ pn : ℕ → SphericalProfile, (∀ n,RowSmoothProfile Q (pn n).val) ∧
      Tendsto (fun n => sphericalProfileDistance (pn n).val P.profile.val) atTop (𝓝 0) := by
  let a : Fin P.ranks.length → ℝ := fun j => P.ranks[j.val]!
  let w : Fin P.ranks.length → ℝ := fun j => P.increment j
  have ha (j : Fin P.ranks.length) : 0 ≤ a j ∧ a j<1 := by
    have hm : P.ranks[j.val]! ∈ P.ranks := by
      rw [getElem!_pos P.ranks j.val j.isLt]
      exact List.getElem_mem j.isLt
    exact ⟨(P.valid _ hm).1.le,(P.valid _ hm).2⟩
  have hw (j : Fin P.ranks.length) : 0 ≤ w j := (P.increment j).coe_nonneg
  have ht : (P.root:ℝ)+(∑ j,w j)+(P.residual:ℝ)=Q := by
    simpa only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum] using P.diagonal
  have hprof : P.profile.val=(fun s => (P.root:ℝ)+∑ j,w j*(if a j ≤ s then (1:ℝ) else 0)) := by
    funext s
    rw [RowFiniteProfile.profile,rowCascadeProfile_sum _ P.ordered,rowGaussianBlocks_cumulative]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [w,a]
    split_ifs <;> simp
  let hf (n : ℕ) := rowFiniteSmooth_profile ha hw P.root.coe_nonneg P.residual.coe_nonneg hQ ht
    (show (0:ℝ)<1/((n:ℝ)+2) by positivity) (show (1:ℝ)/((n:ℝ)+2) ≤ 1 by
      apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+2)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n])
  refine ⟨fun n => rowSmoothProfile (hf n),fun n => hf n,?_⟩
  rw [hprof]
  exact rowFiniteSmooth_L1 ha hw P.root.coe_nonneg P.residual.coe_nonneg hQ ht
lemma rowSmooth_density {Q : ℝ} (hQ : 0<Q) (p : SphericalProfile)
    (hp : ∀ s∈Set.Icc 0 1,p.val s ≤ Q) {ε : ℝ} (hε : 0<ε) :
    ∃ q : SphericalProfile, RowSmoothProfile Q q.val ∧ sphericalProfileDistance q.val p.val<ε := by
  have htop : p.val 1 ≤ Q := hp 1 (by norm_num)
  obtain ⟨n,hn⟩ := ((rowGrid_distance_tendsto p htop).eventually (gt_mem_nhds (half_pos hε))).exists
  obtain ⟨pn,hpn,hlim⟩ := (p.rowGrid htop n).smoothApprox hQ
  obtain ⟨m,hm⟩ := (hlim.eventually (gt_mem_nhds (half_pos hε))).exists
  refine ⟨pn m,hpn m,?_⟩
  exact (sphericalProfileDistance_triangle (pn m) (p.rowGrid htop n).profile p).trans_lt (by linarith)
lemma rowSmooth_approximation {Q : ℝ} (hQ : 0<Q) (p : SphericalProfile)
    (hp : ∀ s∈Set.Icc 0 1,p.val s ≤ Q) :
    ∃ pn : ℕ → SphericalProfile, (∀ n,RowSmoothProfile Q (pn n).val) ∧
      Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) atTop (𝓝 0) := by
  have hex (n : ℕ) := rowSmooth_density hQ p hp (show (0:ℝ)<1/((n:ℝ)+1) by positivity)
  choose pn hpn hb using hex
  refine ⟨pn,hpn,?_⟩
  exact squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _) (fun n => (hb n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma rowChord_bound {Q : ℝ} (p q : SphericalProfile) (hp : ∀ s∈Set.Icc 0 1,p.val s ≤ Q)
    (hq : ∀ s∈Set.Icc 0 1,q.val s ≤ Q) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ s∈Set.Icc 0 1,(p.rowChord q θ hθ hθ1).val s ≤ Q := by
  intro s hs
  change (1-θ)*p.val s+θ*q.val s ≤ Q
  nlinarith [mul_le_mul_of_nonneg_left (hp s hs) (sub_nonneg.mpr hθ1),mul_le_mul_of_nonneg_left (hq s hs) hθ]
lemma rowChord_smooth {Q : ℝ} (p q : SphericalProfile) (hp : RowSmoothProfile Q p.val)
    (hq : RowSmoothProfile Q q.val) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    RowSmoothProfile Q (p.rowChord q θ hθ hθ1).val := by
  have he : (p.rowChord q θ hθ hθ1).val=(fun s => p.val s+θ*(q.val s-p.val s)) := by funext s; dsimp [SphericalProfile.rowChord]; ring
  rw [he]
  exact rowSmooth_chord hp hq ⟨hθ,hθ1⟩
lemma rowChord_distance {Q : ℝ} (p q r v : SphericalProfile)
    (hp : p.val 1 ≤ Q) (hq : q.val 1 ≤ Q) (hr : r.val 1 ≤ Q) (hv : v.val 1 ≤ Q)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    sphericalProfileDistance (p.rowChord q θ hθ hθ1).val (r.rowChord v θ hθ hθ1).val ≤
      (1-θ)*sphericalProfileDistance p.val r.val+θ*sphericalProfileDistance q.val v.val := by
  have hh := rowProfileMix_distance (Q:=Q) ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩ ⟨v,hv⟩ θ
  simpa only [rowProfileMix,rowUnitClip,min_eq_right hθ1,max_eq_right hθ,SphericalProfile.rowChord] using hh
lemma rowProfileValue_tendsto {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    (p : SphericalProfile) (pn : ℕ → SphericalProfile)
    (hp : ∀ s∈Set.Icc 0 1,p.val s ≤ Q) (hpn : ∀ n s,s∈Set.Icc 0 1 → (pn n).val s ≤ Q)
    (hlim : Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) atTop (𝓝 0)) :
    Tendsto (fun n => rowProfileValue u Q (pn n)) atTop (𝓝 (rowProfileValue u Q p)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (g:=fun n => L^2/2*sphericalProfileDistance (pn n).val p.val) (fun _ => dist_nonneg)
    (fun n => by rw [Real.dist_eq]; exact rowProfileValue_lipschitz hQ hu hub (pn n) p (hpn n) hp)
  simpa only [mul_zero] using hlim.const_mul (L^2/2)
lemma rowProfileValue_smooth_concave {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hc : ConcaveOn ℝ univ u)
    (p q : SphericalProfile) (hp : RowSmoothProfile Q p.val) (hq : RowSmoothProfile Q q.val)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1-θ)*rowProfileValue u Q p+θ*rowProfileValue u Q q ≤ rowProfileValue u Q (p.rowChord q θ hθ hθ1) := by
  obtain ⟨f,hf,_⟩ := row_rank_existence_unique hQ hu hp
  obtain ⟨g,hg,_⟩ := row_rank_existence_unique hQ hu hq
  obtain ⟨h,hh,_⟩ := row_rank_existence_unique hQ hu (rowChord_smooth p q hp hq hθ hθ1)
  rw [rowProfileValue_smooth hQ hu p hp f hf,rowProfileValue_smooth hQ hu q hq g hg,
    rowProfileValue_smooth hQ hu _ (rowChord_smooth p q hp hq hθ hθ1) h hh]
  exact rowSmoothConcavity u p.val q.val A B C κ Q hQ hu hc hp hq θ hθ hθ1 f g h hf hg hh
lemma rowProfileValue_concave {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    (hc : ConcaveOn ℝ univ u) (p q : SphericalProfile)
    (hp : ∀ s∈Set.Icc 0 1,p.val s ≤ Q) (hq : ∀ s∈Set.Icc 0 1,q.val s ≤ Q)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1-θ)*rowProfileValue u Q p+θ*rowProfileValue u Q q ≤ rowProfileValue u Q (p.rowChord q θ hθ hθ1) := by
  obtain ⟨pn,hpn,hlp⟩ := rowSmooth_approximation hQ p hp
  obtain ⟨qn,hqn,hlq⟩ := rowSmooth_approximation hQ q hq
  have hpb (n : ℕ) (s : ℝ) (hs : s∈Set.Icc 0 1) := ((hpn n).mapsTo hs).2
  have hqb (n : ℕ) (s : ℝ) (hs : s∈Set.Icc 0 1) := ((hqn n).mapsTo hs).2
  let rn (n : ℕ) := (pn n).rowChord (qn n) θ hθ hθ1
  have hlr : Tendsto (fun n => sphericalProfileDistance (rn n).val (p.rowChord q θ hθ hθ1).val) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sphericalProfileDistance_nonneg _ _)
      (fun n => rowChord_distance (pn n) (qn n) p q (hpb n 1 (by norm_num)) (hqb n 1 (by norm_num))
        (hp 1 (by norm_num)) (hq 1 (by norm_num)) hθ hθ1)
    simpa only [mul_zero,add_zero] using (hlp.const_mul (1-θ)).add (hlq.const_mul θ)
  have h1 := rowProfileValue_tendsto hQ hu hub p pn hp hpb hlp
  have h2 := rowProfileValue_tendsto hQ hu hub q qn hq hqb hlq
  have h3 := rowProfileValue_tendsto hQ hu hub (p.rowChord q θ hθ hθ1) rn (rowChord_bound p q hp hq hθ hθ1)
    (fun n => rowChord_bound (pn n) (qn n) (hpb n) (hqb n) hθ hθ1) hlr
  exact le_of_tendsto_of_tendsto ((h1.const_mul (1-θ)).add (h2.const_mul θ)) h3
    (Eventually.of_forall (fun n => rowProfileValue_smooth_concave hQ hu hc (pn n) (qn n) (hpn n) (hqn n) hθ hθ1))
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma gaussianRankProfile_nonneg {rs : List (ℝ × ℝ)}
    (hrs : ∀ r∈rs,0 ≤ r.2) (s : ℝ) : 0 ≤ gaussianRankProfile rs s := by
  unfold gaussianRankProfile
  apply List.sum_nonneg
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
  split_ifs <;> first | exact hrs r hr | exact le_rfl
lemma gaussianRankProfile_zero_below {rs : List (ℝ × ℝ)} {a s : ℝ}
    (ha : ∀ r∈rs,a ≤ r.1) (hs : s<a) : gaussianRankProfile rs s=0 := by
  unfold gaussianRankProfile
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
  exact ite_eq_right (not_le.mpr (hs.trans_le (ha r hr)))
lemma profileRankLaw_Iio {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : profileRankLaw.real (Set.Iio a)=a := by
  have hset : Set.Iio a ∩ Set.Ioc (0:ℝ) 1=Set.Ioo 0 a := by
    ext s; simp only [mem_inter_iff,Set.mem_Iio,Set.mem_Ioc,Set.mem_Ioo]
    constructor
    · exact fun h => ⟨h.2.1,h.1⟩
    · exact fun h => ⟨h.2,h.1,h.2.le.trans ha1⟩
  rw [measureReal_def,profileRankLaw,Measure.restrict_apply measurableSet_Iio,hset,Real.volume_Ioo]
  simpa only [sub_zero] using ENNReal.toReal_ofReal ha
lemma gaussianRankProfile_CDF (rs : List (ℝ × ℝ))
    (hrs : ∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hord : rs.Pairwise (fun r s => r.1 ≤ s.1)) {t : ℝ}
    (ht : t∈Set.Ico 0 (gaussianStepTime rs)) :
    profileRankLaw.real {s | gaussianRankProfile rs s ≤ t}=gaussianStepRightCoefficient rs t := by
  induction rs generalizing t with
  | nil => simp only [gaussianStepTime,List.map_nil,List.sum_nil,Set.mem_Ico] at ht; linarith [ht.1,ht.2]
  | cons r rs ih =>
    have hr := hrs r (by simp)
    have htail : ∀ v∈rs,0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2 := fun v hv => hrs v (by simp [hv])
    obtain ⟨ha,hord⟩ := List.pairwise_cons.mp hord
    by_cases htt : t<r.2
    · have he : {s | gaussianRankProfile (r::rs) s ≤ t}=Set.Iio r.1 := by
        ext s
        simp only [mem_ofPred_eq,Set.mem_Iio]
        by_cases hs : s<r.1
        · rw [show gaussianRankProfile (r::rs) s=0 from by
            exact gaussianRankProfile_zero_below (fun v hv => by
              rcases List.mem_cons.mp hv with hv | hv
              · subst v; exact le_rfl
              · exact ha v hv) hs]
          exact iff_of_true ht.1 hs
        · have hs' : r.1 ≤ s := le_of_not_gt hs
          have he : gaussianRankProfile (r::rs) s=r.2+gaussianRankProfile rs s := by
            simp [gaussianRankProfile,hs']
          rw [he]
          exact iff_of_false (by linarith [gaussianRankProfile_nonneg (fun v hv => (htail v hv).2.2) s]) hs
      rw [he,profileRankLaw_Iio hr.1 hr.2.1]
      simp only [gaussianStepRightCoefficient,ite_eq_left htt]
    · have htt' : r.2 ≤ t := le_of_not_gt htt
      have he : {s | gaussianRankProfile (r::rs) s ≤ t}={s | gaussianRankProfile rs s ≤ t-r.2} := by
        ext s
        simp only [mem_ofPred_eq]
        by_cases hs : s<r.1
        · have hz := gaussianRankProfile_zero_below ha hs
          simp only [gaussianRankProfile,List.map_cons,List.sum_cons,ite_eq_right (not_le.mpr hs)]
          change 0+gaussianRankProfile rs s ≤ t ↔ gaussianRankProfile rs s ≤ t-r.2
          rw [hz]
          exact iff_of_true (by linarith [ht.1]) (by linarith)
        · have hs' : r.1 ≤ s := le_of_not_gt hs
          simp only [gaussianRankProfile,List.map_cons,List.sum_cons,ite_eq_left hs']
          change r.2+gaussianRankProfile rs s ≤ t ↔ gaussianRankProfile rs s ≤ t-r.2
          constructor <;> intro h <;> linarith
      rw [he,ih htail hord ⟨sub_nonneg.mpr htt',by have ht2 : t<r.2+gaussianStepTime rs := ht.2; linarith⟩]
      simp only [gaussianStepRightCoefficient,ite_eq_right htt]
lemma RowPartition.CDF {Q : ℝ} (P : RowPartition Q) {t : ℝ} (ht : t∈Set.Ico 0 Q) :
    profileCDF P.profile t=gaussianStepRightCoefficient P.blocks t := by
  exact gaussianRankProfile_CDF P.blocks P.valid P.ordered (by simpa only [P.total] using ht)
lemma RowPartition.CDF_ae {Q : ℝ} (P : RowPartition Q) :
    profileCDF P.profile =ᵐ[volume.restrict (Set.Ioc 0 Q)] gaussianStepRightCoefficient P.blocks := by
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (show ∀ᵐ t : ℝ ∂volume,t≠Q from by rw [ae_iff]; simp)] with t ht hne
  exact P.CDF ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma rowProfileValue_partition {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    (P : RowPartition Q) : rowProfileValue u Q P.profile=gaussianRowComposition P.blocks u 0 := by
  have he (n : ℕ) : rowCoeffDistance Q
      (gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF P.profile) n)) (profileCDF P.profile)=
      rowCoeffDistance Q (gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF P.profile) n))
        (gaussianStepRightCoefficient P.blocks) := by
    unfold rowCoeffDistance
    rw [intervalIntegral.integral_of_le hQ.le,intervalIntegral.integral_of_le hQ.le]
    apply integral_congr_ae
    filter_upwards [P.CDF_ae] with t ht
    rw [ht]
  have hlim := rowCDFGrid_L1 hQ (profileCDF_monotone P.profile).measurable
    (profileCDF_bounds P.profile) (profileCDF_ae_continuous P.profile)
  have hseq : Tendsto (rowProfileSequence u Q P.profile) atTop (𝓝 (gaussianRowComposition P.blocks u 0)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (g:=fun n => L^2/2*rowCoeffDistance Q (gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF P.profile) n)) (profileCDF P.profile)) (fun _ => dist_nonneg)
    · intro n
      rw [Real.dist_eq]
      have hh := row_composition_L1_stability hQ hu hub
        (rowCDFGrid_valid hQ.le (profileCDF_bounds P.profile) n) P.valid
        (rowCDFGrid_time Q (profileCDF P.profile) n) P.total 0
      change |rowProfileSequence u Q P.profile n-gaussianRowComposition P.blocks u 0| ≤
        L^2/2*rowCoeffDistance Q (gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF P.profile) n))
          (gaussianStepRightCoefficient P.blocks) at hh
      rw [←he] at hh
      exact hh
    · simpa only [mul_zero,rowCoeffDistance] using hlim.const_mul (L^2/2)
  exact hseq.limUnder_eq
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
 

theorem rowProfileAnalytic : RowProfileAnalyticStatement := by
  intro u A B C κ Q L hQ hu hL hb
  have hub := rowAnalytic_bounded hu hL hb
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p _
    exact rowProfileSequence_converges hQ hu hub p
  · intro P
    exact rowProfileValue_partition hQ hu hub P
  · intro p q hp hq
    exact rowProfileValue_lipschitz hQ hu hub p q hp hq
  · intro p hp f hf
    exact rowProfileValue_smooth hQ hu p hp f hf
  · intro hc p q hp hq θ hθ hθ1
    exact rowProfileValue_concave hQ hu hub hc p q hp hq hθ hθ1
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 
def rowQuadraticHinge (z : ℝ) : ℝ := (1/2:ℝ)*(max (-1-z) 0)^2
 

def RowNonsmoothConcavityStatement : Prop :=
  ∀ (u : ℝ → ℝ),
    ((ConcaveOn ℝ univ u ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |u x-u y| ≤ L*|x-y|) ∨
      ∃ β : ℝ, 0 < β ∧ u=fun z => -β*rowQuadraticHinge z) →
    ∀ Q : ℝ, 0 ≤ Q →
    (∀ p : SphericalProfile, (∀ s ∈ Set.Icc 0 1, p.val s ≤ Q) →
      Tendsto (rowProfileSequence u Q p) atTop (𝓝 (rowProfileValue u Q p))) ∧
    (∀ P : RowPartition Q, rowProfileValue u Q P.profile=gaussianRowComposition P.blocks u 0) ∧
    (∀ p q : SphericalProfile,
      (∀ s ∈ Set.Icc 0 1,p.val s ≤ Q) → (∀ s ∈ Set.Icc 0 1,q.val s ≤ Q) →
      ∀ θ : ℝ, ∀ hθ : 0 ≤ θ, ∀ hθ1 : θ ≤ 1,
      (1-θ)*rowProfileValue u Q p+θ*rowProfileValue u Q q ≤
        rowProfileValue u Q (p.rowChord q θ hθ hθ1))
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 

def RowConcavityMainStatement : Prop :=
  (∀ (u : ℝ → ℝ) (A B C κ Q : ℝ), 0<Q →
    RowAnalyticTerminal u A B C κ Q → ConcaveOn ℝ univ u →
    ∀ p q : SphericalProfile, RowSmoothProfile Q p.val → RowSmoothProfile Q q.val →
    ∀ θ : ℝ, ∀ hθ : 0 ≤ θ, ∀ hθ1 : θ ≤ 1,
      (1-θ)*rowProfileValue u Q p+θ*rowProfileValue u Q q ≤
        rowProfileValue u Q (p.rowChord q θ hθ hθ1)) ∧
  RowNonsmoothConcavityStatement
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma row_uniform_grid_passage {f : ℕ → ℝ} {g : ℕ → ℕ → ℝ} {a e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hg : ∀ k,Tendsto (g k) atTop (𝓝 (a k)))
    (hb : ∀ k n,|f n-g k n| ≤ e k) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) ∧
    (∀ k,|limUnder atTop f-a k| ≤ e k) ∧ Tendsto a atTop (𝓝 (limUnder atTop f)) := by
  have hf : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k,hk⟩ := (he.eventually_lt_const (by positivity : 0<ε/4)).exists
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hg k).cauchySeq (ε/4) (by positivity)
    refine ⟨N,fun m hm n hn => ?_⟩
    have hh := hN m hm n hn
    rw [Real.dist_eq] at hh ⊢
    calc
      _ = |(f m-g k m)+(g k m-g k n)+(g k n-f n)| := by congr 1; ring
      _ ≤ |f m-g k m|+|g k m-g k n|+|g k n-f n| := abs_add_three _ _ _
      _ < ε := by rw [abs_sub_comm (g k n)]; linarith [hb k m,hb k n]
  have hlim := hf.tendsto_limUnder
  have hbound (k : ℕ) : |limUnder atTop f-a k| ≤ e k := le_of_tendsto ((hlim.sub (hg k)).abs) (Eventually.of_forall (hb k))
  refine ⟨hlim,hbound,?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) _ he
  intro k
  rw [Real.dist_eq,abs_sub_comm]
  exact hbound k
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
def RowProfileConclusions (u : ℝ → ℝ) (Q : ℝ) : Prop :=
  (∀ p : SphericalProfile, (∀ s∈Set.Icc 0 1,p.val s ≤ Q) →
    Tendsto (rowProfileSequence u Q p) atTop (𝓝 (rowProfileValue u Q p))) ∧
  (∀ P : RowPartition Q,rowProfileValue u Q P.profile=gaussianRowComposition P.blocks u 0) ∧
  (∀ p q : SphericalProfile,(∀ s∈Set.Icc 0 1,p.val s ≤ Q) → (∀ s∈Set.Icc 0 1,q.val s ≤ Q) →
    ∀ θ : ℝ,∀ hθ : 0 ≤ θ,∀ hθ1 : θ ≤ 1,
      (1-θ)*rowProfileValue u Q p+θ*rowProfileValue u Q q ≤ rowProfileValue u Q (p.rowChord q θ hθ hθ1))
lemma row_terminal_profile_passage {u : ℝ → ℝ} {v : ℕ → ℝ → ℝ} {Q : ℝ}
    {A B C L H e : ℕ → ℝ} (hQ : 0<Q)
    (hv : ∀ n,RowAnalyticTerminal (v n) (A n) (B n) (C n) 0 Q)
    (hvb : ∀ n,RowBoundedTerminal (v n) (L n) (H n)) (hvc : ∀ n,ConcaveOn ℝ univ (v n))
    (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ rs : List (ℝ × ℝ),(∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) → gaussianStepTime rs=Q →
      ∀ n,|gaussianRowComposition rs u 0-gaussianRowComposition rs (v n) 0| ≤ e n)
    (hfinite : ∀ rs : List (ℝ × ℝ),(∀ r∈rs,0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) → gaussianStepTime rs=Q →
      Tendsto (fun n => gaussianRowComposition rs (v n) 0) atTop (𝓝 (gaussianRowComposition rs u 0))) :
    RowProfileConclusions u Q := by
  have hg (p : SphericalProfile) := row_uniform_grid_passage he
    (fun n => rowProfileSequence_converges hQ (hv n) (hvb n) p)
    (fun k n => hb (rowCDFGrid Q (profileCDF p) n) (rowCDFGrid_valid hQ.le (profileCDF_bounds p) n)
      (rowCDFGrid_time Q (profileCDF p) n) k)
  have hlim (p : SphericalProfile) : Tendsto (fun n => rowProfileValue (v n) Q p) atTop (𝓝 (rowProfileValue u Q p)) := (hg p).2.2
  refine ⟨fun p _ => (hg p).1,?_,?_⟩
  · intro P
    have h1 := hlim P.profile
    have h2 := hfinite P.blocks P.valid P.total
    have heq (n : ℕ) := rowProfileValue_partition hQ (hv n) (hvb n) P
    simp_rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  · intro p q hp hq θ hθ hθ1
    exact le_of_tendsto_of_tendsto (((hlim p).const_mul (1-θ)).add ((hlim q).const_mul θ))
      (hlim (p.rowChord q θ hθ hθ1)) (Eventually.of_forall (fun n => rowProfileValue_concave hQ (hv n) (hvb n) (hvc n) p q hp hq hθ hθ1))
lemma row_composition_total_zero {rs : List (ℝ × ℝ)} (hrs : ∀ r∈rs,0 ≤ r.2)
    (hT : gaussianStepTime rs=0) (u : ℝ → ℝ) : gaussianRowComposition rs u=u := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have htail : ∀ r∈rs,0 ≤ r.2 := fun r hr => hrs r (List.mem_cons_of_mem _ hr)
    have hr : r.2=0 := by
      have hsum : r.2+gaussianStepTime rs=0 := by simpa [gaussianStepTime] using hT
      have h1 := hrs r (by simp)
      have h2 := gaussianStepTime_nonneg htail
      linarith
    have htime : gaussianStepTime rs=0 := by simpa [gaussianStepTime,hr] using hT
    rw [show gaussianRowComposition (r::rs) u=gaussianRowOperator r.1 r.2 (gaussianRowComposition rs u) from rfl,ih htail htime,hr]
    funext x
    exact gaussianRowOperator_zero r.1 u x
lemma rowProfile_zero (u : ℝ → ℝ) : RowProfileConclusions u 0 := by
  have hseq (p : SphericalProfile) (n : ℕ) : rowProfileSequence u 0 p n=u 0 := by
    exact congrFun (row_composition_total_zero (fun r hr => (rowCDFGrid_valid (le_refl 0) (profileCDF_bounds p) n r hr).2.2)
      (rowCDFGrid_time 0 (profileCDF p) n) u) 0
  have hsfun (p : SphericalProfile) : rowProfileSequence u 0 p=(fun _ : ℕ => u 0) := funext (hseq p)
  have hval (p : SphericalProfile) : rowProfileValue u 0 p=u 0 := by
    exact (show Tendsto (rowProfileSequence u 0 p) atTop (𝓝 (u 0)) by rw [hsfun]; exact tendsto_const_nhds).limUnder_eq
  refine ⟨?_,?_,?_⟩
  · intro p _
    simpa only [hval,hsfun] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => u 0) atTop (𝓝 (u 0)))
  · intro P
    rw [hval,row_composition_total_zero (fun r hr => (P.valid r hr).2.2) P.total]
  · intro p q _ _ θ hθ hθ1
    simp only [hval]
    nlinarith
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 

lemma row_weighted_terminal_bound {Q C L ε : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    {F G : ℝ → ℝ → ℝ} {m : ℝ → ℝ}
    (hcF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc 0 Q ×ˢ univ))
    (hcG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Set.Icc 0 Q ×ˢ univ))
    (hxF : ∀ t ∈ Set.Icc 0 Q, Differentiable ℝ (F t) ∧ Differentiable ℝ (deriv (F t)))
    (hxG : ∀ t ∈ Set.Icc 0 Q, Differentiable ℝ (G t) ∧ Differentiable ℝ (deriv (G t)))
    (htF : ∀ t ∈ Set.Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => F s x)
      (-(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)) (Set.Ici t) t)
    (htG : ∀ t ∈ Set.Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => G s x)
      (-(1/2:ℝ)*(deriv (deriv (G t)) x+m t*(deriv (G t) x)^2)) (Set.Ici t) t)
    (hm : ∀ t ∈ Set.Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hboundF : ∀ t ∈ Set.Icc 0 Q, ∀ x, |F t x| ≤ C*(1+x^2))
    (hboundG : ∀ t ∈ Set.Icc 0 Q, ∀ x, |G t x| ≤ C*(1+x^2))
    (hgradF : ∀ t ∈ Set.Icc 0 Q, ∀ x, |deriv (F t) x| ≤ L*(1+|x|))
    (hgradG : ∀ t ∈ Set.Icc 0 Q, ∀ x, |deriv (G t) x| ≤ L*(1+|x|))
    (hterm : ∀ x, |F Q x-G Q x| ≤ ε*(1+x^2)^2) :
    |F 0 0-G 0 0| ≤ ε*Real.exp ((10+8*L)*Q) := by
  let U := fun t x => F t x-G t x
  let b := fun t x => m t*(deriv (F t) x+deriv (G t) x)/2
  let d := fun t x => -(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)-
    (-(1/2:ℝ)*(deriv (deriv (G t)) x+m t*(deriv (G t) x)^2))
  have hdx (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      HasDerivAt (U t) (deriv (F t) x-deriv (G t) x) x :=
    ((hxF t ht).1 x).hasDerivAt.sub ((hxG t ht).1 x).hasDerivAt
  have hdx2 (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (U t)) (deriv (deriv (F t)) x-deriv (deriv (G t)) x) x := by
    have he : deriv (U t)=fun y => deriv (F t) y-deriv (G t) y := funext fun y => (hdx t ht y).deriv
    rw [he]
    exact ((hxF t ht).2 x).hasDerivAt.sub ((hxG t ht).2 x).hasDerivAt
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) : |b t x| ≤ L*(1+|x|) := by
    have hh : |deriv (F t) x+deriv (G t) x| ≤ 2*(L*(1+|x|)) :=
      (abs_add_le _ _).trans (by linarith [hgradF t ht x,hgradG t ht x])
    have h1 := mul_le_mul_of_nonneg_left hh (hm t ht).1
    have h2 := mul_le_mul_of_nonneg_right (hm t ht).2 (show 0 ≤ 2*(L*(1+|x|)) by positivity)
    dsimp [b]
    rw [abs_div,abs_mul,abs_of_nonneg (hm t ht).1]
    norm_num only [show |(2:ℝ)|=2 by norm_num]
    nlinarith
  have hg : Higher.UniformPolynomialGrowth (Set.Icc 0 Q) U := by
    refine ⟨2,2*C,by positivity,fun t ht x => ?_⟩
    calc
      |U t x| ≤ |F t x|+|G t x| := abs_sub _ _
      _ ≤ 2*C*(1+x^2) := by linarith [hboundF t ht x,hboundG t ht x]
      _ ≤ 2*C*(1+|x|)^2 := mul_le_mul_of_nonneg_left (by nlinarith [sq_abs x,abs_nonneg x]) (by positivity)
  have hp (t : ℝ) (ht : t ∈ Set.Ico 0 Q) (x : ℝ) :
      |d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+0*U t x| ≤ (0:ℝ)*(1+x^2)^(0+2) := by
    rw [(hdx2 t ⟨ht.1,ht.2.le⟩ x).deriv,(hdx t ⟨ht.1,ht.2.le⟩ x).deriv]
    have he : d t x+(1/2:ℝ)*(deriv (deriv (F t)) x-deriv (deriv (G t)) x)+
        b t x*(deriv (F t) x-deriv (G t) x)+0*U t x=0 := by dsimp [d,b]; ring
    rw [he]; simp
  have hh := VariableDiffusion.backward_polynomial_source_bound (a:=fun _ _ => (1/2:ℝ))
    (r:=fun _ _ => 0) 0 hQ hL (by norm_num : (0:ℝ) ≤ 1/2) (le_refl 0) hε (le_refl 0)
    (hcF.sub hcG) (fun t ht => ⟨fun x => (hdx t ht x).differentiableAt,fun x => (hdx2 t ht x).differentiableAt⟩)
    (fun t ht x => (htF t ht x).sub (htG t ht x)) (fun _ _ _ => ⟨by norm_num,le_rfl⟩)
    hb hg (fun _ _ _ => le_rfl) hp hterm 0 ⟨le_rfl,hQ.le⟩ 0
  have he : polynomialBarrier 0 (ε+0) (0+(4*(1/2:ℝ)*((0:ℕ)+2)^2+4*L*((0:ℕ)+2)+1)+1) Q 0 0 =
      ε*Real.exp ((10+8*L)*Q) := by
    have hcoef : (0+(4*(1/2:ℝ)*((0:ℕ)+2)^2+4*L*((0:ℕ)+2)+1)+1)=10+8*L := by norm_num; ring
    rw [hcoef]
    simp [polynomialBarrier]
  rw [he] at hh
  exact hh
end MicroscopicJamming

end

end OAI
