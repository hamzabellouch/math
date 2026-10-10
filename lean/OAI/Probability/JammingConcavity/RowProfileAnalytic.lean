import Mathlib
import OAI.Probability.JammingConcavity.RowFiniteDiagonal

namespace OAI

/-! Row Profile Analytic. -/

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace MicroscopicJamming
def profileRankLaw : Measure ℝ := volume.restrict (Set.Ioc 0 1)
def profileCDF (p : SphericalProfile) (t : ℝ) : ℝ :=
  profileRankLaw.real {s | p.val s ≤ t}
structure RowPartition (Q : ℝ) where
  blocks : List (ℝ × ℝ)
  valid : ∀ r ∈ blocks, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2
  ordered : blocks.Pairwise (fun r s => r.1 ≤ s.1)
  total : gaussianStepTime blocks=Q

def RowPartition.profile {Q : ℝ} (P : RowPartition Q) : SphericalProfile where
  val := gaussianRankProfile P.blocks
  mono := by
    intro s hs t ht hst
    unfold gaussianRankProfile
    apply List.sum_le_sum
    intro r hr
    split_ifs with h h'
    · rfl
    · exact False.elim (h' (h.trans hst))
    · exact (P.valid r hr).2.2
    · rfl
  nonneg := by
    intro s hs
    apply List.sum_nonneg
    intro x hx
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
    split_ifs
    · exact (P.valid r hr).2.2
    · exact le_rfl

 

def rowProfileSequence (u : ℝ → ℝ) (Q : ℝ) (p : SphericalProfile) (n : ℕ) : ℝ :=
  gaussianRowComposition (gaussianGrid (profileCDF p) 0 (Q/((n:ℝ)+1)) (n+1)) u 0

def rowProfileValue (u : ℝ → ℝ) (Q : ℝ) (p : SphericalProfile) : ℝ :=
  limUnder atTop (rowProfileSequence u Q p)

def SphericalProfile.rowChord (p q : SphericalProfile) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : SphericalProfile where
  val := fun s => (1-θ)*p.val s+θ*q.val s
  mono := fun _ hs _ ht hst => add_le_add
    (mul_le_mul_of_nonneg_left (p.mono hs ht hst) (sub_nonneg.mpr hθ1))
    (mul_le_mul_of_nonneg_left (q.mono hs ht hst) hθ)
  nonneg := fun s hs => add_nonneg (mul_nonneg (sub_nonneg.mpr hθ1) (p.nonneg s hs))
    (mul_nonneg hθ (q.nonneg s hs))

 

def RowProfileAnalyticStatement : Prop :=
  ∀ (u : ℝ → ℝ) (A B C κ Q L : ℝ), 0 < Q →
    RowAnalyticTerminal u A B C κ Q → 0 ≤ L → (∀ x, |deriv u x| ≤ L) →
    (∀ p : SphericalProfile, (∀ s ∈ Set.Icc 0 1, p.val s ≤ Q) →
      Tendsto (rowProfileSequence u Q p) atTop (𝓝 (rowProfileValue u Q p))) ∧
    (∀ P : RowPartition Q, rowProfileValue u Q P.profile = gaussianRowComposition P.blocks u 0) ∧
    (∀ p q : SphericalProfile, (∀ s ∈ Set.Icc 0 1, p.val s ≤ Q) →
      (∀ s ∈ Set.Icc 0 1, q.val s ≤ Q) →
      |rowProfileValue u Q p-rowProfileValue u Q q| ≤ (L^2/2)*sphericalProfileDistance p.val q.val) ∧
    (∀ p : SphericalProfile, RowSmoothProfile Q p.val →
      ∀ f : ℝ → ℝ → ℝ, RowClassicalRankSolution u p.val f → rowProfileValue u Q p=f 0 0) ∧
    (ConcaveOn ℝ univ u → ∀ p q : SphericalProfile,
      (∀ s ∈ Set.Icc 0 1, p.val s ≤ Q) → (∀ s ∈ Set.Icc 0 1, q.val s ≤ Q) →
      ∀ θ : ℝ, ∀ hθ : 0 ≤ θ, ∀ hθ1 : θ ≤ 1,
      (1-θ)*rowProfileValue u Q p+θ*rowProfileValue u Q q ≤
        rowProfileValue u Q (p.rowChord q θ hθ hθ1))

end MicroscopicJamming

 
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MicroscopicJamming
instance : IsProbabilityMeasure profileRankLaw := by
  constructor
  simp [profileRankLaw]

lemma profileCDF_monotone (p : SphericalProfile) : Monotone (profileCDF p) := by
  intro x y hxy
  exact measureReal_mono (fun s hs => hs.trans hxy)

lemma profileCDF_bounds (p : SphericalProfile) (t : ℝ) : 0 ≤ profileCDF p t ∧ profileCDF p t ≤ 1 := by
  constructor
  · exact measureReal_nonneg
  · exact (measureReal_mono (subset_univ _)).trans_eq (probReal_univ)

lemma profileCDF_closed (p : SphericalProfile) (t : ℝ) :
    profileCDF p t=profileRankLaw.real {s | rowClosedProfile p s ≤ t} := by
  unfold profileCDF
  simp only [measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [show rowClosedProfile p s=p.val s from rowClosedProfile_eq p ⟨hs.1.le,hs.2⟩]

lemma profileCDF_integral (p : SphericalProfile) (t : ℝ) :
    profileCDF p t=∫ s, (if rowClosedProfile p s ≤ t then (1:ℝ) else 0) ∂profileRankLaw := by
  rw [profileCDF_closed]
  have hm : MeasurableSet {s | rowClosedProfile p s ≤ t} := measurableSet_le (measurable_rowClosedProfile p) measurable_const
  have hh := integral_indicator_one (μ:=profileRankLaw) hm
  simpa only [indicator_apply,mem_ofPred_eq,Pi.one_apply] using hh.symm

lemma profileCDF_ae_continuous (p : SphericalProfile) :
    ∀ᵐ t : ℝ ∂volume, ContinuousAt (profileCDF p) t := by
  rw [ae_iff]
  exact (profileCDF_monotone p).countable_not_continuousAt.measure_zero volume

lemma rowAnalytic_bounded {u : ℝ → ℝ} {A B C κ Q L : ℝ}
    (hu : RowAnalyticTerminal u A B C κ Q) (hL : 0 ≤ L) (hb : ∀ x, |deriv u x| ≤ L) :
    RowBoundedTerminal u L (C+κ) := by
  apply rowTerminal_of_C2 (hu.1.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top)) hL (add_nonneg hu.2.2.1 hu.2.2.2.1)
  intro x
  refine ⟨hb x,abs_le.mpr ⟨?_,?_⟩⟩
  · linarith [(hu.2.2.2.2.2.2 x).2.2.1,hu.2.2.2.1]
  · linarith [(hu.2.2.2.2.2.2 x).2.2.2,hu.2.2.1]
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
 
lemma row_integrated_difference_le {Q C L : ℝ} (hQ : 0 < Q) (hC : 0 ≤ C) (hL : 0 ≤ L)
    {F G : ℝ → ℝ → ℝ} {m n h : ℝ → ℝ}
    (hcF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (Set.Icc 0 Q ×ˢ univ))
    (hcG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (Set.Icc 0 Q ×ˢ univ))
    (hch : ContinuousOn h (Set.Icc 0 Q))
    (hhn : ∀ t ∈ Set.Icc 0 Q, 0 ≤ h t) (hhQ : h Q=0)
    (hht : ∀ t ∈ Set.Ico 0 Q, HasDerivWithinAt h (-(L^2/2*|m t-n t|)) (Set.Ici t) t)
    (hxF : ∀ t ∈ Set.Icc 0 Q, Differentiable ℝ (F t) ∧ Differentiable ℝ (deriv (F t)))
    (hxG : ∀ t ∈ Set.Icc 0 Q, Differentiable ℝ (G t) ∧ Differentiable ℝ (deriv (G t)))
    (htF : ∀ t ∈ Set.Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => F s x)
      (-(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)) (Set.Ici t) t)
    (htG : ∀ t ∈ Set.Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => G s x)
      (-(1/2:ℝ)*(deriv (deriv (G t)) x+n t*(deriv (G t) x)^2)) (Set.Ici t) t)
    (hm : ∀ t ∈ Set.Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hboundF : ∀ t ∈ Set.Icc 0 Q, ∀ x, |F t x| ≤ C*(1+x^2))
    (hboundG : ∀ t ∈ Set.Icc 0 Q, ∀ x, |G t x| ≤ C*(1+x^2))
    (hgradF : ∀ t ∈ Set.Icc 0 Q, ∀ x, |deriv (F t) x| ≤ L)
    (hgradG : ∀ t ∈ Set.Icc 0 Q, ∀ x, |deriv (G t) x| ≤ L)
    (hterm : ∀ x, F Q x=G Q x) :
    ∀ t ∈ Set.Icc 0 Q, ∀ x, F t x-G t x ≤ h t := by
  let U := fun t x => F t x-G t x-h t
  let b := fun t x => m t*(deriv (F t) x+deriv (G t) x)/2
  let d := fun t x => -(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)-
    (-(1/2:ℝ)*(deriv (deriv (G t)) x+n t*(deriv (G t) x)^2))+L^2/2*|m t-n t|
  have hdx (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      HasDerivAt (U t) (deriv (F t) x-deriv (G t) x) x := by
    exact (((hxF t ht).1 x).hasDerivAt.sub ((hxG t ht).1 x).hasDerivAt).sub_const (h t)
  have hdx2 (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (U t)) (deriv (deriv (F t)) x-deriv (deriv (G t)) x) x := by
    have he : deriv (U t)=fun y => deriv (F t) y-deriv (G t) y := funext fun y => (hdx t ht y).deriv
    rw [he]
    exact ((hxF t ht).2 x).hasDerivAt.sub ((hxG t ht).2 x).hasDerivAt
  have hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Set.Icc 0 Q ×ˢ univ) :=
    (hcF.sub hcG).sub (hch.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have htime (t : ℝ) (ht : t ∈ Set.Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => U s x) (d t x) (Set.Ici t) t := by
    convert ((htF t ht x).sub (htG t ht x)).sub (hht t ht) using 1; first | rfl | (dsimp [d,U]; ring)
  have hb (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) : |b t x| ≤ L*(1+|x|) := by
    have hh : |deriv (F t) x+deriv (G t) x| ≤ 2*L :=
      (abs_add_le _ _).trans (by linarith [hgradF t ht x,hgradG t ht x])
    have h1 := mul_le_mul_of_nonneg_left hh (hm t ht).1
    have h2 := mul_le_mul_of_nonneg_right (hm t ht).2 (show 0 ≤ 2*L by positivity)
    dsimp [b]
    rw [abs_div,abs_mul,abs_of_nonneg (hm t ht).1]
    norm_num only [show |(2:ℝ)|=2 by norm_num]
    nlinarith [mul_nonneg hL (abs_nonneg x)]
  have hg (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) : U t x ≤ (2*C)*(1+x^2) := by
    dsimp [U]
    nlinarith [hboundF t ht x,hboundG t ht x,le_abs_self (F t x),neg_abs_le (G t x),hhn t ht]
  have hp (t : ℝ) (ht : t ∈ Set.Ico 0 Q) (x : ℝ) :
      0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x := by
    have htcc : t ∈ Set.Icc 0 Q := ⟨ht.1,ht.2.le⟩
    rw [(hdx2 t htcc x).deriv,(hdx t htcc x).deriv]
    have he : d t x+(1/2:ℝ)*(deriv (deriv (F t)) x-deriv (deriv (G t)) x)+
        b t x*(deriv (F t) x-deriv (G t) x)=
        (L^2*|m t-n t|-(m t-n t)*(deriv (G t) x)^2)/2 := by dsimp [d,b]; ring
    rw [he]
    have hs := sq_le_sq₀ (abs_nonneg (deriv (G t) x)) hL
    have hs' : (deriv (G t) x)^2 ≤ L^2 := by simpa only [sq_abs] using hs.mpr (hgradG t htcc x)
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (m t-n t)) (sq_nonneg (deriv (G t) x))
    have h2 := mul_le_mul_of_nonneg_left hs' (abs_nonneg (m t-n t))
    nlinarith
  have hm' := backward_comparison Q L (2*C) hQ hL (by positivity) U b d hc
    (fun t ht => ⟨fun x => (hdx t ht x).differentiableAt,fun x => (hdx2 t ht x).differentiableAt⟩)
    htime hb hg hp (fun x => by dsimp [U]; rw [hterm x,hhQ]; simp)
  intro t ht x
  have hh := hm' t ht x
  dsimp [U] at hh
  linarith
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma gaussianStepRightCoefficient_measurable (rs : List (ℝ × ℝ)) :
    Measurable (gaussianStepRightCoefficient rs) := by
  induction rs with
  | nil => exact measurable_const
  | cons r rs ih =>
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (ih.comp (measurable_id.sub measurable_const))

lemma gaussianStepRightCoefficient_local (rs : List (ℝ × ℝ)) (t : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Ico t (t+ε),
      gaussianStepRightCoefficient rs s=gaussianStepRightCoefficient rs t := by
  induction rs generalizing t with
  | nil => exact ⟨1,by norm_num,fun _ _ => rfl⟩
  | cons r rs ih =>
    by_cases h : t < r.2
    · refine ⟨r.2-t,by linarith,?_⟩
      intro s hs
      have hs' : s < r.2 := by linarith [hs.2]
      simp [gaussianStepRightCoefficient,h,hs']
    · obtain ⟨ε,hε,he⟩ := ih (t-r.2)
      refine ⟨ε,hε,?_⟩
      intro s hs
      have hs' : ¬s < r.2 := by linarith [hs.1]
      simp only [gaussianStepRightCoefficient,ite_eq_right h,ite_eq_right hs']
      exact he _ ⟨by linarith [hs.1],by linarith [hs.2]⟩

lemma gaussianStepRightCoefficient_rightContinuous (rs : List (ℝ × ℝ)) (t : ℝ) :
    ContinuousWithinAt (gaussianStepRightCoefficient rs) (Set.Ici t) t := by
  obtain ⟨ε,hε,he⟩ := gaussianStepRightCoefficient_local rs t
  have hev : ∀ᶠ s in 𝓝[Set.Ici t] t, gaussianStepRightCoefficient rs s=gaussianStepRightCoefficient rs t := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show t<t+ε by linarith)).filter_mono nhdsWithin_le_nhds] with s hs hs'
    exact he s ⟨hs,hs'⟩
  exact tendsto_const_nhds.congr' (hev.mono fun _ hh => hh.symm)

lemma rowStepDifference_integrable (rs ss : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hss : ∀ r ∈ ss, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) (a b : ℝ) :
    IntervalIntegrable (fun t => |gaussianStepRightCoefficient rs t-gaussianStepRightCoefficient ss t|) volume a b := by
  apply IntervalIntegrable.mono_fun (f:=fun _ : ℝ => (1:ℝ)) intervalIntegrable_const
    ((gaussianStepRightCoefficient_measurable rs).sub (gaussianStepRightCoefficient_measurable ss)).abs.aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_abs,Real.norm_eq_abs,abs_one,Pi.sub_apply]
  have hr := gaussianStepRightCoefficient_bounds hrs t
  have hs := gaussianStepRightCoefficient_bounds hss t
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma rowStepDifference_primitive {Q L : ℝ} (_hQ : 0 ≤ Q) (rs ss : List (ℝ × ℝ))
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hss : ∀ r ∈ ss, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2) :
    let h := fun t => L^2/2*(∫ v in t..Q, |gaussianStepRightCoefficient rs v-gaussianStepRightCoefficient ss v|)
    ContinuousOn h (Set.Icc 0 Q) ∧ (∀ t ∈ Set.Icc 0 Q, 0 ≤ h t) ∧ h Q=0 ∧
    ∀ t ∈ Set.Ico 0 Q, HasDerivWithinAt h (-(L^2/2*|gaussianStepRightCoefficient rs t-gaussianStepRightCoefficient ss t|)) (Set.Ici t) t := by
  dsimp only
  let f := fun t => |gaussianStepRightCoefficient rs t-gaussianStepRightCoefficient ss t|
  have hi := rowStepDifference_integrable rs ss hrs hss
  have hm : StronglyMeasurable f := ((gaussianStepRightCoefficient_measurable rs).sub
    (gaussianStepRightCoefficient_measurable ss)).abs.stronglyMeasurable
  have hc : Continuous (fun t => ∫ v in t..Q, f v) := by
    simp only [intervalIntegral.integral_symm Q]
    exact (intervalIntegral.continuous_primitive hi Q).neg
  refine ⟨(continuous_const.mul hc).continuousOn,?_,by simp,?_⟩
  · intro t ht
    exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg ht.2 (fun _ _ => abs_nonneg _))
  · intro t ht
    have hd := intervalIntegral.integral_hasDerivWithinAt_left (s:=Set.Ici t) (t:=Set.Ioi t)
      (hi t Q) hm.stronglyMeasurableAtFilter
      ((((gaussianStepRightCoefficient_rightContinuous rs t).mono Ioi_subset_Ici_self).sub
        ((gaussianStepRightCoefficient_rightContinuous ss t).mono Ioi_subset_Ici_self)).abs)
    convert hd.const_mul (L^2/2) using 1; first | rfl | ring
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma row_step_L1_stability {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    {rs ss : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hss : ∀ r ∈ ss, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hTr : gaussianStepTime rs=Q) (hTs : gaussianStepTime ss=Q) :
    ∀ t ∈ Set.Icc 0 Q, ∀ x,
      |gaussianStepPath rs u t x-gaussianStepPath ss u t x| ≤
        L^2/2*(∫ v in t..Q, |gaussianStepRightCoefficient rs v-gaussianStepRightCoefficient ss v|) := by
  obtain ⟨D,J,hD,hJ,hpath⟩ := gaussian_step_path A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨_,htermR,htimeR,hspaceR⟩ := hpath u hu rs hrs hTr.le
  obtain ⟨_,htermS,htimeS,hspaceS⟩ := hpath u hu ss hss hTs.le
  have hxr (t : ℝ) (ht : t ∈ Set.Icc 0 Q) :
      Differentiable ℝ (gaussianStepPath rs u t) ∧ Differentiable ℝ (deriv (gaussianStepPath rs u t)) := by
    have hh := hspaceR t ht.1 (hTr ▸ ht.2)
    exact ⟨hh.1,hh.2.1⟩
  have hxs (t : ℝ) (ht : t ∈ Set.Icc 0 Q) :
      Differentiable ℝ (gaussianStepPath ss u t) ∧ Differentiable ℝ (deriv (gaussianStepPath ss u t)) := by
    have hh := hspaceS t ht.1 (hTs ▸ ht.2)
    exact ⟨hh.1,hh.2.1⟩
  have hgr (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath rs u t) x| ≤ J*(1+|x|) :=
    ((hspaceR t ht.1 (hTr ▸ ht.2)).2.2 x).1
  have hgs (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath ss u t) x| ≤ J*(1+|x|) :=
    ((hspaceS t ht.1 (hTs ▸ ht.2)).2.2 x).1
  have hcr := gaussianStepPath_jointly_continuous hD hJ hTr htimeR
    (fun t ht htR => ⟨(hspaceR t ht htR).1,fun x => ((hspaceR t ht htR).2.2 x).1⟩)
  have hcs := gaussianStepPath_jointly_continuous hD hJ hTs htimeS
    (fun t ht htS => ⟨(hspaceS t ht htS).1,fun x => ((hspaceS t ht htS).2.2 x).1⟩)
  have hpr (t : ℝ) (ht : t ∈ Set.Ico 0 Q) (x : ℝ) :=
    gaussianStepPath_right_pde hQ hu hrs hTr.le (hTr ▸ ht) x
  have hps (t : ℝ) (ht : t ∈ Set.Ico 0 Q) (x : ℝ) :=
    gaussianStepPath_right_pde hQ hu hss hTs.le (hTs ▸ ht) x
  have hb : 0 ≤ |B|+A*(1+Q) := add_nonneg (abs_nonneg _) (mul_nonneg hu.2.1 (by linarith))
  have hvr (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :=
    gaussianStepPath_global_value_bound hQ hu hrs hTr ht x
  have hvs (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :=
    gaussianStepPath_global_value_bound hQ hu hss hTs ht x
  have hmr (t : ℝ) (_ : t ∈ Set.Icc 0 Q) := gaussianStepRightCoefficient_bounds hrs t
  have hms (t : ℝ) (_ : t ∈ Set.Icc 0 Q) := gaussianStepRightCoefficient_bounds hss t
  have hgr' (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath rs u t) x| ≤ L := by
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hub (gaussianStepRemainder rs t)
      (gaussianStepRemainder_valid hrs ht.1).1
    exact hK.slope x
  have hgs' (t : ℝ) (ht : t ∈ Set.Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath ss u t) x| ≤ L := by
    obtain ⟨K,hK⟩ := rowBoundedComposition_terminal hub (gaussianStepRemainder ss t)
      (gaussianStepRemainder_valid hss ht.1).1
    exact hK.slope x
  have hterm (x : ℝ) : gaussianStepPath rs u Q x=gaussianStepPath ss u Q x := by
    simpa only [hTr,hTs] using (htermR x).trans (htermS x).symm
  obtain ⟨hc,hn,hend,hder⟩ := rowStepDifference_primitive (L:=L) hQ.le rs ss hrs hss
  have hr := row_integrated_difference_le hQ hb hub.L_nonneg hcr hcs hc hn hend hder
    hxr hxs hpr hps hmr hvr hvs hgr' hgs' hterm
  obtain ⟨hc',hn',hend',hder'⟩ := rowStepDifference_primitive (L:=L) hQ.le ss rs hss hrs
  have hs := row_integrated_difference_le hQ hb hub.L_nonneg hcs hcr hc' hn' hend' hder'
    hxs hxr hps hpr hms hvs hvr hgs' hgr' (fun x => (hterm x).symm)
  intro t ht x
  rw [abs_le]
  refine ⟨?_,hr t ht x⟩
  have hh := hs t ht x
  simp only [abs_sub_comm (gaussianStepRightCoefficient ss _) (gaussianStepRightCoefficient rs _)] at hh
  linarith

lemma row_composition_L1_stability {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    {rs ss : List (ℝ × ℝ)}
    (hrs : ∀ r ∈ rs, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hss : ∀ r ∈ ss, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
    (hTr : gaussianStepTime rs=Q) (hTs : gaussianStepTime ss=Q) (x : ℝ) :
      |gaussianRowComposition rs u x-gaussianRowComposition ss u x| ≤
        L^2/2*(∫ v in (0:ℝ)..Q, |gaussianStepRightCoefficient rs v-gaussianStepRightCoefficient ss v|) := by
  simpa only [gaussianStepPath_zero (fun r hr => (hrs r hr).2.2),gaussianStepPath_zero (fun r hr => (hss r hr).2.2)] using
    row_step_L1_stability hQ hu hub hrs hss hTr hTs 0 ⟨le_rfl,hQ.le⟩ x
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma gaussianStepCoefficient_ae_right (rs : List (ℝ × ℝ)) :
    gaussianStepCoefficient rs =ᵐ[volume] gaussianStepRightCoefficient rs := by
  induction rs with
  | nil => exact ae_of_all _ (fun _ => rfl)
  | cons r rs ih =>
    have hshift : ∀ᵐ t : ℝ ∂volume, gaussianStepCoefficient rs (t-r.2)=gaussianStepRightCoefficient rs (t-r.2) := by
      simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-r.2)).quasiMeasurePreserving.ae ih
    filter_upwards [hshift, (show ∀ᵐ t : ℝ ∂volume, t≠r.2 from by rw [ae_iff]; simp)] with t ht hne
    by_cases h : t < r.2
    · simp only [gaussianStepCoefficient,gaussianStepRightCoefficient,ite_eq_left h,ite_eq_left h.le]
    · have h' : ¬t ≤ r.2 := fun hh => h (lt_of_le_of_ne hh hne)
      simp only [gaussianStepCoefficient,gaussianStepRightCoefficient,ite_eq_right h,ite_eq_right h',ht]

def rowCDFGrid (Q : ℝ) (m : ℝ → ℝ) (n : ℕ) : List (ℝ × ℝ) :=
  gaussianGrid m 0 (Q/((n:ℝ)+1)) (n+1)
lemma rowCDFGrid_valid {Q : ℝ} (hQ : 0 ≤ Q) {m : ℝ → ℝ}
    (hm : ∀ t, 0 ≤ m t ∧ m t ≤ 1) (n : ℕ) :
    ∀ r ∈ rowCDFGrid Q m n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2 :=
  gaussianGrid_valid (n+1) (by positivity) (fun t _ => hm t)
lemma rowCDFGrid_time (Q : ℝ) (m : ℝ → ℝ) (n : ℕ) : gaussianStepTime (rowCDFGrid Q m n)=Q := by
  rw [rowCDFGrid,gaussianGrid_time,Nat.cast_add,Nat.cast_one]
  exact mul_div_cancel₀ Q (by positivity)
lemma rowCDFGrid_tendsto {Q : ℝ} (hQ : 0 < Q) {m : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Icc 0 Q) (hm : ContinuousAt m t) :
    Tendsto (fun n => gaussianStepCoefficient (rowCDFGrid Q m n) t) atTop (𝓝 (m t)) := by
  have hmesh : Tendsto (fun n : ℕ => Q/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using (tendsto_const_nhds (x:=Q)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hex (n : ℕ) : ∃ s ∈ Set.Icc (0:ℝ) Q, |s-t| ≤ Q/((n:ℝ)+1) ∧
      gaussianStepCoefficient (rowCDFGrid Q m n) t=m s := by
    have hlen : ((n+1:ℕ):ℝ)*(Q/((n:ℝ)+1))=Q := by
      rw [Nat.cast_add,Nat.cast_one]; exact mul_div_cancel₀ Q (by positivity)
    simpa only [rowCDFGrid,hlen,zero_add] using gaussianGrid_coefficient_sample (m:=m) (a:=0) (n+1)
      (by omega) (by positivity : 0 ≤ Q/((n:ℝ)+1)) (show t∈Set.Icc 0 (((n+1:ℕ):ℝ)*(Q/((n:ℝ)+1))) by simpa only [hlen] using ht)
  choose s hs hd he using hex
  have hst : Tendsto s atTop (𝓝 t) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [Real.dist_eq] using hd n) hmesh
  exact (hm.tendsto.comp hst).congr (fun n => (he n).symm)
lemma rowCDFGrid_L1 {Q : ℝ} (hQ : 0 < Q) {m : ℝ → ℝ}
    (hmeas : Measurable m) (hb : ∀ t, 0 ≤ m t ∧ m t ≤ 1)
    (hc : ∀ᵐ t : ℝ ∂volume, ContinuousAt m t) :
    Tendsto (fun n => ∫ t in (0:ℝ)..Q, |gaussianStepRightCoefficient (rowCDFGrid Q m n) t-m t|) atTop (𝓝 0) := by
  have he : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      gaussianStepCoefficient (rowCDFGrid Q m n) t=gaussianStepRightCoefficient (rowCDFGrid Q m n) t := by
    rw [ae_all_iff]
    intro n
    exact gaussianStepCoefficient_ae_right (rowCDFGrid Q m n)
  have hconv : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 Q),
      Tendsto (fun n => |gaussianStepRightCoefficient (rowCDFGrid Q m n) t-m t|) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hc,ae_restrict_of_ae he] with t ht hct het
    have hh := (rowCDFGrid_tendsto hQ ⟨ht.1.le,ht.2⟩ hct).sub (tendsto_const_nhds (x:=m t))
    simpa only [het,sub_self,abs_zero] using hh.abs
  have hlim := tendsto_integral_of_dominated_convergence (μ:=volume.restrict (Set.Ioc (0:ℝ) Q))
    (f:=fun _ => (0:ℝ)) (bound:=fun _ => (1:ℝ))
    (fun n => ((gaussianStepRightCoefficient_measurable _).sub hmeas).abs.aestronglyMeasurable)
    (integrable_const 1) (fun n => by
      filter_upwards [] with t
      rw [Real.norm_eq_abs,abs_abs,Pi.sub_apply]
      have hg := gaussianStepRightCoefficient_bounds (rowCDFGrid_valid hQ.le hb n) t
      exact abs_le.mpr ⟨by linarith [(hb t).1,(hb t).2,hg.1,hg.2],by linarith [(hb t).1,(hb t).2,hg.1,hg.2]⟩) hconv
  simpa only [intervalIntegral.integral_of_le hQ.le,integral_zero,Pi.sub_apply] using hlim
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma row_indicator_distance_integral {a b Q : ℝ} (ha : a∈Set.Icc 0 Q) (hb : b∈Set.Icc 0 Q) :
    (∫ t in (0:ℝ)..Q, |(if a ≤ t then (1:ℝ) else 0)-(if b ≤ t then 1 else 0)|)=|a-b| := by
  have hbase {a b : ℝ} (ha : a∈Set.Icc 0 Q) (hb : b∈Set.Icc 0 Q) (hab : a≤b) :
      (∫ t in (0:ℝ)..Q, |(if a ≤ t then (1:ℝ) else 0)-(if b ≤ t then 1 else 0)|)=b-a := by
    have he : (fun t : ℝ => |(if a ≤ t then (1:ℝ) else 0)-(if b ≤ t then 1 else 0)|)=
        (Set.Ico a b).indicator (fun _ => (1:ℝ)) := by
      funext t
      simp only [indicator_apply,Set.mem_Ico]
      by_cases h1 : a≤t
      · by_cases h2 : b≤t
        · simp [h1,h2,not_lt.mpr h2]
        · simp [h1,h2,lt_of_not_ge h2]
      · have h2 : ¬b≤t := fun h => h1 (hab.trans h)
        simp [h1,h2]
    rw [he,intervalIntegral.integral_of_le (ha.1.trans ha.2),integral_indicator measurableSet_Ico]
    rw [Measure.restrict_restrict measurableSet_Ico]
    have hinter : (Set.Ico a b ∩ Set.Ioc 0 Q : Set ℝ) =ᵐ[volume] (Set.Ico a b : Set ℝ) := by
      filter_upwards [(show ∀ᵐ t : ℝ ∂volume,t≠0 from by rw [ae_iff]; simp)] with t ht
      change ((a ≤ t ∧ t < b) ∧ (0 < t ∧ t ≤ Q)) = (a ≤ t ∧ t < b)
      apply propext
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h,lt_of_le_of_ne (ha.1.trans h.1) (Ne.symm ht),h.2.le.trans hb.2⟩
    rw [Measure.restrict_congr_set hinter]
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ico,smul_eq_mul,mul_one]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rcases le_total a b with hab | hba
  · rw [hbase ha hb hab,abs_of_nonpos (sub_nonpos.mpr hab)]; ring
  · simp_rw [abs_sub_comm (if a ≤ _ then (1:ℝ) else 0)]
    rw [hbase hb ha hba,abs_of_nonneg (sub_nonneg.mpr hba)]

lemma profileCDF_distance {Q : ℝ} (hQ : 0 ≤ Q) (p q : SphericalProfile)
    (hp : ∀ s∈Set.Icc 0 1,p.val s≤Q) (hq : ∀ s∈Set.Icc 0 1,q.val s≤Q) :
    (∫ t in (0:ℝ)..Q, |profileCDF p t-profileCDF q t|) ≤ sphericalProfileDistance p.val q.val := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 Q)
  let k : ℝ × ℝ → ℝ := fun z => |(if rowClosedProfile p z.2≤z.1 then (1:ℝ) else 0)-
    (if rowClosedProfile q z.2≤z.1 then 1 else 0)|
  have hk : Measurable k := by
    exact (Measurable.ite (measurableSet_le ((measurable_rowClosedProfile p).comp measurable_snd) measurable_fst)
      measurable_const measurable_const |>.sub (Measurable.ite
        (measurableSet_le ((measurable_rowClosedProfile q).comp measurable_snd) measurable_fst) measurable_const measurable_const)).abs
  have hkb (z : ℝ × ℝ) : ‖k z‖≤1 := by dsimp [k]; simp only [abs_abs]; split_ifs <;> norm_num
  have hki : Integrable k (μ.prod profileRankLaw) := Integrable.of_bound hk.aestronglyMeasurable 1 (ae_of_all _ hkb)
  have hpint (t : ℝ) : Integrable (fun s => if rowClosedProfile p s≤t then (1:ℝ) else 0) profileRankLaw :=
    Integrable.of_bound (Measurable.ite (measurableSet_le (measurable_rowClosedProfile p) measurable_const)
      measurable_const measurable_const).aestronglyMeasurable 1 (ae_of_all _ (fun s => by split_ifs <;> norm_num))
  have hqint (t : ℝ) : Integrable (fun s => if rowClosedProfile q s≤t then (1:ℝ) else 0) profileRankLaw :=
    Integrable.of_bound (Measurable.ite (measurableSet_le (measurable_rowClosedProfile q) measurable_const)
      measurable_const measurable_const).aestronglyMeasurable 1 (ae_of_all _ (fun s => by split_ifs <;> norm_num))
  have hi : Integrable (fun t => |profileCDF p t-profileCDF q t|) μ :=
    Integrable.of_bound ((profileCDF_monotone p).measurable.sub (profileCDF_monotone q).measurable).abs.aestronglyMeasurable 1 (ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs,abs_abs]; exact abs_le.mpr ⟨by linarith [(profileCDF_bounds p t).1,(profileCDF_bounds q t).2],by linarith [(profileCDF_bounds p t).2,(profileCDF_bounds q t).1]⟩))
  rw [intervalIntegral.integral_of_le hQ]
  calc
    _ ≤ ∫ t, ∫ s, k (t,s) ∂profileRankLaw ∂μ := integral_mono_ae hi hki.integral_prod_left (ae_of_all _ (fun t => by
      change |profileCDF p t-profileCDF q t| ≤ ∫ s,k (t,s) ∂profileRankLaw
      rw [profileCDF_integral p,profileCDF_integral q,← integral_sub (hpint t) (hqint t)]
      exact abs_integral_le_integral_abs))
    _ = ∫ s, ∫ t, k (t,s) ∂μ ∂profileRankLaw := integral_integral_swap hki
    _ = sphericalProfileDistance p.val q.val := by
      rw [sphericalProfileDistance,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hss : s∈Set.Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2⟩
      dsimp [k,μ]
      simp only [rowClosedProfile_eq p hss,rowClosedProfile_eq q hss]
      exact (intervalIntegral.integral_of_le hQ).symm.trans
        (row_indicator_distance_integral ⟨p.nonneg s hss,hp s hss⟩ ⟨q.nonneg s hss,hq s hss⟩)
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
def rowCoeffDistance (Q : ℝ) (m n : ℝ → ℝ) : ℝ := ∫ t in (0:ℝ)..Q, |m t-n t|
lemma rowCoeff_integrable {m n : ℝ → ℝ} {a b : ℝ}
    (hm : Measurable m) (hn : Measurable n)
    (hmb : ∀ t,0 ≤ m t ∧ m t ≤ 1) (hnb : ∀ t,0 ≤ n t ∧ n t ≤ 1) :
    IntervalIntegrable (fun t => |m t-n t|) volume a b := by
  apply IntervalIntegrable.mono_fun (f:=fun _ : ℝ => (1:ℝ)) intervalIntegrable_const (hm.sub hn).abs.aestronglyMeasurable
  filter_upwards [] with t
  simp only [Real.norm_eq_abs,abs_abs,abs_one,Pi.sub_apply]
  exact abs_le.mpr ⟨by linarith [(hmb t).1,(hnb t).2],by linarith [(hmb t).2,(hnb t).1]⟩
lemma rowCoeffDistance_triangle {Q : ℝ} (hQ : 0 ≤ Q) {m n p : ℝ → ℝ}
    (hm : Measurable m) (hn : Measurable n) (hp : Measurable p)
    (hmb : ∀ t,0 ≤ m t ∧ m t ≤ 1) (hnb : ∀ t,0 ≤ n t ∧ n t ≤ 1) (hpb : ∀ t,0 ≤ p t ∧ p t ≤ 1) :
    rowCoeffDistance Q m p ≤ rowCoeffDistance Q m n+rowCoeffDistance Q n p := by
  unfold rowCoeffDistance
  rw [←intervalIntegral.integral_add (rowCoeff_integrable hm hn hmb hnb) (rowCoeff_integrable hn hp hnb hpb)]
  apply intervalIntegral.integral_mono_on hQ (rowCoeff_integrable hm hp hmb hpb)
    ((rowCoeff_integrable hm hn hmb hnb).add (rowCoeff_integrable hn hp hnb hpb))
  exact fun t _ => abs_sub_le (m t) (n t) (p t)
lemma rowCoeffDistance_comm (Q : ℝ) (m n : ℝ → ℝ) : rowCoeffDistance Q m n=rowCoeffDistance Q n m := by
  unfold rowCoeffDistance; simp_rw [abs_sub_comm]
lemma rowCoeffDistance_nonneg {Q : ℝ} (hQ : 0 ≤ Q) (m n : ℝ → ℝ) : 0 ≤ rowCoeffDistance Q m n :=
  intervalIntegral.integral_nonneg hQ (fun _ _ => abs_nonneg _)
lemma row_cauchy_error {a e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n m, |a n-a m| ≤ e n+e m) : CauchySeq a := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun n hn m hm => ?_⟩
  rw [Real.dist_eq]
  exact (hb n m).trans_lt (by linarith [hN n hn,hN m hm])
lemma rowProfileSequence_converges {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    (p : SphericalProfile) : Tendsto (rowProfileSequence u Q p) atTop (𝓝 (rowProfileValue u Q p)) := by
  let f (n : ℕ) := gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF p) n)
  let e (n : ℕ) := rowCoeffDistance Q (f n) (profileCDF p)
  have hf (n : ℕ) := gaussianStepRightCoefficient_measurable (rowCDFGrid Q (profileCDF p) n)
  have hfb (n : ℕ) := gaussianStepRightCoefficient_bounds (rowCDFGrid_valid hQ.le (profileCDF_bounds p) n)
  have he : Tendsto e atTop (𝓝 0) := rowCDFGrid_L1 hQ (profileCDF_monotone p).measurable (profileCDF_bounds p) (profileCDF_ae_continuous p)
  have hC : CauchySeq (rowProfileSequence u Q p) := row_cauchy_error
    (by simpa only [mul_zero] using he.const_mul (L^2/2)) (fun n m => by
      have hh := row_composition_L1_stability hQ hu hub
        (rowCDFGrid_valid hQ.le (profileCDF_bounds p) n) (rowCDFGrid_valid hQ.le (profileCDF_bounds p) m)
        (rowCDFGrid_time Q (profileCDF p) n) (rowCDFGrid_time Q (profileCDF p) m) 0
      change |rowProfileSequence u Q p n-rowProfileSequence u Q p m| ≤ L^2/2*rowCoeffDistance Q (f n) (f m) at hh
      calc
        _  ≤  _ := hh
        _  ≤  L^2/2*(e n+e m) := mul_le_mul_of_nonneg_left (by
          have ht : rowCoeffDistance Q (f n) (f m) ≤ rowCoeffDistance Q (f n) (profileCDF p)+rowCoeffDistance Q (profileCDF p) (f m) :=
            rowCoeffDistance_triangle hQ.le (hf n) (profileCDF_monotone p).measurable (hf m) (hfb n) (profileCDF_bounds p) (hfb m)
          rw [rowCoeffDistance_comm Q (profileCDF p) (f m)] at ht
          exact ht) (by positivity)
        _ = _ := mul_add _ _ _)
  exact hC.tendsto_limUnder

lemma rowProfileValue_lipschitz {u : ℝ → ℝ} {A B C κ Q L H : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hub : RowBoundedTerminal u L H)
    (p q : SphericalProfile) (hp : ∀ s∈Set.Icc 0 1,p.val s ≤ Q) (hq : ∀ s∈Set.Icc 0 1,q.val s ≤ Q) :
    |rowProfileValue u Q p-rowProfileValue u Q q| ≤ L^2/2*sphericalProfileDistance p.val q.val := by
  let f (n : ℕ) := gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF p) n)
  let g (n : ℕ) := gaussianStepRightCoefficient (rowCDFGrid Q (profileCDF q) n)
  have hb (n : ℕ) : |rowProfileSequence u Q p n-rowProfileSequence u Q q n| ≤ 
      L^2/2*(rowCoeffDistance Q (f n) (profileCDF p)+rowCoeffDistance Q (profileCDF p) (profileCDF q)+rowCoeffDistance Q (g n) (profileCDF q)) := by
    have hh := row_composition_L1_stability hQ hu hub
      (rowCDFGrid_valid hQ.le (profileCDF_bounds p) n) (rowCDFGrid_valid hQ.le (profileCDF_bounds q) n)
      (rowCDFGrid_time Q (profileCDF p) n) (rowCDFGrid_time Q (profileCDF q) n) 0
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hf := gaussianStepRightCoefficient_measurable (rowCDFGrid Q (profileCDF p) n)
    have hg := gaussianStepRightCoefficient_measurable (rowCDFGrid Q (profileCDF q) n)
    have hfb := gaussianStepRightCoefficient_bounds (rowCDFGrid_valid hQ.le (profileCDF_bounds p) n)
    have hgb := gaussianStepRightCoefficient_bounds (rowCDFGrid_valid hQ.le (profileCDF_bounds q) n)
    have h1 := rowCoeffDistance_triangle hQ.le hf (profileCDF_monotone p).measurable hg hfb (profileCDF_bounds p) hgb
    have h2 := rowCoeffDistance_triangle hQ.le (profileCDF_monotone p).measurable (profileCDF_monotone q).measurable hg (profileCDF_bounds p) (profileCDF_bounds q) hgb
    rw [rowCoeffDistance_comm Q (profileCDF q) (g n)] at h2
    change rowCoeffDistance Q (f n) (g n) ≤ _
    linarith
  have hfp := rowCDFGrid_L1 hQ (profileCDF_monotone p).measurable (profileCDF_bounds p) (profileCDF_ae_continuous p)
  have hfq := rowCDFGrid_L1 hQ (profileCDF_monotone q).measurable (profileCDF_bounds q) (profileCDF_ae_continuous q)
  have hh := le_of_tendsto_of_tendsto
    ((rowProfileSequence_converges hQ hu hub p).sub (rowProfileSequence_converges hQ hu hub q)).abs
    (((hfp.add tendsto_const_nhds).add hfq).const_mul (L^2/2)) (Eventually.of_forall hb)
  simp only [zero_add,add_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (profileCDF_distance hQ.le p q hp hq) (by positivity))
end MicroscopicJamming

 
open Set Filter MeasureTheory
open scoped Topology

namespace MicroscopicJamming
lemma profileCDF_smooth_inverse {Q : ℝ} {p : SphericalProfile} (hp : RowSmoothProfile Q p.val)
    {m : ℝ → ℝ} (hmb : ∀ t∈Set.Icc 0 Q,0 ≤ m t ∧ m t ≤ 1)
    (hinv : ∀ t∈Set.Icc 0 Q,p.val (m t)=t) {t : ℝ} (ht : t∈Set.Icc 0 Q) :
    profileCDF p t=m t := by
  have hm := hmb t ht
  have he : ({s | p.val s ≤ t} : Set ℝ) =ᵐ[profileRankLaw] (Set.Iic (m t) : Set ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    change (p.val s ≤ t) = (s ≤ m t)
    apply propext
    simpa only [hinv t ht] using hp.strictMonoOn.le_iff_le ⟨hs.1.le,hs.2⟩ hm
  unfold profileCDF
  rw [measureReal_def,measure_congr he]
  have hset : Set.Iic (m t) ∩ Set.Ioc (0:ℝ) 1=Set.Ioc 0 (m t) := by
    ext s; simp only [mem_inter_iff,Set.mem_Iic,Set.mem_Ioc]; constructor
    · exact fun h => ⟨h.2.1,h.1⟩
    · exact fun h => ⟨h.2,h.1,h.2.trans hm.2⟩
  rw [profileRankLaw,Measure.restrict_apply measurableSet_Iic,hset,Real.volume_Ioc]
  simpa only [sub_zero] using ENNReal.toReal_ofReal hm.1

lemma rowCDFGrid_uniform {Q : ℝ} (hQ : 0<Q) {m : ℝ → ℝ} (hm : ContinuousOn m (Set.Icc 0 Q)) :
    TendstoUniformlyOn (fun n => gaussianStepCoefficient (rowCDFGrid Q m n)) m atTop (Set.Icc 0 Q) := by
  have hlen (n : ℕ) : ((n+1:ℕ):ℝ)*(Q/((n:ℝ)+1))=Q := by
    rw [Nat.cast_add,Nat.cast_one]; exact mul_div_cancel₀ Q (by positivity)
  have hlim : Tendsto (fun n : ℕ => Q/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using (tendsto_const_nhds (x:=Q)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have huc := Metric.uniformContinuousOn_iff.mp (isCompact_Icc.uniformContinuousOn_of_continuous hm)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ,hδ,hnear⟩ := huc ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn t ht
  have ht' : t∈Set.Icc 0 (((n+1:ℕ):ℝ)*(Q/((n:ℝ)+1))) := by simpa only [hlen] using ht
  obtain ⟨s,hs,hd,he⟩ := gaussianGrid_coefficient_sample (m:=m) (a:=0) (n+1) (by omega)
    (by positivity : 0 ≤ Q/((n:ℝ)+1)) ht'
  have hs' : s∈Set.Icc 0 Q := by simpa only [hlen,zero_add] using hs
  change dist (m t) (gaussianStepCoefficient (gaussianGrid m 0 (Q/((n:ℝ)+1)) (n+1)) t)<ε
  rw [he]
  apply hnear t ht s hs'
  rw [Real.dist_eq,abs_sub_comm]
  exact (by simpa only [zero_add] using hd : |s-t| ≤ Q/((n:ℝ)+1)).trans_lt hn

lemma rowProfileValue_smooth {u : ℝ → ℝ} {A B C κ Q : ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q)
    (p : SphericalProfile) (hp : RowSmoothProfile Q p.val)
    (f : ℝ → ℝ → ℝ) (hf : RowClassicalRankSolution u p.val f) : rowProfileValue u Q p=f 0 0 := by
  obtain ⟨m,hm,hmb,hinv,hleft⟩ := rowSmooth_inverse hp
  have he := fun t ht => profileCDF_smooth_inverse hp hmb hinv (t:=t) ht
  have hc : ContinuousOn (profileCDF p) (Set.Icc 0 Q) := hm.congr (fun t ht => he t ht)
  have hib : ∀ t∈Set.Icc 0 Q,p.val (profileCDF p t)=t := fun t ht => (congrArg p.val (he t ht)).trans (hinv t ht)
  have hil : ∀ s∈Set.Icc (0:ℝ) 1,profileCDF p (p.val s)=s := fun s hs => (he _ (hp.mapsTo hs)).trans (hleft s hs)
  have hF := rowRank_to_variance hp hc (fun t _ => profileCDF_bounds p t) hib hil hf
  obtain ⟨L,hL,hsolve⟩ := row_variance_existence A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨F,hFF,hbound,huniq,hgrid⟩ := hsolve u hu (profileCDF p) hc (fun t _ => profileCDF_bounds p t)
  have hlim := hgrid (rowCDFGrid Q (profileCDF p)) (rowCDFGrid_valid hQ.le (profileCDF_bounds p))
    (rowCDFGrid_time Q (profileCDF p)) (rowCDFGrid_uniform hQ hc) 1 (by norm_num)
  have ht := hlim.tendsto_at (show ((0:ℝ),(0:ℝ))∈Set.Icc 0 Q ×ˢ Set.Icc (-1) 1 from ⟨⟨le_rfl,hQ.le⟩,by norm_num⟩)
  have hzero : profileCDF p 0=0 := by simpa only [hp.2.1] using hil 0 (by norm_num)
  have hval := huniq (fun t => f (profileCDF p t)) hF 0 ⟨le_rfl,hQ.le⟩ 0
  rw [hzero] at hval
  have hseq : Tendsto (rowProfileSequence u Q p) atTop (𝓝 (f 0 0)) := by
    have hz (n : ℕ) : gaussianStepPath (rowCDFGrid Q (profileCDF p) n) u 0 = gaussianRowComposition (rowCDFGrid Q (profileCDF p) n) u :=
      gaussianStepPath_zero (fun r hr => (rowCDFGrid_valid hQ.le (profileCDF_bounds p) n r hr).2.2) u
    change Tendsto (fun n => gaussianStepPath (rowCDFGrid Q (profileCDF p) n) u 0 0) atTop (𝓝 (F 0 0)) at ht
    simp only [hz,hval] at ht
    exact ht
  exact hseq.limUnder_eq
end MicroscopicJamming

end

end OAI
