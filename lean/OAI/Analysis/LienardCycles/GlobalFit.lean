import OAI.Analysis.LienardCycles.FitProperness

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open Set Filter
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic

lemma label_model_slope {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    J ((label ((k,r),M/r),k),r)=slope ((k,r),M) := by
  have hA : |M/r|<1 := by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hM
  apply (slope_eq hr hM _).symm
  have hh := label_spec (k := k) hr hA
  change H ((J ((label ((k,r),M/r),k),r),k),r)/r=M/r at hh
  exact (div_left_inj' (ne_of_gt hr)).mp hh

lemma label_L_eq {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    L ((label ((k,r),M/r),k),r)=angle (conditionalV ((k,r),M)) := by
  dsimp only [L,D,conditionalV]
  rw [label_model_slope hr hM]

lemma slope_reflection {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    slope ((-k,r),-M)=-slope ((k,r),M) := by
  apply slope_eq hr (by simpa only [abs_neg] using hM)
  rw [reflection _ _ hr,slope_spec hr hM]

lemma Hr_reflection (d k : ℝ) {r : ℝ} (hr : 0 < r) :
    Hr ((-d,-k),r)=-Hr ((d,k),r) := by
  apply (Hr_hasDerivAt hr).unique
  exact (Hr_hasDerivAt hr).neg.congr_of_eventuallyEq
    ((eventually_gt_nhds hr).mono (fun s hs => reflection d k hs))

lemma conditionalV_reflection {r M k : ℝ} (hr : 0 < r) (hM : |M|<r) :
    conditionalV ((-k,r),-M)=-conditionalV ((k,r),M) := by
  dsimp only [conditionalV]
  rw [slope_reflection hr hM,Hr_reflection _ _ hr]

lemma conditionalV_gt {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ∃ k, v < conditionalV ((k,r),M) := by
  by_contra! h
  apply seqL_not_bddAbove hr (show |M/r|<1 by rw [abs_div,abs_of_pos hr]; exact (div_lt_one hr).mpr hM)
  refine ⟨angle v,?_⟩
  rintro y ⟨n,rfl⟩
  change L ((label ((((n:ℝ)+1,r),M/r)),(n:ℝ)+1),r) ≤ angle v
  rw [label_L_eq hr hM]
  apply angle_strictMono.monotoneOn (abs_lt.mp (Hr_abs_lt hr)) (abs_lt.mp hv) (h _)

lemma conditionalV_lt {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ∃ k, conditionalV ((k,r),M)<v := by
  obtain ⟨k,hk⟩ := conditionalV_gt (M := -M) (v := -v) hr (by simpa only [abs_neg] using hM) (by simpa only [abs_neg] using hv)
  refine ⟨-k,?_⟩
  have he := conditionalV_reflection (k := k) (M := -M) hr (by simpa only [abs_neg] using hM)
  simp only [neg_neg] at he
  rw [he]
  linarith

lemma conditionalV_exists {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ∃ k, conditionalV ((k,r),M)=v := by
  obtain ⟨a,ha⟩ := conditionalV_lt hr hM hv
  obtain ⟨b,hb⟩ := conditionalV_gt hr hM hv
  have hab : a < b := (conditionalV_strictMono hr hM).lt_iff_lt.mp (ha.trans hb)
  have hc : Continuous (fun k => conditionalV ((k,r),M)) := by
    apply continuous_iff_continuousAt.mpr
    intro k
    exact ((conditionalV_analytic hr hM).comp (f := fun k : ℝ => ((k,r),M)) k
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).continuousAt
  obtain ⟨k,_,hk⟩ := intermediate_value_Icc hab.le hc.continuousOn ⟨ha.le,hb.le⟩
  exact ⟨k,hk⟩

noncomputable def fitK (q : (ℝ × ℝ) × ℝ) : ℝ := by
  classical
  exact if h : ∃ k, conditionalV ((k,q.1.1),q.1.2)=q.2 then h.choose else 0
noncomputable def fitD (q : (ℝ × ℝ) × ℝ) : ℝ := slope ((fitK q,q.1.1),q.1.2)

lemma fitK_spec {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    conditionalV ((fitK ((r,M),v),r),M)=v := by
  have he := conditionalV_exists hr hM hv
  simp only [fitK,dite_eq_left he]
  exact he.choose_spec
lemma fit_spec {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    H ((fitD ((r,M),v),fitK ((r,M),v)),r)=M ∧
    Hr ((fitD ((r,M),v),fitK ((r,M),v)),r)=v :=
  ⟨slope_spec hr hM,fitK_spec hr hM hv⟩
lemma fitK_eq {r M v k : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1)
    (hk : conditionalV ((k,r),M)=v) : fitK ((r,M),v)=k :=
  (conditionalV_strictMono hr hM).injective ((fitK_spec hr hM hv).trans hk.symm)
lemma fit_unique {r M v d k : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1)
    (hd : H ((d,k),r)=M) (hk : Hr ((d,k),r)=v) :
    fitD ((r,M),v)=d ∧ fitK ((r,M),v)=k := by
  have hs := slope_eq (k := k) hr hM hd
  have he : conditionalV ((k,r),M)=v := by dsimp only [conditionalV]; rw [hs,hk]
  have hfit := fitK_eq hr hM hv he
  refine ⟨?_,hfit⟩
  dsimp only [fitD]
  rw [hfit,hs]

lemma fitK_analytic {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ContDiffAt ℝ ω fitK ((r,M),v) := by
  let k := fitK ((r,M),v)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => conditionalV ((q.2,q.1.1),q.1.2)
  have hf : ContDiffAt ℝ ω f ((r,M),k) :=
    (conditionalV_analytic (k := k) hr hM).comp
      (f := fun q : (ℝ × ℝ) × ℝ => ((q.2,q.1.1),q.1.2)) ((r,M),k)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  obtain ⟨Y,hY,hY₀,he⟩ := ArcEndpoints.level_hit hf (conditionalV_deriv hr hM)
    (fitK_spec hr hM hv) (ne_of_gt (div_pos (G_pos hr) (QuadraticVariation.P_pos hr)))
  apply hY.congr_of_eventuallyEq
  have hp : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((r,M),v), 0 < q.1.1 :=
    continuousAt_const.eventually_lt continuousAt_fst.fst hr
  have hm : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((r,M),v), |q.1.2|<q.1.1 :=
    continuousAt_fst.snd.abs.eventually_lt continuousAt_fst.fst hM
  have hv' : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((r,M),v), |q.2|<1 :=
    continuousAt_snd.abs.eventually_lt continuousAt_const hv
  filter_upwards [he,hp,hm,hv'] with q hq hqr hqM hqv
  exact fitK_eq hqr hqM hqv hq
lemma fitD_analytic {r M v : ℝ} (hr : 0 < r) (hM : |M|<r) (hv : |v|<1) :
    ContDiffAt ℝ ω fitD ((r,M),v) :=
  (slope_analytic (k := fitK ((r,M),v)) hr hM).comp
    (f := fun q : (ℝ × ℝ) × ℝ => ((fitK q,q.1.1),q.1.2)) ((r,M),v)
    (((fitK_analytic hr hM hv).prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
end QuinticLienard.QuadraticFit

end OAI
