import OAI.Analysis.LienardCycles.CurvatureComparison

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open PartialCalculus QuadraticCoordinates ArcEndpoints

lemma midpoint_strictMono (k : ℝ) {r : ℝ} (hr : 0 < r) :
    StrictMono (fun d => H ((d,k),r)) := by
  apply strictMono_of_deriv_pos
  intro d
  rw [(P_hasDerivAt hr).deriv]
  exact QuadraticVariation.P_pos hr

lemma midpoint_above (k : ℝ) {r M : ℝ} (hr : 0 < r) (hM : M < r) :
    ∃ d, M < H ((d,k),r) := by
  by_contra! hn
  let h₀ := H (((0:ℝ),k),r)
  have hh₀ := abs_lt.mp (H_abs_lt (d := 0) (k := k) hr)
  let c := (r-M)*(r+h₀)
  have hc : 0 < c := mul_pos (sub_pos.mpr hM) (by dsimp [h₀]; linarith [hh₀.1])
  let B := 2*r/c+|k|+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlen : 0 < 2*r+1 := by linarith
  have hab : B < B+(2*r+1) := lt_add_of_pos_right _ hlen
  obtain ⟨d,hd,he⟩ := exists_hasDerivAt_eq_slope
    (fun x => H ((x,k),r)) (fun x => P ((x,k),r)) hab
    (fun x _ => (P_hasDerivAt hr).continuousAt.continuousWithinAt)
    (fun x _ => P_hasDerivAt hr)
  have hp := QuadraticVariation.P_pos (d := d) (k := k) hr
  have hp1 : P ((d,k),r) < 1 := by
    rw [he]
    apply (div_lt_one (by linarith : 0 < B+(2*r+1)-B)).mpr
    have ha := (abs_lt.mp (H_abs_lt (d := B) (k := k) hr)).1
    have hb := (abs_lt.mp (H_abs_lt (d := B+(2*r+1)) (k := k) hr)).2
    linarith
  have hd0 : 0 < d := hB.trans hd.1
  have hlo : h₀ ≤ H ((d,k),r) := (midpoint_strictMono k hr).monotone hd0.le
  have hhi := hn d
  have hgap : c ≤ r^2-H ((d,k),r)^2 := by
    have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).1
    have hm := mul_le_mul (show r-M ≤ r-H ((d,k),r) by linarith)
      (show r+h₀ ≤ r+H ((d,k),r) by linarith)
      (show 0 ≤ r+h₀ by dsimp [h₀]; linarith [hh₀.1])
      (show 0 ≤ r-H ((d,k),r) by linarith)
    dsimp [c]
    nlinarith [hm]
  have hkp : -|k| ≤ k*P ((d,k),r) := by
    have h₁ := mul_le_mul_of_nonneg_right (neg_abs_le k) hp.le
    have h₂ := mul_le_mul_of_nonneg_left hp1.le (abs_nonneg k)
    nlinarith
  have hlow : 2*r/c < d+k*P ((d,k),r) := by
    dsimp [B] at hd
    linarith [hd.1]
  have hsum : 0 < d+k*P ((d,k),r) := (div_pos (by linarith) hc).trans hlow
  have hm₁ := (div_lt_iff₀ hc).mp hlow
  have hm₂ := mul_le_mul_of_nonneg_left hgap hsum.le
  have heq := width_identity (d := d) (k := k) hr
  have hGN := ne_of_gt (H_gap_pos (d := d) (k := k) hr)
  have heq' : (d+k*P ((d,k),r))*(r^2-H ((d,k),r)^2)=r*Hr ((d,k),r)+H ((d,k),r) := by
    apply (eq_div_iff hGN).mp
    simpa only [add_comm,gap] using heq
  have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).2
  have hv := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).2
  have hh₁ := mul_lt_mul_of_pos_left hv hr
  nlinarith [hm₁,hm₂,heq']

lemma midpoint_below (k : ℝ) {r M : ℝ} (hr : 0 < r) (hM : -r < M) :
    ∃ d, H ((d,k),r) < M := by
  obtain ⟨d,hd⟩ := midpoint_above (-k) hr (show -M < r by linarith)
  refine ⟨-d,?_⟩
  have he := reflection d (-k) hr
  simp only [neg_neg] at he
  rw [he]
  linarith

lemma midpoint_exists {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    ∃ d, H ((d,k),r)=M := by
  obtain ⟨a,ha⟩ := midpoint_below k hr (abs_lt.mp hM).1
  obtain ⟨b,hb⟩ := midpoint_above k hr (abs_lt.mp hM).2
  have hab : a < b := (midpoint_strictMono k hr).lt_iff_lt.mp (ha.trans hb)
  obtain ⟨d,_,hd⟩ := intermediate_value_Icc hab.le
    (fun x _ => (P_hasDerivAt hr).continuousAt.continuousWithinAt) ⟨ha.le,hb.le⟩
  exact ⟨d,hd⟩

noncomputable def slope (q : (ℝ × ℝ) × ℝ) : ℝ := by
  classical
  exact if h : ∃ d, H ((d,q.1.1),q.1.2)=q.2 then h.choose else 0

lemma slope_spec {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    H ((slope ((k,r),M),k),r)=M := by
  have he := midpoint_exists (k := k) hr hM
  simp only [slope,dite_eq_left he]
  exact he.choose_spec

lemma slope_eq {k r M d : ℝ} (hr : 0 < r) (hM : |M| < r)
    (hd : H ((d,k),r)=M) : slope ((k,r),M)=d :=
  (midpoint_strictMono k hr).injective ((slope_spec hr hM).trans hd.symm)

lemma slope_analytic {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    ContDiffAt ℝ ω slope ((k,r),M) := by
  let d := slope ((k,r),M)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => H ((q.2,q.1.1),q.1.2)
  have hf : ContDiffAt ℝ ω f ((k,r),d) :=
    (H_analytic (d := d) (k := k) hr).comp (g := H) (f := fun q : (ℝ × ℝ) × ℝ => ((q.2,q.1.1),q.1.2)) ((k,r),d)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  have hd : HasDerivAt (fun s => f ((k,r),s)) (P ((d,k),r)) d := P_hasDerivAt hr
  obtain ⟨Y,hY,hY₀,he⟩ := level_hit hf hd (slope_spec hr hM)
    (ne_of_gt (QuadraticVariation.P_pos hr))
  apply hY.congr_of_eventuallyEq
  have hpos : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),M), 0 < q.1.2 :=
    continuousAt_const.eventually_lt continuousAt_fst.snd hr
  have habs : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),M), |q.2| < q.1.2 :=
    continuousAt_snd.abs.eventually_lt continuousAt_fst.snd hM
  filter_upwards [he,hpos,habs] with q hq hqr hqM
  exact slope_eq hqr hqM hq

end QuinticLienard.QuadraticFit

end OAI
