import OAI.Analysis.LienardCycles.PositiveTransport

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open PartialCalculus QuadraticCoordinates ReferenceCharacteristic

lemma slope_curvature_deriv {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    HasDerivAt (fun a => slope ((a,r),M))
      (-Q ((slope ((k,r),M),k),r)/P ((slope ((k,r),M),k),r)) k := by
  have hs := ((slope_analytic hr hM).comp (f := fun a : ℝ => ((a,r),M)) k
    ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hprod := (H_analytic (d := slope ((k,r),M)) (k := k) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((slope ((a,r),M),a),r)) k
      ((hs.hasDerivAt.prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have he := hprod.unique ((hasDerivAt_const k M).congr_of_eventuallyEq
    (Eventually.of_forall (fun a => slope_spec (k := a) hr hM)))
  rw [fderiv_model] at he
  have hP := ne_of_gt (QuadraticVariation.P_pos (d := slope ((k,r),M)) (k := k) hr)
  have hd : deriv (fun a => slope ((a,r),M)) k = -Q ((slope ((k,r),M),k),r)/P ((slope ((k,r),M),k),r) := by
    dsimp only [P,Q,Hr] at hP ⊢
    field_simp [hP]
    simp only [one_mul,zero_mul,add_zero,Function.comp_def] at he
    linarith
  rw [←hd]
  exact hs.hasDerivAt

noncomputable def conditionalV (q : (ℝ × ℝ) × ℝ) : ℝ := Hr ((slope q,q.1.1),q.1.2)

lemma conditionalV_analytic {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    ContDiffAt ℝ ω conditionalV ((k,r),M) :=
  (Hr_analytic (d := slope ((k,r),M)) (k := k) hr).comp
    (f := fun q : (ℝ × ℝ) × ℝ => ((slope q,q.1.1),q.1.2)) ((k,r),M)
    (((slope_analytic hr hM).prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)

lemma conditionalV_deriv {k r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    HasDerivAt (fun a => conditionalV ((a,r),M))
      (G ((slope ((k,r),M),k),r)/P ((slope ((k,r),M),k),r)) k := by
  have h := (Hr_analytic (d := slope ((k,r),M)) (k := k) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((slope ((a,r),M),a),r)) k
      (((slope_curvature_deriv hr hM).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  rw [fderiv_model] at h
  have hR := direction_comm (H_analytic (d := slope ((k,r),M)) (k := k) hr) ((1,0),0) ((0,0),1)
  have hS := direction_comm (H_analytic (d := slope ((k,r),M)) (k := k) hr) ((0,1),0) ((0,0),1)
  change direction ((1,0),0) Hr _=R _ at hR
  change direction ((0,1),0) Hr _=S _ at hS
  convert! h using 1
  rw [hR,hS]
  dsimp only [G]
  field_simp [ne_of_gt (QuadraticVariation.P_pos (d := slope ((k,r),M)) (k := k) hr)]
  ring

lemma conditionalV_strictMono {r M : ℝ} (hr : 0 < r) (hM : |M| < r) :
    StrictMono (fun k => conditionalV ((k,r),M)) := by
  apply strictMono_of_deriv_pos
  intro k
  rw [(conditionalV_deriv hr hM).deriv]
  exact div_pos (G_pos hr) (QuadraticVariation.P_pos hr)

lemma reference_midpoint_exists {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    ∃ z, A ((z,k),r)=A₀ := by
  have hm : |r*A₀|<r := by rw [abs_mul,abs_of_pos hr]; nlinarith
  obtain ⟨d,hd⟩ := midpoint_exists (k := k) hr hm
  obtain ⟨z,hz⟩ := J_surjective d k hr
  refine ⟨z,?_⟩
  dsimp only [A]
  rw [hz,hd]
  field_simp

lemma reference_midpoint_strictMono (k : ℝ) {r : ℝ} (hr : 0 < r) :
    StrictMono (fun z => A ((z,k),r)) := by
  apply strictMono_of_deriv_pos
  intro z
  rw [(Az_hasDerivAt hr).deriv]
  exact Az_pos hr

noncomputable def label (q : (ℝ × ℝ) × ℝ) : ℝ := by
  classical
  exact if h : ∃ z, A ((z,q.1.1),q.1.2)=q.2 then h.choose else 0

lemma label_spec {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    A ((label ((k,r),A₀),k),r)=A₀ := by
  have he := reference_midpoint_exists (k := k) hr hA
  simp only [label,dite_eq_left he]
  exact he.choose_spec

lemma label_eq {k r A₀ z : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hz : A ((z,k),r)=A₀) : label ((k,r),A₀)=z :=
  (reference_midpoint_strictMono k hr).injective ((label_spec hr hA).trans hz.symm)

lemma label_analytic {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    ContDiffAt ℝ ω label ((k,r),A₀) := by
  let z := label ((k,r),A₀)
  let f : (ℝ × ℝ) × ℝ → ℝ := fun q => A ((q.2,q.1.1),q.1.2)
  have hf : ContDiffAt ℝ ω f ((k,r),z) :=
    (A_analytic (q := ((z,k),r)) hr).comp (g := A)
      (f := fun q : (ℝ × ℝ) × ℝ => ((q.2,q.1.1),q.1.2)) ((k,r),z)
      ((contDiffAt_snd.prodMk contDiffAt_fst.fst).prodMk contDiffAt_fst.snd)
  obtain ⟨Y,hY,hY₀,he⟩ := ArcEndpoints.level_hit hf (Az_hasDerivAt hr)
    (label_spec hr hA) (ne_of_gt (Az_pos hr))
  apply hY.congr_of_eventuallyEq
  have hpos : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),A₀), 0 < q.1.2 :=
    continuousAt_const.eventually_lt continuousAt_fst.snd hr
  have habs : ∀ᶠ q : (ℝ × ℝ) × ℝ in 𝓝 ((k,r),A₀), |q.2| < 1 :=
    continuousAt_snd.abs.eventually_lt continuousAt_const hA
  filter_upwards [he,hpos,habs] with q hq hqr hqA
  exact label_eq hqr hqA hq

lemma label_curvature_deriv {k r A₀ : ℝ} (hr : 0 < r) (hA : |A₀| < 1) :
    HasDerivAt (fun a => label ((a,r),A₀)) (-T ((label ((k,r),A₀),k),r)) k := by
  have hs := ((label_analytic hr hA).comp (f := fun a : ℝ => ((a,r),A₀)) k
    ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)).differentiableAt (by simp)
  have hprod := (A_analytic (q := ((label ((k,r),A₀),k),r)) hr).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((label ((a,r),A₀),a),r)) k
      ((hs.hasDerivAt.prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k r))
  have he := hprod.unique ((hasDerivAt_const k A₀).congr_of_eventuallyEq
    (Eventually.of_forall (fun a => label_spec (k := a) hr hA)))
  rw [fderiv_model] at he
  have hP := ne_of_gt (Az_pos (z := label ((k,r),A₀)) (k := k) hr)
  have hd : deriv (fun a => label ((a,r),A₀)) k = -T ((label ((k,r),A₀),k),r) := by
    dsimp only [T,Az,Ak] at hP ⊢
    field_simp [hP]
    simp only [one_mul,zero_mul,add_zero,Function.comp_def] at he
    linarith
  rw [←hd]
  exact hs.hasDerivAt

lemma T_strictAnti (z k : ℝ) : StrictAntiOn (fun s => T ((z,k),s)) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun s hs => (T_deriv hs).continuousAt.continuousWithinAt)
  intro s hs
  have hs' : 0 < s := interior_subset hs
  rw [(T_deriv (z := z) (k := k) hs').deriv]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (A_gap_pos hs'))
      (QuadraticVariation.Q_pos hs')) (Jz_pos hs'))
    (mul_pos hs' (sq_pos_of_pos (Az_pos hs')))

lemma conditionalA_deriv {k r A₀ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1) (hs : 0 < s) :
    HasDerivAt (fun a => A ((label ((a,r),A₀),a),s))
      (Az ((label ((k,r),A₀),k),s)*(T ((label ((k,r),A₀),k),s)-T ((label ((k,r),A₀),k),r))) k := by
  have h := (A_analytic (q := ((label ((k,r),A₀),k),s)) hs).differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt (f := fun a => ((label ((a,r),A₀),a),s)) k
      (((label_curvature_deriv hr hA).prodMk (hasDerivAt_id k)).prodMk (hasDerivAt_const k s))
  rw [fderiv_model] at h
  convert! h using 1
  have h₁ := ne_of_gt (Az_pos (z := label ((k,r),A₀)) (k := k) hs)
  have h₂ := ne_of_gt (Az_pos (z := label ((k,r),A₀)) (k := k) hr)
  dsimp only [T,Az,Ak] at h₁ h₂ ⊢
  field_simp [h₁,h₂]
  ring

lemma conditionalA_strictMono {r A₀ s : ℝ} (hr : 0 < r) (hA : |A₀| < 1)
    (hs : 0 < s) (hsr : s < r) : StrictMono (fun k => A ((label ((k,r),A₀),k),s)) := by
  apply strictMono_of_deriv_pos
  intro k
  rw [(conditionalA_deriv hr hA hs).deriv]
  exact mul_pos (Az_pos hs) (sub_pos.mpr (T_strictAnti _ _ hs hr hsr))
end QuinticLienard.QuadraticFit

end OAI
