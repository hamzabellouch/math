import OAI.Analysis.LienardCycles.QuadraticDerivatives

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open ScalarArcs ArcEndpoints CanonicalVariation PolynomialModel WidthCoordinates
  PartialCalculus QuadraticCoordinates

noncomputable def m (q : (ℝ × ℝ) × ℝ) : ℝ := q.2-H q
noncomputable def n (q : (ℝ × ℝ) × ℝ) : ℝ := q.2+H q
noncomputable def ell (q : (ℝ × ℝ) × ℝ) : ℝ := (1+Hr q)/(1-Hr q)

lemma m_pos {d k r : ℝ} (hr : 0 < r) : 0 < m ((d,k),r) := by
  have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).2
  dsimp [m]; linarith
lemma n_pos {d k r : ℝ} (hr : 0 < r) : 0 < n ((d,k),r) := by
  have hh := (abs_lt.mp (H_abs_lt (d := d) (k := k) hr)).1
  dsimp [n]; linarith
lemma mr_pos {d k r : ℝ} (hr : 0 < r) : 0 < 1-Hr ((d,k),r) := by
  have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).2
  linarith
lemma ell_pos {d k r : ℝ} (hr : 0 < r) : 0 < ell ((d,k),r) := by
  apply div_pos _ (mr_pos hr)
  have hh := (abs_lt.mp (Hr_abs_lt (d := d) (k := k) hr)).1
  linarith

theorem radius_chart {d k r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ → ℝ, ContDiffAt ℝ ω ρ (m ((d,k),r)) ∧
      ρ (m ((d,k),r)) = r ∧
      (∀ᶠ s in 𝓝 (m ((d,k),r)), m ((d,k),ρ s)=s) ∧
      HasDerivAt ρ (1/(1-Hr ((d,k),r))) (m ((d,k),r)) := by
  let f : ℝ × ℝ → ℝ := fun q => m ((d,k),q.2)-q.1
  have hf : ContDiffAt ℝ ω f (m ((d,k),r),r) :=
    (contDiffAt_snd.sub ((H_analytic (d := d) (k := k) hr).comp (m ((d,k),r),r)
      (contDiffAt_const.prodMk contDiffAt_snd))).sub
      contDiffAt_fst
  have hd : HasDerivAt (fun s => f (m ((d,k),r),s)) (1-Hr ((d,k),r)) r :=
    ((hasDerivAt_id r).sub (Hr_hasDerivAt hr)).sub_const _
  obtain ⟨ρ,hρ,hρ0,he,_⟩ := transverse_hit hf hd (ne_of_gt (mr_pos hr))
  have he0 : ∀ᶠ s in 𝓝 (m ((d,k),r)), m ((d,k),ρ s)=s := by
    filter_upwards [he] with s hs
    dsimp [f] at hs
    linarith
  have hdρ := (hρ.differentiableAt (by simp)).hasDerivAt
  have hmD : HasDerivAt (fun s => m ((d,k),s)) (1-Hr ((d,k),r))
      (ρ (m ((d,k),r))) := by
    rw [hρ0]
    exact (hasDerivAt_id r).sub (Hr_hasDerivAt hr)
  have hcomp := hmD.comp (m ((d,k),r)) hdρ
  have hder := hcomp.unique ((hasDerivAt_id _).congr_of_eventuallyEq he0)
  have heder : deriv ρ (m ((d,k),r))=1/(1-Hr ((d,k),r)) := by
    apply (eq_div_iff (ne_of_gt (mr_pos hr))).mpr
    simpa only [mul_comm] using hder
  exact ⟨ρ,hρ,hρ0,he0,by simpa only [heder] using hdρ⟩

structure LowerChart (d k r : ℝ) where
  radius : ℝ → ℝ
  upper : ℝ → ℝ
  solution : ℝ × ℝ → ℝ
  radius_analytic : ContDiffAt ℝ ω radius (m ((d,k),r))
  radius_base : radius (m ((d,k),r)) = r
  radius_relation : ∀ᶠ s in 𝓝 (m ((d,k),r)), m ((d,k),radius s)=s
  radius_derivative : HasDerivAt radius (1/(1-Hr ((d,k),r))) (m ((d,k),r))
  upper_def : ∀ s, upper s=n ((d,k),radius s)
  upper_analytic : ContDiffAt ℝ ω upper (m ((d,k),r))
  upper_base : upper (m ((d,k),r)) = n ((d,k),r)
  upper_derivative : HasDerivAt upper (ell ((d,k),r)) (m ((d,k),r))
  solution_continuous : ∀ s, Continuous (fun y => solution (s,y))
  solution_analytic : ∀ y ∈ Icc (-m ((d,k),r)) (n ((d,k),r)),
    ContDiffAt ℝ ω solution (m ((d,k),r),y)
  equation : ∀ y ∈ Icc (-m ((d,k),r)) (n ((d,k),r)),
    ∀ᶠ q in 𝓝 (m ((d,k),r),y), HasDerivAt (fun s => solution (q.1,s))
      (d*solution q+(k/2)*(solution q)^2-q.2) q.2
  lower_zero : ∀ᶠ s in 𝓝 (m ((d,k),r)), solution (s,-s)=0
  upper_zero : ∀ᶠ s in 𝓝 (m ((d,k),r)), solution (s,upper s)=0

theorem lower_chart {d k r : ℝ} (hr : 0 < r) : Nonempty (LowerChart d k r) := by
  obtain ⟨ρ,hρ,hρ0,hρeq,hρd⟩ := radius_chart (d := d) (k := k) hr
  let m₀ := m ((d,k),r)
  have hρbase : ρ m₀ = r := hρ0
  let Y : ℝ → ℝ := fun s => n ((d,k),ρ s)
  have hY : ContDiffAt ℝ ω Y m₀ := by
    have hH0 : ContDiffAt ℝ ω H ((d,k),ρ m₀) := by
      rw [hρbase]; exact H_analytic hr
    exact hρ.add (ContDiffAt.comp m₀ (g := H)
      (f := fun s => ((d,k),ρ s)) hH0 (contDiffAt_const.prodMk hρ))
  have hY0 : Y m₀=n ((d,k),r) := by simp only [Y,m₀,hρ0]
  have hYd : HasDerivAt Y (ell ((d,k),r)) m₀ := by
    have hnD : HasDerivAt (fun s => n ((d,k),s)) (1+Hr ((d,k),r)) (ρ m₀) := by
      rw [hρbase]
      exact (hasDerivAt_id r).add (Hr_hasDerivAt hr)
    have hd := hnD.comp m₀ hρd
    convert! hd using 1
    dsimp [ell]
    ring
  let T : ℝ → ℝ := fun s => peakAtWidth profile (((d,k),0),ρ s)
  have hT : ContDiffAt ℝ ω T m₀ := by
    have hT0 : ContDiffAt ℝ ω (peakAtWidth profile) (((d,k),0),ρ m₀) := by
      rw [hρbase]
      exact peak_analytic profile profile_contDiff model_local_flow hr
    exact ContDiffAt.comp m₀ (g := peakAtWidth profile)
      (f := fun s => (((d,k),(0:ℝ)),ρ s)) hT0 (contDiffAt_const.prodMk hρ)
  have hTs : 0 < T m₀ := by
    simpa only [T,m₀,hρ0] using (peak_spec profile profile_contDiff model_local_flow
      (p := (d,k)) (h := 0) hr).1
  obtain ⟨w,hwc,_,hwd,hwe,hwa⟩ := endpoint_witness profile profile_contDiff model_local_flow hTs
  let u : ℝ × ℝ → ℝ := fun q => w (((d,k),T q.1),q.2)
  have hlift (y : ℝ) : ContDiffAt ℝ ω
      (fun q : ℝ × ℝ => (((d,k),T q.1),q.2)) (m₀,y) :=
    (contDiffAt_const.prodMk (hT.comp (m₀,y) contDiffAt_fst)).prodMk contDiffAt_snd
  have href := FixedWidthFamilies.endpoint_formulas profile profile_contDiff model_local_flow
    (p := (d,k)) (h := 0) hr
  have hlower : lowerFamily profile (((d,k),T m₀),0) = -m ((d,k),r) := by
    dsimp only [T]
    rw [hρbase]
    have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
    rw [href.1,h0,add_zero]
    dsimp [m,H]; ring
  have hupper : upperFamily profile (((d,k),T m₀),0) = n ((d,k),r) := by
    dsimp only [T]
    rw [hρbase]
    have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
    rw [href.2,h0,add_zero]
    exact add_comm _ _
  rw [hlower,hupper] at hwd hwe
  have hua (y : ℝ) (hy : y ∈ Icc (-m ((d,k),r)) (n ((d,k),r))) :
      ContDiffAt ℝ ω u (m₀,y) := (hwd y hy).comp (m₀,y) (hlift y)
  have hue (y : ℝ) (hy : y ∈ Icc (-m ((d,k),r)) (n ((d,k),r))) :
      ∀ᶠ q in 𝓝 (m₀,y), HasDerivAt (fun s => u (q.1,s))
        (d*u q+(k/2)*(u q)^2-q.2) q.2 := by
    filter_upwards [(hlift y).continuousAt.eventually (hwe y hy)] with q hq
    simpa only [profile] using hq
  have harch : ∀ᶠ s in 𝓝 m₀,
      IsArch (fun x => profile ((d,k),x)) (fun y => u (s,y)) 0 (T s) (-s) (Y s) := by
    have hmap : ContinuousAt (fun s => (((d,k),T s),(0:ℝ))) m₀ :=
      (continuousAt_const.prodMk hT.continuousAt).prodMk continuousAt_const
    have hpos : ∀ᶠ s in 𝓝 m₀, 0 < ρ s :=
      continuousAt_const.eventually_lt hρ.continuousAt (by simpa only [hρbase] using hr)
    filter_upwards [hmap.eventually hwa,hpos,hρeq] with s hs hps heq
    have hf := FixedWidthFamilies.endpoint_formulas profile profile_contDiff model_local_flow
      (p := (d,k)) (h := 0) hps
    have hl : lowerFamily profile (((d,k),T s),0) = -s := by
      have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
      change ρ s-H ((d,k),ρ s)=s at heq
      change lowerFamily profile (((d,k),T s),0) = -s
      rw [show lowerFamily profile (((d,k),T s),0) =
        H ((d,k),ρ s)+profile ((d,k),0)-ρ s from hf.1,h0]
      linarith
    have hu : upperFamily profile (((d,k),T s),0) = Y s := by
      have h0 : profile ((d,k),(0:ℝ)) = 0 := by simp [profile]
      change upperFamily profile (((d,k),T s),0) = ρ s+H ((d,k),ρ s)
      rw [hf.2,h0,add_zero]
      exact add_comm _ _
    simpa only [hl,hu] using hs
  exact ⟨{ radius := ρ
           upper := Y
           solution := u
           radius_analytic := hρ
           radius_base := hρ0
           radius_relation := hρeq
           radius_derivative := hρd
           upper_def := fun _ => rfl
           upper_analytic := hY
           upper_base := hY0
           upper_derivative := hYd
           solution_continuous := fun s => hwc ((d,k),T s)
           solution_analytic := hua
           equation := hue
           lower_zero := harch.mono (fun _ hs => hs.lower)
           upper_zero := harch.mono (fun _ hs => hs.upper) }⟩

end QuinticLienard.ModelEndpoint

end OAI
