import OAI.Analysis.LienardCycles.AxisBranches

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus
lemma endpoint_germ_eq {a : Fin 6 → ℝ} {u : Bool} {t : ℝ} {G : ℝ×ℝ → ℝ}
    (ht : 0<t) (hG : ContDiffAt ℝ ω G (t,0))
    (he : ∀ᶠ q in 𝓝 (t,(0:ℝ)), 0<q.2 → G q=branch a u q) :
    ∀ᶠ s in 𝓝 t, G (s,0)=axisEndpoint a u s := by
  have hGc : ∀ᶠ s in 𝓝 t, ContinuousAt G (s,0) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually (hG.eventually (by simp))] with s hs
    exact hs.continuousAt
  filter_upwards [eventually_gt_nhds ht,he.curry_nhds,hGc] with s hs hse hsc
  have hlim : Tendsto (fun x=>G (s,x)) (𝓝[>] 0) (𝓝 (G (s,0))) :=
    (hsc.comp (f:=fun x : ℝ=>(s,x)) (continuousAt_const.prodMk continuousAt_id)).tendsto.mono_left inf_le_left
  have hEq : (fun x=>G (s,x)) =ᶠ[𝓝[>] 0] (fun x=>branch a u (s,x)) := by
    filter_upwards [hse.filter_mono inf_le_left,self_mem_nhdsWithin] with x hx hx0
    exact hx hx0
  exact tendsto_nhds_unique hlim ((branch_tendsto a u hs).congr' hEq.symm)
lemma axisEndpoint_analytic (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t)
    (htr : axisEndpoint a u t≠poly a 0) : ContDiffAt ℝ ω (axisEndpoint a u) t := by
  obtain ⟨G,hG,_,he,_⟩ := endpoint_germ a u ht htr
  exact (hG.comp t (contDiffAt_id.prodMk contDiffAt_const)).congr_of_eventuallyEq
    ((endpoint_germ_eq ht hG he).mono fun _ h=>h.symm)
lemma axisEndpoint_sign (a : Fin 6 → ℝ) (u : Bool) {t : ℝ} (ht : 0<t)
    (htr : axisEndpoint a u t≠poly a 0) :
    if u then 0<deriv (axisEndpoint a u) t else deriv (axisEndpoint a u) t<0 := by
  obtain ⟨G,hG,_,he,hd⟩ := endpoint_germ a u ht htr
  have hde : deriv (axisEndpoint a u) t=first G (t,0) :=
    ((first_hasDerivAt (hG.differentiableAt (by simp))).congr_of_eventuallyEq
      ((endpoint_germ_eq ht hG he).mono fun _ h=>h.symm)).deriv
  rwa [hde]

lemma endpoint_peak_order (a : Fin 6 → ℝ) {h s t : ℝ} (hh : 0<h) (hs : h<s) (hst : s≤t) :
    endpoint a false h t≤endpoint a false h s ∧ endpoint a true h s≤endpoint a true h t := by
  have ha (u : Bool) (p : ℝ) (hp : h<p) : ContDiffAt ℝ ω (fun q=>endpoint a u h q) p := by
    obtain ⟨hl,hr⟩ := PositiveVariation.endpoints (QuinticProfile.profile a)
      (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh hp
    cases u
    · exact hl.comp p ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)
    · exact hr.comp p ((contDiffAt_const.prodMk contDiffAt_id).prodMk contDiffAt_const)
  have hd (p : ℝ) (hp : h<p) := PositiveVariation.peak_signs (QuinticProfile.profile a)
      (fun _ h=>QuinticProfile.analytic a h) (QuinticProfile.local_flow a) (p:=(0:ℝ)) hh hp
  have hl : AntitoneOn (endpoint a false h) (Ioi h) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi h)
      (fun p hp=>(ha false p hp).continuousAt.continuousWithinAt)
      (fun p hp=>(ha false p (interior_subset hp)).differentiableAt (by simp) |>.differentiableWithinAt)
    intro p hp
    exact (hd p (interior_subset hp)).1.le
  have hr : MonotoneOn (endpoint a true h) (Ioi h) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi h)
      (fun p hp=>(ha true p hp).continuousAt.continuousWithinAt)
      (fun p hp=>(ha true p (interior_subset hp)).differentiableAt (by simp) |>.differentiableWithinAt)
    intro p hp
    exact (hd p (interior_subset hp)).2.le
  exact ⟨hl hs (hs.trans_le hst) hst,hr hs (hs.trans_le hst) hst⟩
lemma axis_peak_order (a : Fin 6 → ℝ) {s t : ℝ} (hs : 0<s) (hst : s≤t) :
    axisEndpoint a false t≤axisEndpoint a false s ∧ axisEndpoint a true s≤axisEndpoint a true t := by
  have hE : ∀ᶠ h in 𝓝[>] (0:ℝ), endpoint a false h t≤endpoint a false h s ∧
      endpoint a true h s≤endpoint a true h t := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hs).filter_mono inf_le_left] with h hh hs'
    exact endpoint_peak_order a hh hs' hst
  have hls := lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn hs
  have hlt := lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn (hs.trans_le hst)
  have hrs := upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn hs
  have hrt := upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn (hs.trans_le hst)
  exact ⟨le_of_tendsto_of_tendsto hlt hls (hE.mono fun _ h=>h.1),
    le_of_tendsto_of_tendsto hrs hrt (hE.mono fun _ h=>h.2)⟩

def transversePeaks (a : Fin 6 → ℝ) : Set ℝ :=
  {t | 0<t ∧ axisEndpoint a false t<poly a 0 ∧ poly a 0<axisEndpoint a true t}
lemma transversePeaks_upper (a : Fin 6 → ℝ) {s t : ℝ} (hs : s ∈ transversePeaks a) (hst : s≤t) :
    t ∈ transversePeaks a := by
  have he := axis_peak_order a hs.1 hst
  exact ⟨hs.1.trans_le hst,he.1.trans_lt hs.2.1,hs.2.2.trans_le he.2⟩
lemma transversePeaks_open (a : Fin 6 → ℝ) : IsOpen (transversePeaks a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  have hl := (axisEndpoint_analytic a false ht.1 ht.2.1.ne).continuousAt
  have hr := (axisEndpoint_analytic a true ht.1 ht.2.2.ne').continuousAt
  exact (eventually_gt_nhds ht.1).and
    ((hl.eventually_lt continuousAt_const ht.2.1).and (continuousAt_const.eventually_lt hr ht.2.2))
lemma transversePeaks_ordConnected (a : Fin 6 → ℝ) : OrdConnected (transversePeaks a) := by
  constructor
  intro s hs t _ x hx
  exact transversePeaks_upper a hs hx.1
noncomputable def axisWidth (a : Fin 6 → ℝ) (t : ℝ) : ℝ := (axisEndpoint a true t-axisEndpoint a false t)/2
noncomputable def axisCenter (a : Fin 6 → ℝ) (t : ℝ) : ℝ := (axisEndpoint a true t+axisEndpoint a false t)/2-poly a 0
lemma axisWidth_analytic (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    ContDiffAt ℝ ω (axisWidth a) t :=
  ((axisEndpoint_analytic a true ht.1 ht.2.2.ne').sub (axisEndpoint_analytic a false ht.1 ht.2.1.ne)).div_const 2
lemma axisCenter_analytic (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    ContDiffAt ℝ ω (axisCenter a) t :=
  (((axisEndpoint_analytic a true ht.1 ht.2.2.ne').add (axisEndpoint_analytic a false ht.1 ht.2.1.ne)).div_const 2).sub contDiffAt_const
lemma axisWidth_pos_deriv (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    0<axisWidth a t ∧ 0<deriv (axisWidth a) t ∧ |axisCenter a t|<axisWidth a t ∧
      |deriv (axisCenter a) t/deriv (axisWidth a) t|<1 := by
  have hl := axisEndpoint_sign a false ht.1 ht.2.1.ne
  have hr := axisEndpoint_sign a true ht.1 ht.2.2.ne'
  simp only [Bool.false_eq_true,↓reduceIte] at hl hr
  have hld := (axisEndpoint_analytic a false ht.1 ht.2.1.ne).differentiableAt (by simp)
  have hrd := (axisEndpoint_analytic a true ht.1 ht.2.2.ne').differentiableAt (by simp)
  have hwd : deriv (axisWidth a) t=(deriv (axisEndpoint a true) t-deriv (axisEndpoint a false) t)/2 :=
    ((hrd.hasDerivAt.sub hld.hasDerivAt).div_const 2).deriv
  have hcd : deriv (axisCenter a) t=(deriv (axisEndpoint a true) t+deriv (axisEndpoint a false) t)/2 :=
    (((hrd.hasDerivAt.add hld.hasDerivAt).div_const 2).sub_const (poly a 0)).deriv
  have hp : 0<axisWidth a t := by dsimp [axisWidth]; linarith [ht.2.1,ht.2.2]
  refine ⟨hp,by rw [hwd]; linarith,?_,?_⟩
  · rw [abs_lt]
    dsimp [axisCenter,axisWidth]
    constructor <;> linarith [ht.2.1,ht.2.2]
  · rw [hwd,hcd]
    rw [abs_div,abs_of_pos (show 0<(deriv (axisEndpoint a true) t-deriv (axisEndpoint a false) t)/2 by linarith),div_lt_one]
    · rw [abs_lt]; constructor <;> linarith
    · linarith
lemma axisWidth_strictMono (a : Fin 6 → ℝ) : StrictMonoOn (axisWidth a) (transversePeaks a) := by
  apply strictMonoOn_of_deriv_pos (convex_iff_ordConnected.mpr (transversePeaks_ordConnected a))
    (fun t ht=>(axisWidth_analytic a ht).continuousAt.continuousWithinAt)
  intro t ht
  exact (axisWidth_pos_deriv a (interior_subset ht)).2.1
end QuinticLienard.AxisFlow

end OAI
