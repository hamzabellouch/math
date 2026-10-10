import OAI.Analysis.LienardCycles.AxisRegularity

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
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth

def axisWidths (a : Fin 6 → ℝ) : Set ℝ := axisWidth a '' transversePeaks a
noncomputable def axisPeak (a : Fin 6 → ℝ) (r : ℝ) : ℝ :=
  Classical.epsilon (fun t=>t ∈ transversePeaks a ∧ axisWidth a t=r)
lemma axisPeak_spec (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    axisPeak a r ∈ transversePeaks a ∧ axisWidth a (axisPeak a r)=r :=
  Classical.epsilon_spec hr
lemma axisPeak_eq (a : Fin 6 → ℝ) {r t : ℝ} (ht : t ∈ transversePeaks a) (he : axisWidth a t=r) :
    axisPeak a r=t := by
  have hs := axisPeak_spec a (mem_image_of_mem (axisWidth a) ht)
  rw [he] at hs
  exact (axisWidth_strictMono a).injOn hs.1 ht (hs.2.trans he.symm)
noncomputable def axisM (a : Fin 6 → ℝ) (r : ℝ) : ℝ := axisCenter a (axisPeak a r)
lemma axisM_abs_lt (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) : 0<r ∧ |axisM a r|<r := by
  have ht := axisPeak_spec a hr
  constructor
  · rw [←ht.2]; exact (axisWidth_pos_deriv a ht.1).1
  · exact (axisWidth_pos_deriv a ht.1).2.2.1.trans_eq ht.2

theorem width_germ (a : Fin 6 → ℝ) {t : ℝ} (ht : t ∈ transversePeaks a) :
    ∃ Y G : ℝ×ℝ → ℝ,
      ContDiffAt ℝ ω Y (0,axisWidth a t) ∧ ContDiffAt ℝ ω G (0,axisWidth a t) ∧
      Y (0,axisWidth a t)=t ∧ G (0,axisWidth a t)=axisCenter a t ∧
      (∀ᶠ r in 𝓝 (axisWidth a t), r ∈ axisWidths a ∧ Y (0,r)=axisPeak a r ∧ G (0,r)=axisM a r) ∧
      (∀ᶠ q in 𝓝 ((0:ℝ),axisWidth a t), 0<q.1 →
        Y q=peakAtWidth (QuinticProfile.profile a) ((0,q.1^2/2),q.2) ∧
        G q=QuinticFit.M a (q.1^2/2,q.2)) := by
  obtain ⟨l,hla,hl0,hle,_⟩ := endpoint_germ a false ht.1 ht.2.1.ne
  obtain ⟨b,hba,hb0,hbe,_⟩ := endpoint_germ a true ht.1 ht.2.2.ne'
  have hle0 := endpoint_germ_eq ht.1 hla hle
  have hbe0 := endpoint_germ_eq ht.1 hba hbe
  let W : ℝ×ℝ → ℝ := fun q=>(b (q.2,q.1)-l (q.2,q.1))/2
  have hWa : ContDiffAt ℝ ω W (0,t) := ((hba.sub hla).div_const 2).comp (0,t)
    (contDiffAt_snd.prodMk contDiffAt_fst)
  have hW0 : W (0,t)=axisWidth a t := by dsimp [W,axisWidth]; rw [hl0,hb0]
  have hWslice : (fun s=>W (0,s)) =ᶠ[𝓝 t] axisWidth a := by
    filter_upwards [hle0,hbe0] with s hls hbs
    simp only [W,axisWidth,hls,hbs]
  have hWd : HasDerivAt (fun s=>W (0,s)) (deriv (axisWidth a) t) t :=
    ((axisWidth_analytic a ht).differentiableAt (by simp)).hasDerivAt.congr_of_eventuallyEq hWslice
  obtain ⟨Y,hY,hY0,hYe⟩ := ArcEndpoints.level_hit hWa hWd hW0 (axisWidth_pos_deriv a ht).2.1.ne'
  let G : ℝ×ℝ → ℝ := fun q=>(b (Y q,q.1)+l (Y q,q.1))/2-poly a q.1
  have hYa : ContDiffAt ℝ ω (fun q=>(Y q,q.1)) (0,axisWidth a t) := hY.prodMk contDiffAt_fst
  have hGa : ContDiffAt ℝ ω G (0,axisWidth a t) := by
    have hh : ContDiffAt ℝ ω (fun q=>(b q+l q)/2) (t,0) := (hba.add hla).div_const 2
    have hc : ContDiffAt ℝ ω (fun q : ℝ×ℝ=>poly a q.1) (0,axisWidth a t) := by unfold poly; fun_prop
    exact (show ContDiffAt ℝ ω (fun q=>(b (Y q,q.1)+l (Y q,q.1))/2) (0,axisWidth a t) from
      (by
        have hh' : ContDiffAt ℝ ω (fun q=>(b q+l q)/2) (Y (0,axisWidth a t),0) := by rw [hY0]; exact hh
        exact hh'.comp (f:=fun q : ℝ×ℝ=>(Y q,q.1)) (0,axisWidth a t) hYa)).sub hc
  have hG0 : G (0,axisWidth a t)=axisCenter a t := by dsimp [G,axisCenter]; rw [hY0,hl0,hb0]
  have hYlim : ContinuousAt (fun r=>Y (0,r)) (axisWidth a t) :=
    hY.continuousAt.comp (f:=fun r : ℝ=>(0,r)) (continuousAt_const.prodMk continuousAt_id)
  have hYt : Tendsto (fun r=>Y (0,r)) (𝓝 (axisWidth a t)) (𝓝 t) := by simpa only [hY0] using hYlim.tendsto
  have hYtrans : ∀ᶠ r in 𝓝 (axisWidth a t), Y (0,r) ∈ transversePeaks a :=
    hYlim.eventually ((transversePeaks_open a).mem_nhds (by simpa only [hY0] using ht))
  have hslice : ∀ᶠ r in 𝓝 (axisWidth a t), r ∈ axisWidths a ∧ Y (0,r)=axisPeak a r ∧ G (0,r)=axisM a r := by
    have hNb : ∀ᶠ r in 𝓝 (axisWidth a t), b (Y (0,r),0)=axisEndpoint a true (Y (0,r)) := hYt.eventually hbe0
    have hNl : ∀ᶠ r in 𝓝 (axisWidth a t), l (Y (0,r),0)=axisEndpoint a false (Y (0,r)) := hYt.eventually hle0
    filter_upwards [hYtrans,(continuousAt_const.prodMk continuousAt_id).eventually hYe,hNb,hNl] with r htr he hb hl
    have hwr : axisWidth a (Y (0,r))=r := by simpa only [W,axisWidth,id_eq,hb,hl] using he
    have hpeak := (axisPeak_eq a htr hwr).symm
    refine ⟨⟨Y (0,r),htr,hwr⟩,hpeak,?_⟩
    dsimp only [G,axisM,axisCenter]
    rw [hb,hl,hpeak]
  have hposr : 0<axisWidth a t := (axisWidth_pos_deriv a ht).1
  have hheight : ∀ᶠ q in 𝓝 ((0:ℝ),axisWidth a t), q.1^2/2<Y q :=
    ((continuousAt_fst.pow 2).div_const 2).eventually_lt hY.continuousAt (by simpa only [Pi.pow_apply,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,hY0] using ht.1)
  have hposEq : ∀ᶠ q in 𝓝 ((0:ℝ),axisWidth a t), 0<q.1 →
      Y q=peakAtWidth (QuinticProfile.profile a) ((0,q.1^2/2),q.2) ∧
      G q=QuinticFit.M a (q.1^2/2,q.2) := by
    have hNl := hYa.continuousAt.eventually (by simpa only [hY0] using hle)
    have hNb := hYa.continuousAt.eventually (by simpa only [hY0] using hbe)
    filter_upwards [hYe,hNl,hNb,hheight,continuousAt_snd.eventually (eventually_gt_nhds hposr)] with q hq hl hb hh hr hx
    have hh0 : 0<q.1^2/2 := div_pos (sq_pos_of_pos hx) (by norm_num)
    have hwr : widthFamily (QuinticProfile.profile a) (((0:ℝ),Y q),q.1^2/2)=q.2 := by
      have he := hq
      simp only [W,hb hx,hl hx,branch,endpoint,Bool.false_eq_true,↓reduceIte] at he
      exact he
    have hp := peak_eq (QuinticProfile.profile a) (fun _ h=>QuinticProfile.analytic a h)
      (QuinticProfile.local_flow a) hr hh0 hh hwr
    refine ⟨hp.symm,?_⟩
    dsimp only [G,QuinticFit.M,PositiveTransport.M,midpointAtWidth,midpointFamily]
    rw [hp]
    rw [hb hx,hl hx]
    change (endpoint a true (q.1^2/2) (Y q)+endpoint a false (q.1^2/2) (Y q))/2-poly a q.1=
      ScalarArcs.midpoint (φ a) (q.1^2/2) (Y q)
    dsimp only [ScalarArcs.midpoint]
    rw [φ_square a hx.le]
    rfl
  exact ⟨Y,G,hY,hGa,hY0,hG0,hslice,hposEq⟩
end QuinticLienard.AxisFlow

end OAI
