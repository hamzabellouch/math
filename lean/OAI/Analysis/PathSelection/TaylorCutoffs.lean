import Mathlib
import OAI.Analysis.PathSelection.ClockAlgebra

namespace OAI

/-! Uniform Taylor cutoffs, compact family holomorphy and moving Taylor polynomials. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Filter Topology Complex Metric
open scoped BigOperators
namespace DegeneratingTrees.TaylorCutoff
variable {E : Type*} [NormedAddCommGroup E]

private def extend {r : ℝ} (f : C(sphere (0 : ℂ) r,E)) (z : ℂ) : E := by
  classical
  exact if hz : z ∈ sphere (0 : ℂ) r then f ⟨z,hz⟩ else 0

private lemma extend_on {r : ℝ} (f : C(sphere (0 : ℂ) r,E))
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) r) : extend f z = f ⟨z,hz⟩ := by
  simp only [extend,dite_eq_left hz]

private lemma extend_continuousOn {r : ℝ} (f : C(sphere (0 : ℂ) r,E)) :
    ContinuousOn (extend f) (sphere (0 : ℂ) r) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert f.continuous using 1
  ext z
  exact extend_on f z.property

 
variable [NormedSpace ℂ E]

def circleMap (r : ℝ) (hr : 0 ≤ r) : C(sphere (0 : ℂ) r,E) →L[ℂ] E :=
  let L : C(sphere (0 : ℂ) r,E) →ₗ[ℂ] E :=
    { toFun := fun f => ∮ z in C(0,r), extend f z
      map_add' := by
        intro f g
        have he : extend (f+g) = fun z => extend f z + extend g z := by
          ext z
          by_cases hz : z ∈ sphere (0 : ℂ) r <;>
            simp only [extend,hz,dite_true,dite_false,ContinuousMap.add_apply,add_zero]
        rw [he]
        exact circleIntegral.integral_add
          ((extend_continuousOn f).circleIntegrable hr)
          ((extend_continuousOn g).circleIntegrable hr)
      map_smul' := by
        intro c f
        have he : extend (c • f) = fun z => c • extend f z := by
          ext z
          by_cases hz : z ∈ sphere (0 : ℂ) r <;>
            simp only [extend,hz,dite_true,dite_false,ContinuousMap.smul_apply,smul_zero]
        rw [he,circleIntegral.integral_smul]
        rfl }
  L.mkContinuous (2*Real.pi*r) (by
    intro f
    apply circleIntegral.norm_integral_le_of_norm_le_const hr
    intro z hz
    rw [extend_on f hz]
    exact f.norm_coe_le_norm ⟨z,hz⟩)

lemma circleMap_eq {r : ℝ} (hr : 0 ≤ r) (f : C(sphere (0 : ℂ) r,E))
    (F : ℂ → E) (hF : ∀ z : sphere (0 : ℂ) r, f z = F z) :
    circleMap r hr f = ∮ z in C(0,r), F z := by
  apply circleIntegral.integral_congr hr
  intro z hz
  rw [extend_on f hz]
  exact hF ⟨z,hz⟩

lemma sphere_ne_zero {r : ℝ} (hr : 0 < r) (w : sphere (0:ℂ) r) : (w:ℂ) ≠ 0 := by
  intro he
  have hw : ‖(w:ℂ)‖ = r := by simpa only [mem_sphere,dist_zero_right] using w.property
  rw [he,norm_zero] at hw
  exact hr.ne' hw.symm

lemma sphere_sub_ball_ne_zero {r : ℝ} (w : sphere (0:ℂ) r) (u : ball (0:ℂ) r) :
    (w:ℂ)-(u:ℂ) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro he
  have hw : ‖(w:ℂ)‖ = r := by simpa only [mem_sphere,dist_zero_right] using w.property
  have hu : ‖(u:ℂ)‖ < r := by simpa only [mem_ball,dist_zero_right] using u.property
  rw [he] at hw
  exact (ne_of_lt hu) hw

 
def tailProfile {r : ℝ} (hr : 0 < r) (n : ℕ)
    (f : C(sphere (0:ℂ) r,E)) (u : ball (0:ℂ) r) : C(sphere (0:ℂ) r,E) :=
  ⟨fun w => ((w:ℂ)^n*((w:ℂ)-(u:ℂ)))⁻¹ • f w,
    ((continuous_subtype_val.pow n).mul
      (continuous_subtype_val.sub continuous_const)).inv₀
        (fun w => mul_ne_zero (pow_ne_zero _ (sphere_ne_zero hr w))
          (sphere_sub_ball_ne_zero w u)) |>.smul f.continuous⟩

def tail {r : ℝ} (hr : 0 < r) (n : ℕ)
    (f : C(sphere (0:ℂ) r,E)) (u : ball (0:ℂ) r) : E :=
  (2*Real.pi*I : ℂ)⁻¹ • circleMap r hr.le (tailProfile hr n f u)

lemma continuous_tailProfile {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Continuous (fun x : C(sphere (0:ℂ) r,E) × ball (0:ℂ) r =>
      tailProfile hr n x.1 x.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun x : (C(sphere (0:ℂ) r,E) × ball (0:ℂ) r) × sphere (0:ℂ) r =>
    ((x.2:ℂ)^n*((x.2:ℂ)-(x.1.2:ℂ)))⁻¹ • x.1.1 x.2)
  apply Continuous.smul
  · apply Continuous.inv₀
    · fun_prop
    · intro x
      exact mul_ne_zero (pow_ne_zero _ (sphere_ne_zero hr x.2))
        (sphere_sub_ball_ne_zero x.2 x.1.2)
  · exact continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd)

lemma continuous_tail {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Continuous (fun x : C(sphere (0:ℂ) r,E) × ball (0:ℂ) r => tail hr n x.1 x.2) :=
  continuous_const.smul ((circleMap r hr.le).continuous.comp (continuous_tailProfile hr n))

attribute [local irreducible] tail tailProfile circleMap

 

theorem tail_tendsto {α : Type*} {l : Filter α} {r : ℝ} (hr : 0 < r)
    (n : ℕ) {f : α → C(sphere (0:ℂ) r,E)} {f₀ : C(sphere (0:ℂ) r,E)}
    {u : α → ball (0:ℂ) r} {u₀ : ball (0:ℂ) r}
    (hf : Tendsto f l (𝓝 f₀)) (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun x => tail hr n (f x) (u x)) l
      (𝓝 (tail hr n f₀ u₀)) := by
  have ht : Tendsto (fun x : C(sphere (0:ℂ) r,E) × ball (0:ℂ) r =>
      tail hr n x.1 x.2) (𝓝 (f₀,u₀)) (𝓝 (tail hr n f₀ u₀)) :=
    (continuous_tail (E := E) hr n).tendsto (f₀,u₀)
  have hp : Tendsto (fun x => (f x,u x)) l (𝓝 (f₀,u₀)) := hf.prodMk_nhds hu
  exact ht.comp hp

theorem tail_tendsto_zero {α : Type*} {l : Filter α} {r : ℝ} (hr : 0 < r)
    (n : ℕ) {f : α → C(sphere (0:ℂ) r,E)} {f₀ : C(sphere (0:ℂ) r,E)}
    {u : α → ball (0:ℂ) r} (hf : Tendsto f l (𝓝 f₀))
    (hu : Tendsto (fun x => (u x:ℂ)) l (𝓝 0)) :
    Tendsto (fun x => tail hr n (f x) (u x)) l
      (𝓝 (tail hr n f₀ ⟨0,by simpa only [mem_ball,dist_self] using hr⟩)) := by
  apply tail_tendsto hr n hf
  exact tendsto_subtype_rng.mpr hu

lemma tail_kernel_step {w u : ℂ} (hw : w ≠ 0) (hwu : w-u ≠ 0) (n : ℕ) :
    (w^n*(w-u))⁻¹ = (w^(n+1))⁻¹ + u*(w^(n+1)*(w-u))⁻¹ := by
  field_simp
  ring

lemma tail_step {r : ℝ} (hr : 0 < r) (n : ℕ)
    (f : C(sphere (0:ℂ) r,E)) (u : ball (0:ℂ) r) :
    tail hr n f u = tail hr n f ⟨0,by simpa using hr⟩ +
      (u:ℂ) • tail hr (n+1) f u := by
  have he : tailProfile hr n f u =
      tailProfile hr n f ⟨0,by simpa using hr⟩ + (u:ℂ) • tailProfile hr (n+1) f u := by
    ext w
    simpa only [tailProfile,ContinuousMap.coe_mk,ContinuousMap.add_apply,
      ContinuousMap.smul_apply,sub_zero,pow_succ,add_smul,mul_smul] using
      congrArg (fun z : ℂ => z • f w)
        (tail_kernel_step (sphere_ne_zero hr w) (sphere_sub_ball_ne_zero w u) n)
  simp only [tail,he,map_add,map_smul,smul_add,smul_comm (u:ℂ)]

 

theorem finite_cutoff {r : ℝ} (hr : 0 < r) (n : ℕ)
    (f : C(sphere (0:ℂ) r,E)) (u : ball (0:ℂ) r) :
    tail hr 0 f u = (∑ k ∈ Finset.range n, (u:ℂ)^k •
      tail hr k f ⟨0,by simpa using hr⟩) + (u:ℂ)^n • tail hr n f u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih,tail_step hr n f u,smul_add,Finset.sum_range_succ,pow_succ,
        mul_smul]
      module

variable [CompleteSpace E]

lemma tail_zero_eq {r : ℝ} (hr : 0 < r) {F : ℂ → E}
    (hF : DifferentiableOn ℂ F (closedBall 0 r)) (u : ball (0:ℂ) r) :
    tail hr 0 ⟨fun w => F w,hF.continuousOn.mono sphere_subset_closedBall
      |>.domRestrict⟩ u = F u := by
  unfold tail
  rw [circleMap_eq hr.le _ (fun w => (w-(u:ℂ))⁻¹ • F w) (by intro w; simp only [tailProfile,ContinuousMap.coe_mk,pow_zero,one_mul]; rfl)]
  rw [hF.circleIntegral_sub_inv_smul u.property]
  rw [smul_smul,inv_mul_cancel₀]
  · exact one_smul ℂ _
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero

end DegeneratingTrees.TaylorCutoff

 

 

 

open Set Filter Topology Complex MeasureTheory Metric
open scoped NNReal
namespace DegeneratingTrees.Clock

lemma clm_circleIntegral {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    (L : V →L[ℂ] W) {f : ℂ → V} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    (∮ z in C(c,r),L (f z)) = L (∮ z in C(c,r),f z) := by
  simpa only [circleIntegral,map_smul] using
    L.intervalIntegral_comp_comm ((circleIntegrable_iff r).mp hf)

lemma compact_family_analyticAt {S : Type*} [TopologicalSpace S] [CompactSpace S]
    {F : ℂ → C(S,ℂ)} {c : ℂ} {r : ℝ≥0} (hr : 0<r)
    (hc : ContinuousOn F (closedBall c r))
    (ha : ∀ s : S,DiffContOnCl ℂ (fun z => F z s) (ball c r)) :
    AnalyticAt ℂ F c := by
  let G : ℂ → C(S,ℂ) := fun w => (2*Real.pi*I:ℂ)⁻¹ •
    ∮ z in C(c,r),(z-w)⁻¹ • F z
  have hGa : AnalyticAt ℂ G c :=
    (hasFPowerSeriesOn_cauchy_integral
      ((hc.mono sphere_subset_closedBall).circleIntegrable r.2) hr).analyticAt
  apply hGa.congr
  filter_upwards [ball_mem_nhds c hr] with w hw
  apply ContinuousMap.ext
  intro s
  let L : C(S,ℂ) →L[ℂ] ℂ := ContinuousMap.evalCLM ℂ s
  have hkernel : ContinuousOn (fun z : ℂ => (z-w)⁻¹ • F z) (sphere c r) := by
    have hi : ContinuousOn (fun z : ℂ => (z-w)⁻¹) (sphere c r) := by
      apply ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
      intro z hz he
      have : z=w := sub_eq_zero.mp he
      subst z
      have : dist w c=(r:ℝ) := mem_sphere.mp hz
      exact (ne_of_lt (mem_ball.mp hw)) this
    exact hi.smul (hc.mono sphere_subset_closedBall)
  have hcomm := clm_circleIntegral L (hkernel.circleIntegrable r.2)
  change L (G w)=F w s
  dsimp only [G]
  rw [map_smul]
  calc
    _ = (2*Real.pi*I:ℂ)⁻¹ • (∮ z in C(c,r),L ((z-w)⁻¹ • F z)) :=
      congrArg (fun x : ℂ => (2*Real.pi*I:ℂ)⁻¹ • x) hcomm.symm
    _ = F w s := by
      simpa only [map_smul,ContinuousMap.evalCLM_apply,L] using
        (ha s).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw

lemma compact_family_analyticAt_of_joint {S : Type*} [TopologicalSpace S] [CompactSpace S]
    {F : ℂ → C(S,ℂ)} {c : ℂ} {r : ℝ≥0} (hr : 0<r)
    (hc : ContinuousOn (fun p : ℂ × S => F p.1 p.2) (closedBall c r ×ˢ univ))
    (ha : ∀ s : S,DiffContOnCl ℂ (fun z => F z s) (ball c r)) :
    AnalyticAt ℂ F c :=
  compact_family_analyticAt hr (ContinuousMap.continuousOn_of_continuousOn_uncurry F hc) ha

end DegeneratingTrees.Clock

 

 

 

open Set Filter Topology Complex Metric
namespace DegeneratingTrees.TaylorCutoff
attribute [local irreducible] tail tailProfile circleMap

 
def scalarTailCLM {r : ℝ} (hr : 0<r) (n : ℕ) (u : ball (0:ℂ) r) :
    C(sphere (0:ℂ) r,ℂ) →L[ℂ] ℂ where
  toFun := fun f => tail hr n f u
  map_add' := by
    intro f g
    have he : tailProfile hr n (f+g) u = tailProfile hr n f u+tailProfile hr n g u := by
      ext w
      simp only [tailProfile,ContinuousMap.coe_mk,ContinuousMap.add_apply,smul_add]
    simp only [tail,he,map_add,smul_add]
  map_smul' := by
    intro c f
    have he : tailProfile hr n (c • f) u = c • tailProfile hr n f u := by
      ext w
      simp only [tailProfile,ContinuousMap.coe_mk,ContinuousMap.smul_apply,smul_comm c]
    simp only [tail,he,map_smul,smul_comm c,RingHom.id_apply]
  cont := by
    exact (continuous_tail (E := ℂ) hr n).comp (continuous_id.prodMk continuous_const)

def shiftedBoundary (G : C(ℂ,ℂ)) (r : ℝ) (a : ℂ) : C(sphere (0:ℂ) r,ℂ) :=
  ⟨fun w => G (a+w),G.continuous.comp (continuous_const.add continuous_subtype_val)⟩

lemma continuous_shiftedBoundary (G : C(ℂ,ℂ)) (r : ℝ) : Continuous (shiftedBoundary G r) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact G.continuous.comp (continuous_fst.add (continuous_subtype_val.comp continuous_snd))

lemma shift_mem_disc {d a w : ℂ} {r : ℝ} (hr : 0<r)
    (ha : a∈closedBall d r) (hw : w∈closedBall (0:ℂ) r) :
    a+w∈ball d (3*r) := by
  rw [mem_ball,dist_eq_norm]
  have h : ‖(a-d)+w‖ ≤ 2*r := by
    calc
      _ ≤ ‖a-d‖+‖w‖ := norm_add_le _ _
      _ ≤ r+r := add_le_add (by simpa only [mem_closedBall,dist_eq_norm] using ha)
        (by simpa only [mem_closedBall,dist_zero_right] using hw)
      _ = _ := by ring
  have he : a+w-d=(a-d)+w := by ring
  rw [he]
  linarith

lemma shiftedBoundary_analyticAt {G : C(ℂ,ℂ)} {d : ℂ} {r : ℝ} (hr : 0<r)
    (hG : AnalyticOnNhd ℂ G (ball d (3*r))) :
    AnalyticAt ℂ (shiftedBoundary G r) d := by
  have ha : ∀ w : sphere (0:ℂ) r,
      AnalyticOnNhd ℂ (fun a => G (a+w)) (closedBall d r) := by
    intro w a ha
    exact (hG _ (shift_mem_disc hr ha (sphere_subset_closedBall w.property))).comp
      (f := fun a : ℂ => a+(w:ℂ)) (analyticAt_id.add analyticAt_const)
  apply Clock.compact_family_analyticAt (r := ⟨r,hr.le⟩) hr
    (continuous_shiftedBoundary G r).continuousOn
  intro w
  change DiffContOnCl ℂ (fun a => G (a+(w:ℂ))) (ball d r)
  refine ⟨((ha w).differentiableOn.mono ball_subset_closedBall),?_⟩
  simpa only [closure_ball _ hr.ne'] using (ha w).continuousOn

lemma local_continuous_extension {g : ℂ → ℂ} {d : ℂ} (hg : AnalyticAt ℂ g d) :
    ∃ (G : C(ℂ,ℂ)) (r : ℝ),0<r ∧
      AnalyticOnNhd ℂ G (ball d (3*r)) ∧ EqOn G g (closedBall d (3*r)) := by
  obtain ⟨R,hR,hgR⟩ := hg.exists_ball_analyticOnNhd
  let r : ℝ := R/4
  have hr : 0<r := by dsimp [r]; positivity
  have hsub : closedBall d (3*r) ⊆ ball d R := by
    intro z hz
    have hz := mem_closedBall.mp hz
    rw [mem_ball]
    dsimp [r] at *
    linarith
  let gC : C(closedBall d (3*r),ℂ) :=
    ⟨fun z => g z,(hgR.continuousOn.mono hsub).domRestrict⟩
  obtain ⟨G,hG⟩ := gC.exists_restrict_eq isClosed_closedBall
  have he : EqOn G g (closedBall d (3*r)) := by
    intro z hz
    exact DFunLike.congr_fun hG ⟨z,hz⟩
  refine ⟨G,r,hr,?_,he⟩
  intro z hz
  apply (hgR z (hsub (ball_subset_closedBall hz))).congr
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact (he (ball_subset_closedBall hw)).symm

 

theorem analytic_moving_taylor {g : ℂ → ℂ} {d : ℂ} (hg : AnalyticAt ℂ g d) :
    ∃ c : ℕ → ℂ → ℂ,(∀ n,AnalyticAt ℂ (c n) d) ∧
      ∀ (a f : ℂ → ℂ) (δ : ℝ),Tendsto a sectorInfinity (𝓝 d) →
        0<δ → Clock.ExpBound (-δ) f → ∀ N : ℕ,
        Clock.ExpBound (-δ*(N:ℝ)) (fun z => g (a z+f z)-
          ∑ n ∈ Finset.range N,c n (a z)*f z^n) := by
  classical
  obtain ⟨G,r,hr,hG,heG⟩ := local_continuous_extension hg
  let u₀ : ball (0:ℂ) r := ⟨0,by simpa using hr⟩
  let c : ℕ → ℂ → ℂ := fun n a => scalarTailCLM hr n u₀ (shiftedBoundary G r a)
  have hc : ∀ n,AnalyticAt ℂ (c n) d := by
    intro n
    exact ((scalarTailCLM hr n u₀).analyticAt _).comp (shiftedBoundary_analyticAt hr hG)
  refine ⟨c,hc,?_⟩
  intro a f δ ha hδ hf N
  have hft := hf.tendsto_zero (neg_neg_of_pos hδ)
  let u : ℂ → ball (0:ℂ) r := fun z =>
    if hz : f z∈ball (0:ℂ) r then ⟨f z,hz⟩ else u₀
  have hue : (fun z => (u z:ℂ)) =ᶠ[sectorInfinity] f := by
    filter_upwards [hft.eventually (ball_mem_nhds (0:ℂ) hr)] with z hz
    dsimp only [u]
    split_ifs with h
    · rfl
    · exact False.elim (h hz)
  have hut : Tendsto (fun z => (u z:ℂ)) sectorInfinity (𝓝 0) :=
    hft.congr' hue.symm
  have hboundary := (continuous_shiftedBoundary G r).continuousAt.tendsto.comp ha
  have htail := tail_tendsto_zero hr N hboundary hut
  have hbound := (hf.pow N).mul (Clock.ExpBound.of_tendsto htail)
  simp only [add_zero] at hbound
  apply hbound.congr
  filter_upwards [hue,ha.eventually (ball_mem_nhds d hr)] with z hz hza
  have hdiff : DifferentiableOn ℂ (fun w => G (a z+w)) (closedBall (0:ℂ) r) := by
    intro w hw
    exact ((hG _ (shift_mem_disc hr (ball_subset_closedBall hza) hw)).differentiableAt.comp w
      ((differentiableAt_const (a z)).add differentiableAt_id)).differentiableWithinAt
  have htail₀ : tail hr 0 (shiftedBoundary G r (a z)) (u z) = G (a z+f z) := by
    have h := tail_zero_eq hr hdiff (u z)
    rw [hz] at h
    exact h
  have hcut := finite_cutoff hr N (shiftedBoundary G r (a z)) (u z)
  rw [htail₀] at hcut
  have hazf : a z+f z∈closedBall d (3*r) := by
    apply ball_subset_closedBall
    apply shift_mem_disc hr (ball_subset_closedBall hza)
    rw [←hz]
    exact ball_subset_closedBall (u z).property
  rw [heG hazf] at hcut
  simp only [hz,smul_eq_mul] at hcut
  change f z^N*tail hr N (shiftedBoundary G r (a z)) (u z) = _
  change _ = g (a z+f z)-∑ n ∈ Finset.range N,
      tail hr n (shiftedBoundary G r (a z)) u₀*f z^n
  simp_rw [mul_comm (tail hr _ _ _)]
  exact (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hcut.symm))

end DegeneratingTrees.TaylorCutoff
end

end OAI
