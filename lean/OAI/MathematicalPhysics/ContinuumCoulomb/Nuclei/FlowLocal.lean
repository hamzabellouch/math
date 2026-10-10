import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.FlowPathFamily
import OAI.Analysis.BiholderTransport.LocalFlow.SmoothFlowEndpoint

namespace OAI

/-! A genuine C⁴ local flow for the four-dimensional autonomous lift. The
path family is identified with its ODE by the proved rescaling uniqueness. -/

noncomputable section
open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace ContinuumCoulomb
open WeakMTWTransport

private theorem flow_endpoint_deriv_zero (f : C(FlowPhase,FlowPhase))
    (hf : ContDiff ℝ 4 f) (U : (ℝ × FlowPhase) → FlowPath) (x : FlowPhase)
    (hU : ContDiffAt ℝ 4 U (0,x))
    (hEq : ∀ᶠ z in 𝓝 ((0:ℝ),x), U z = ContinuousMap.const UnitTime z.2+
      z.1 • unitPathIntegral (f.comp (U z))) :
    HasDerivAt (fun t => U (t,x) ⟨1,by simp⟩) (f x) 0 := by
  let e : UnitTime := ⟨1,by simp⟩
  let W : ℝ → FlowPhase := fun t => unitPathIntegral (f.comp (U (t,x))) e
  have hW : ContDiffAt ℝ 4 W 0 :=
    (ContinuousMap.evalCLM ℝ e).contDiff.contDiffAt.comp 0
      (unitPathIntegral.contDiff.contDiffAt.comp 0
        ((contDiff_path_comp_nat 4 f hf).contDiffAt.comp 0
          (hU.comp 0 (contDiffAt_id.prodMk contDiffAt_const))))
  have hUx : U (0,x) = ContinuousMap.const UnitTime x := ode_family_initial hEq.self_of_nhds
  have hW0 : W 0 = f x := by
    simp [W,unitPathIntegral_apply,hUx,extendUnitPath,ContinuousMap.comp_apply,e]
  have heq : (fun t : ℝ => U (t,x) e) =ᶠ[𝓝 0] (fun t => x+t • W t) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hEq] with t ht
    exact congrArg (fun u : FlowPath => u e) ht
  have hd := ((hasDerivAt_id (0:ℝ)).smul
    (hW.differentiableAt (by norm_num)).hasDerivAt).const_add x
  change HasDerivAt (fun t => x+t • W t) ((0:ℝ) • deriv W 0+(1:ℝ) • W 0) 0 at hd
  have hd' : HasDerivAt (fun t => x+t • W t) (f x) 0 := by
    simpa only [id_eq,Pi.smul_apply,one_smul,zero_smul,add_zero,zero_add,hW0] using hd
  exact hd'.congr_of_eventuallyEq heq

theorem flow_c4_local (f : FlowPhase → FlowPhase) (hf : ContDiff ℝ 4 f) (a : FlowPhase) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : (ℝ × FlowPhase) → FlowPhase,
      ContDiffOn ℝ 4 Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨U,S,hS,ha,hU,hUa,hEq⟩ := flow_c4_rescaled_family f hf a
  let fC : C(FlowPhase,FlowPhase) := ⟨f,hf.continuous⟩
  obtain ⟨K,B,hBa,hLip⟩ := (hf.contDiffAt.of_le (by norm_num : (1:ℕ∞ω) ≤ 4)).exists_lipschitzOnWith
  obtain ⟨b,hb,hbB⟩ := Metric.mem_nhds_iff.mp hBa
  have hcont : ContinuousAt U (0,a) := (hU.contDiffAt (hS.mem_nhds ha)).continuousAt
  have hn : ∀ᶠ z in 𝓝 ((0:ℝ),a), z ∈ S ∧ dist (U z) (ContinuousMap.const UnitTime a) < b := by
    have h := hcont.eventually (Metric.ball_mem_nhds (U (0,a)) hb)
    rw [hUa] at h
    exact (show ∀ᶠ z in 𝓝 ((0:ℝ),a), z ∈ S from hS.mem_nhds ha).and h
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hn
  let R := Metric.ball ((0:ℝ),a) ε
  have hRS : R ⊆ S := fun z hz => (hεsub hz).1
  have hRB : ∀ z ∈ R, ∀ s, U z s ∈ B := by
    intro z hz s
    apply hbB
    exact lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := U z)
      (g := ContinuousMap.const UnitTime a) s) (hεsub hz).2
  let r := ε/3
  have hr : 0 < r := div_pos hε (by norm_num)
  have htr : ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r, (t,x) ∈ R ∧ (2*t,x) ∈ R := by
    intro t ht x hx
    have habs : |t| < r := abs_lt.mpr ht
    have hx' : dist x a < r := hx
    have hre : r < ε := by dsimp [r]; linarith
    have ht2 : |2*t| < ε := by
      rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      dsimp [r] at habs
      linarith
    constructor
    · change dist (t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨habs.trans hre,hx'.trans hre⟩
    · change dist (2*t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨ht2,hx'.trans hre⟩
  let Φ : (ℝ × FlowPhase) → FlowPhase := fun z => U z ⟨1,by simp⟩
  refine ⟨r,hr,Φ,?_,?_,?_⟩
  · have hUSub : ContDiffOn ℝ 4 U (Ioo (-r) r ×ˢ Metric.ball a r) :=
      hU.mono (fun z hz => hRS (htr z.1 hz.1 z.2 hz.2).1)
    exact (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : UnitTime)).contDiff.comp_contDiffOn hUSub
  · intro x hx
    have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_neg_of_pos hr,hr⟩
    have hi := ode_family_initial (hEq (0,x) (hRS (htr 0 h0 x hx).1))
    exact congrArg (fun u : FlowPath => u ⟨1,by simp⟩) hi
  · intro t ht x hx
    by_cases ht0 : t = 0
    · subst t
      have hi : Φ (0,x) = x := congrArg (fun u : FlowPath => u ⟨1,by simp⟩)
        (ode_family_initial (hEq (0,x) (hRS (htr 0 ht x hx).1)))
      rw [hi]
      exact flow_endpoint_deriv_zero fC hf U x
        (hU.contDiffAt (hS.mem_nhds (hRS (htr 0 ht x hx).1)))
        (Filter.eventually_of_mem (hS.mem_nhds (hRS (htr 0 ht x hx).1)) hEq)
    · exact ode_family_endpoint_deriv_ne_zero fC U R Metric.isOpen_ball
        (fun z hz => hEq z (hRS hz)) K B hLip hRB t x ht0
        (htr t ht x hx).1 (htr t ht x hx).2

end ContinuumCoulomb

end

end OAI
