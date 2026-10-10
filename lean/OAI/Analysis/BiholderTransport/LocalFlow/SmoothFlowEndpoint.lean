import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.ImplicitODE

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma ode_family_initial {f : C(E,E)} {U : (ℝ × E) → C(UnitTime,E)} {x : E}
    (h : U (0,x) = ContinuousMap.const UnitTime x +
      (0:ℝ) • unitPathIntegral (f.comp (U (0,x)))) :
    U (0,x) = ContinuousMap.const UnitTime x := by simpa using h

lemma ode_family_endpoint_deriv_zero (f : C(E,E)) (hf : ContDiff ℝ ∞ f)
    (U : (ℝ × E) → C(UnitTime,E)) (x : E)
    (hU : ContDiffAt ℝ ∞ U (0,x))
    (hEq : ∀ᶠ z in 𝓝 ((0:ℝ),x), U z = ContinuousMap.const UnitTime z.2 +
      z.1 • unitPathIntegral (f.comp (U z))) :
    HasDerivAt (fun t => U (t,x) ⟨1,by simp⟩) (f x) 0 := by
  let e : UnitTime := ⟨1,by simp⟩
  let W : ℝ → E := fun t => unitPathIntegral (f.comp (U (t,x))) e
  have hW : ContDiffAt ℝ ∞ W 0 :=
    (ContinuousMap.evalCLM ℝ e).contDiff.contDiffAt.comp 0
      (unitPathIntegral.contDiff.contDiffAt.comp 0
        ((contDiff_path_comp f hf).contDiffAt.comp 0
          (hU.comp 0 (contDiffAt_id.prodMk contDiffAt_const))))
  have hUx : U (0,x) = ContinuousMap.const UnitTime x := ode_family_initial hEq.self_of_nhds
  have hW0 : W 0 = f x := by
    simp [W,unitPathIntegral_apply,hUx,extendUnitPath,ContinuousMap.comp_apply,e]
  have heq : (fun t : ℝ => U (t,x) e) =ᶠ[𝓝 0] (fun t => x + t • W t) := by
    filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually hEq] with t ht
    exact congrArg (fun u : C(UnitTime,E) => u e) ht
  have hd := ((hasDerivAt_id (0:ℝ)).smul (hW.differentiableAt (by simp)).hasDerivAt).const_add x
  change HasDerivAt (fun t => x + t • W t)
    ((0:ℝ) • deriv W 0 + (1:ℝ) • W 0) 0 at hd
  have hd' : HasDerivAt (fun t => x + t • W t) (f x) 0 := by
    simpa only [id_eq,Pi.smul_apply,one_smul,zero_smul,add_zero,zero_add,hW0] using hd
  exact hd'.congr_of_eventuallyEq heq

lemma ode_family_endpoint_deriv_ne_zero (f : C(E,E))
    (U : (ℝ × E) → C(UnitTime,E)) (S : Set (ℝ × E)) (hS : IsOpen S)
    (hEq : ∀ z ∈ S, U z = ContinuousMap.const UnitTime z.2 +
      z.1 • unitPathIntegral (f.comp (U z)))
    (K : ℝ≥0) (B : Set E) (hf : LipschitzOnWith K f B)
    (hB : ∀ z ∈ S, ∀ s, U z s ∈ B)
    (t : ℝ) (x : E) (ht : t ≠ 0) (htS : (t,x) ∈ S) (h2tS : (2*t,x) ∈ S) :
    HasDerivAt (fun q => U (q,x) ⟨1,by simp⟩)
      (f (U (t,x) ⟨1,by simp⟩)) t := by
  let a : ℝ := 2*t
  have ha : a ≠ 0 := mul_ne_zero (by norm_num) ht
  have hratio : t/a = 1/2 := by dsimp [a]; field_simp
  have hmem : t/a ∈ Ioo (0:ℝ) 1 := by rw [hratio]; norm_num
  have hnear : ∀ᶠ q in 𝓝 t, (q,x) ∈ S ∧ q/a ∈ Ioo (0:ℝ) 1 :=
    ((continuousAt_id.prodMk continuousAt_const).eventually (hS.mem_nhds htS)).and
      ((continuousAt_id.div_const a).eventually (isOpen_Ioo.mem_nhds hmem))
  let γ := rescaledIntegralCurve f a x (U (a,x))
  have heq : (fun q => U (q,x) ⟨1,by simp⟩) =ᶠ[𝓝 t] (fun q => γ (q/a)) := by
    filter_upwards [hnear] with q hq
    have hqa : a * (q/a) = q := by field_simp
    have hs := rescaled_ode_path_time_scaling f a x (U (a,x)) (U (q,x))
      ⟨q/a,Ioo_subset_Icc_self hq.2⟩ K B hf (hEq (a,x) h2tS)
      (by simpa only [hqa] using hEq (q,x) hq.1)
      (hB (a,x) h2tS) (hB (q,x) hq.1)
    exact hs.symm.trans (rescaledIntegralCurve_eq f a x (U (a,x))
      (hEq (a,x) h2tS) ⟨q/a,Ioo_subset_Icc_self hq.2⟩).symm
  have hd := (hasDerivAt_rescaledIntegralCurve f a x (U (a,x))
    (hEq (a,x) h2tS) (t/a) (Ioo_subset_Icc_self hmem)).scomp t
      ((hasDerivAt_id t).div_const a)
  have hd' : HasDerivAt (fun q => γ (q/a)) (f (γ (t/a))) t := by
    simpa only [one_div,smul_smul,inv_mul_cancel₀ ha,one_smul,Function.comp_def,id_eq,γ] using hd
  have hpoint : U (t,x) ⟨1,by simp⟩ = γ (t/a) := heq.self_of_nhds
  rw [←hpoint] at hd'
  exact hd'.congr_of_eventuallyEq heq

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma exists_smooth_local_flow (f : E → E) (hf : ContDiff ℝ ∞ f) (a : E) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : (ℝ × E) → E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨U,S,hS,ha,hU,hUa,hEq⟩ := exists_smooth_rescaled_ode_family_on f hf a
  let fC : C(E,E) := ⟨f,hf.continuous⟩
  obtain ⟨K,B,hBa,hLip⟩ := (hf.contDiffAt.of_le (by simp : (1:ℕ∞ω) ≤ (∞:ℕ∞ω))).exists_lipschitzOnWith
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
    have ht2 : |2*t| < ε := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; dsimp [r] at habs; linarith
    constructor
    · change dist (t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨habs.trans hre,hx'.trans hre⟩
    · change dist (2*t,x) (0,a) < ε
      rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
      exact ⟨ht2,hx'.trans hre⟩
  let Φ : (ℝ × E) → E := fun z => U z ⟨1,by simp⟩
  refine ⟨r,hr,Φ,?_,?_,?_⟩
  · have hUSub : ContDiffOn ℝ ∞ U (Ioo (-r) r ×ˢ Metric.ball a r) :=
      hU.mono (fun z hz => hRS (htr z.1 hz.1 z.2 hz.2).1)
    exact (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : UnitTime)).contDiff.comp_contDiffOn hUSub
  · intro x hx
    have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_neg_of_pos hr,hr⟩
    have hi := ode_family_initial (hEq (0,x) (hRS (htr 0 h0 x hx).1))
    exact congrArg (fun u : C(UnitTime,E) => u ⟨1,by simp⟩) hi
  · intro t ht x hx
    by_cases ht0 : t = 0
    · subst t
      have hi : Φ (0,x) = x := congrArg (fun u : C(UnitTime,E) => u ⟨1,by simp⟩)
        (ode_family_initial (hEq (0,x) (hRS (htr 0 ht x hx).1)))
      rw [hi]
      exact ode_family_endpoint_deriv_zero fC hf U x
        (hU.contDiffAt (hS.mem_nhds (hRS (htr 0 ht x hx).1)))
        (Filter.eventually_of_mem (hS.mem_nhds (hRS (htr 0 ht x hx).1)) hEq)
    · exact ode_family_endpoint_deriv_ne_zero fC U R Metric.isOpen_ball
        (fun z hz => hEq z (hRS hz)) K B hLip hRB t x ht0
        (htr t ht x hx).1 (htr t ht x hx).2

end WeakMTWTransport

end

end OAI
