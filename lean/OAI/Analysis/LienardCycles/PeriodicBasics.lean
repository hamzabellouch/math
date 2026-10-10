import OAI.Analysis.LienardCycles.FiniteFlow

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
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
lemma vectorField_contDiff (F : Polynomial ℝ) : ContDiff ℝ ω (vectorField F) := by
  have hp : ContDiff ℝ ω (fun x : ℝ=>F.eval x) := by simpa [Polynomial.aeval_def] using! F.contDiff_aeval ω
  exact (contDiff_snd.sub (hp.comp contDiff_fst)).prodMk contDiff_fst.neg
lemma IsSolution.continuous {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) : Continuous z :=
  continuous_iff_continuousAt.mpr fun t=>(hz t).continuousAt
lemma IsSolution.x_deriv {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) (t : ℝ) :
    HasDerivAt (fun s=>(z s).1) ((z t).2-F.eval (z t).1) t := by
  simpa [vectorField] using! (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
lemma IsSolution.y_deriv {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) (t : ℝ) :
    HasDerivAt (fun s=>(z s).2) (-(z t).1) t := by
  simpa [vectorField] using! (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hz t)
lemma IsSolution.eq_of_eq {F : Polynomial ℝ} {z w : ℝ → Plane}
    (hz : IsSolution F z) (hw : IsSolution F w) {c : ℝ} (hc : z c=w c) : z=w := by
  funext t
  have h := GlobalODE.unique_on_open_interval (vectorField F) isOpen_univ
    (vectorField_contDiff F |>.of_le (by simp) |>.contDiffOn)
    (a:=min t c-1) (b:=max t c+1) (c:=c)
    (by constructor <;> linarith [min_le_right t c,le_max_right t c])
    (fun s _=>⟨hz s,mem_univ _⟩) (fun s _=>⟨hw s,mem_univ _⟩) hc
  exact h (by constructor <;> linarith [min_le_left t c,le_max_left t c])
lemma IsSolution.shift {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z) (s : ℝ) :
    IsSolution F (fun t=>z (t+s)) := by
  intro t
  simpa using! (hz (t+s)).scomp t ((hasDerivAt_id t).add_const s)
lemma IsSolution.periodic_of_hit {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    {s t : ℝ} (he : z (s+t)=z s) : Function.Periodic z t := by
  have h := (hz.shift t).eq_of_eq hz (c:=s) he
  exact fun x=>congrFun h x
lemma equilibrium_solution (F : Polynomial ℝ) : IsSolution F (fun _=>(0,F.eval 0)) := by
  intro t
  simpa [vectorField] using! hasDerivAt_const t ((0,F.eval 0):Plane)
lemma IsSolution.avoids_equilibrium {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    (hn : ∃ s t, z s≠z t) (s : ℝ) : z s≠(0,F.eval 0) := by
  intro he
  have h := hz.eq_of_eq (equilibrium_solution F) he
  obtain ⟨t,u,htu⟩ := hn
  exact htu (by rw [h])
lemma IsSolution.axis_transverse {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    (hn : ∃ s t, z s≠z t) {s : ℝ} (hs : (z s).1=0) : (z s).2≠F.eval 0 := by
  intro h
  exact hz.avoids_equilibrium hn s (Prod.ext hs h)
lemma IsPeriodicOrbit.isCompact {F : Polynomial ℝ} {C : Set Plane} (hC : IsPeriodicOrbit F C) :
    IsCompact C := by
  obtain ⟨z,T,hz,hT,hp,_,rfl⟩ := hC
  rw [←hp.image_Icc hT 0]
  exact isCompact_Icc.image hz.continuous
lemma IsSolution.axis_finite {F : Polynomial ℝ} {z : ℝ → Plane} (hz : IsSolution F z)
    (hn : ∃ s t,z s≠z t) (a b : ℝ) : {t ∈ Icc a b | (z t).1=0}.Finite := by
  have hk : IsCompact {t ∈ Icc a b | (z t).1=0} :=
    isCompact_Icc.inter_right (isClosed_eq hz.continuous.fst continuous_const)
  apply hk.finite
  rw [isDiscrete_iff_nhdsNE]
  intro t ht
  have he := (hz.x_deriv t).eventually_ne (c:=0) (by
    change (z t).2-F.eval (z t).1≠0
    rw [ht.2]
    exact sub_ne_zero.mpr (hz.axis_transverse hn ht.2))
  apply Filter.eventually_false_iff_eq_bot.mp
  have hh : ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 {t ∈ Icc a b | (z t).1=0}, False := by
    filter_upwards [he.filter_mono inf_le_left, (show ∀ᶠ s in 𝓝[≠] t ⊓ 𝓟 {t ∈ Icc a b | (z t).1=0}, s ∈ {t ∈ Icc a b | (z t).1=0} from Filter.Eventually.filter_mono inf_le_right (Filter.eventually_principal.mpr (fun _ h=>h)))] with s hs hs'
    exact hs hs'.2
  exact hh
end QuinticLienard

end OAI
