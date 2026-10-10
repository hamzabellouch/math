import OAI.Analysis.LienardCycles.PeriodicSymmetry

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs

structure IsOpenArch (φ u : ℝ → ℝ) (A B : ℝ) : Prop where
  lt : A<B
  continuous : Continuous u
  left : u A=0
  right : u B=0
  positive : ∀ y ∈ Ioo A B,0<u y
  equation : ∀ y ∈ Ioo A B,HasDerivAt u (φ (u y)-y) y
lemma IsOpenArch.peak_exists {φ u : ℝ → ℝ} {A B : ℝ} (hu : IsOpenArch φ u A B) :
    ∃ H : ℝ,0<H ∧ φ H ∈ Ioo A B ∧ u (φ H)=H ∧ ∀ y ∈ Icc A B,u y≤H := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hu.lt.le) hu.continuous.continuousOn
  have hmid : (A+B)/2 ∈ Ioo A B := ⟨by linarith [hu.lt],by linarith [hu.lt]⟩
  have hmpos : 0<u m := (hu.positive _ hmid).trans_le (hmax (Ioo_subset_Icc_self hmid))
  have hmi : m ∈ Ioo A B := by
    refine ⟨lt_of_le_of_ne hm.1 ?_,lt_of_le_of_ne hm.2 ?_⟩
    · intro he;rw [←he,hu.left] at hmpos;exact lt_irrefl _ hmpos
    · intro he;rw [he,hu.right] at hmpos;exact lt_irrefl _ hmpos
  have hzero := (hmax.isLocalMax (Icc_mem_nhds hmi.1 hmi.2)).hasDerivAt_eq_zero (hu.equation _ hmi)
  have he : φ (u m)=m := sub_eq_zero.mp hzero
  exact ⟨u m,hmpos,he.symm ▸ hmi,by rw [he],fun _ hy=>hmax hy⟩
lemma profile_extension_along_compact {φ u : ℝ → ℝ} {S : Set ℝ}
    (hφ : ContDiffOn ℝ 1 φ (Ioi 0)) (hu : Continuous u) (hS : IsCompact S) (hn : S.Nonempty)
    (hp : ∀ y ∈ S,0<u y) :
    ∃ ψ : ℝ → ℝ,ContDiff ℝ 1 ψ ∧ ∀ y ∈ S,ψ (u y)=φ (u y) := by
  obtain ⟨m,hm,hmin⟩ := hS.exists_isMinOn hn hu.continuousOn
  obtain ⟨M,hM,hmax⟩ := hS.exists_isMaxOn hn hu.continuousOn
  obtain ⟨ψ,K,B,hψ,_,_,he⟩ := positive_profile_extension hφ (half_pos (hp m hm))
    (show u m/2<u M+1 by have hv : u m ≤ u M := hmax hm;
                          linarith [hp m hm])
  exact ⟨ψ,hψ,fun y hy=>he ⟨by have hv : u m ≤ u y := hmin hy; linarith [hp m hm],by have hv : u y ≤ u M := hmax hy; linarith⟩⟩
lemma IsOpenArch.derivative_signs {φ u : ℝ → ℝ} {A B H : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) :
    (∀ y ∈ Ioo A B,y<φ H → 0<φ (u y)-y) ∧
    (∀ y ∈ Ioo A B,φ H<y → φ (u y)-y<0) := by
  have hs (y : ℝ) (hy : y ∈ Ioo A B) :
      (y<φ H → 0<φ (u y)-y) ∧ (φ H<y → φ (u y)-y<0) := by
    let l := min y (φ H)
    let r := max y (φ H)
    have hsub : Icc l r ⊆ Ioo A B := by
      intro v hv
      exact ⟨(lt_min hy.1 hp.1).trans_le hv.1,hv.2.trans_lt (max_lt hy.2 hp.2)⟩
    have hyp : y ∈ Icc l r := ⟨min_le_left _ _,le_max_left _ _⟩
    have hpp : φ H ∈ Icc l r := ⟨min_le_right _ _,le_max_right _ _⟩
    obtain ⟨ψ,hψ,he⟩ := profile_extension_along_compact hφ hu.continuous isCompact_Icc ⟨y,hyp⟩
      (fun v hv=>hu.positive v (hsub hv))
    have heH : ψ H=φ H := by simpa only [hpeak] using he _ hpp
    have hd : ∀ v ∈ Icc l r,HasDerivAt u (ψ (u v)-v) v := fun v hv=>by
      rw [he v hv]; exact hu.equation v (hsub hv)
    have signs := derivative_signs_on_Icc (t := H) hψ hu.continuous hd
      (by simpa only [heH] using hpeak) (by simpa only [heH] using hpp)
    constructor
    · intro h
      have hh := signs.1 y hyp (by simpa only [heH] using h)
      simpa only [he y hyp] using hh
    · intro h
      have hh := signs.2 y hyp (by simpa only [heH] using h)
      simpa only [he y hyp] using hh
  exact ⟨fun y hy=> (hs y hy).1,fun y hy=> (hs y hy).2⟩
lemma IsOpenArch.monotonicity {φ u : ℝ → ℝ} {A B H : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) :
    StrictMonoOn u (Icc A (φ H)) ∧ StrictAntiOn u (Icc (φ H) B) := by
  have hs := hu.derivative_signs hφ hp hpeak
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hu.continuous.continuousOn
    intro y hy
    have hy' : y ∈ Ioo A (φ H) := by simpa using hy
    have hyab : y ∈ Ioo A B := ⟨hy'.1,hy'.2.trans hp.2⟩
    rw [(hu.equation y hyab).deriv]
    exact hs.1 y hyab hy'.2
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hu.continuous.continuousOn
    intro y hy
    have hy' : y ∈ Ioo (φ H) B := by simpa using hy
    have hyab : y ∈ Ioo A B := ⟨hp.1.trans hy'.1,hy'.2⟩
    rw [(hu.equation y hyab).deriv]
    exact hs.2 y hyab hy'.1
lemma IsOpenArch.subarch {φ u : ℝ → ℝ} {A B H h : ℝ}
    (hu : IsOpenArch φ u A B) (hφ : ContDiffOn ℝ 1 φ (Ioi 0))
    (hp : φ H ∈ Ioo A B) (hpeak : u (φ H)=H) (hh : 0<h) (hH : h<H) :
    ∃ a b,A<a ∧ b<B ∧ IsArch φ u h H a b := by
  obtain ⟨a,ha,hua⟩ := intermediate_value_Icc hp.1.le hu.continuous.continuousOn
    (show h ∈ Icc (u A) (u (φ H)) by rw [hu.left,hpeak];exact ⟨hh.le,hH.le⟩)
  obtain ⟨b,hb,hub⟩ := intermediate_value_Icc' hp.2.le hu.continuous.continuousOn
    (show h ∈ Icc (u B) (u (φ H)) by rw [hu.right,hpeak];exact ⟨hh.le,hH.le⟩)
  have hAa : A<a := lt_of_le_of_ne ha.1 (by intro he;rw [←he,hu.left] at hua;exact hh.ne hua)
  have hap : a<φ H := lt_of_le_of_ne ha.2 (by intro he;rw [he,hpeak] at hua;exact hH.ne hua.symm)
  have hpb : φ H<b := lt_of_le_of_ne hb.1 (by intro he;rw [←he,hpeak] at hub;exact hH.ne hub.symm)
  have hbB : b<B := lt_of_le_of_ne hb.2 (by intro he;rw [he,hu.right] at hub;exact hh.ne hub)
  have hs := hu.derivative_signs hφ hp hpeak
  have hm := hu.monotonicity hφ hp hpeak
  refine ⟨a,b,hAa,hbB,hu.continuous,hap,hpb,hpeak,hua,hub,?_,?_,?_,?_,
    hm.1.mono (Icc_subset_Icc hAa.le le_rfl),hm.2.mono (Icc_subset_Icc le_rfl hbB.le)⟩
  · have H := hs.1 a ⟨hAa,hap.trans hp.2⟩ hap
    rw [hua] at H;linarith
  · have H := hs.2 b ⟨hp.1.trans hpb,hbB⟩ hpb
    rw [hub] at H;linarith
  · intro y hy;exact hu.equation y ⟨hAa.trans_le hy.1,hy.2.trans_lt hbB⟩
  · intro y hy
    rcases le_total y (φ H) with hyp|hpy
    · exact ⟨hua ▸ hm.1.monotoneOn ha ⟨hAa.le.trans hy.1,hyp⟩ hy.1,
        hpeak ▸ hm.1.monotoneOn ⟨hAa.le.trans hy.1,hyp⟩ ⟨hp.1.le,le_rfl⟩ hyp⟩
    · exact ⟨hub ▸ hm.2.antitoneOn ⟨hpy,hy.2.trans hbB.le⟩ hb hy.2,
        hpeak ▸ hm.2.antitoneOn ⟨le_rfl,hp.2.le⟩ ⟨hpy,hy.2.trans hbB.le⟩ hpy⟩
end QuinticLienard.ScalarArcs

end OAI
