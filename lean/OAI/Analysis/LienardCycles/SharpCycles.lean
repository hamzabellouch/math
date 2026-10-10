import OAI.Analysis.LienardCycles.CycleSection

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
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open GlobalODE PartialCalculus
noncomputable def average (s : ℝ) : ℝ := -Real.pi*s^2*(4-5*s^2+s^4)
lemma average_deriv (s : ℝ) : HasDerivAt average (-Real.pi*(8*s-20*s^3+6*s^5)) s := by
  have H := (((hasDerivAt_id s).pow 2).const_mul (-Real.pi)).mul
    (((hasDerivAt_const s (4:ℝ)).sub (((hasDerivAt_id s).pow 2).const_mul 5)).add ((hasDerivAt_id s).pow 4))
  convert! H using 1
  simp
  ring

def ReturnFamily.Good (R : ReturnFamily) (p : ℝ × ℝ) : Prop :=
  0<R.σ p ∧ (R.path p (R.σ p)).2.1.1=0 ∧
    0<(R.path p (R.σ p)).2.1.2 ∧ 0<p.2 ∧ R.σ p<turn+1 ∧
    ∀ t ∈ Icc (-1) (turn+1),R.W (R.path p t)=V (R.path p t)
lemma ReturnFamily.Good.faithful {R : ReturnFamily} {p : ℝ × ℝ} (h : R.Good p) :
    ∀ t ∈ Icc 0 (R.σ p), R.W (R.path p t)=V (R.path p t) := by
  intro t ht
  exact h.2.2.2.2.2 t ⟨by linarith [ht.1],ht.2.trans h.2.2.2.2.1.le⟩
lemma ReturnFamily.limitCycle_of_Q (R : ReturnFamily) {ε b : ℝ} (hε : ε≠0)
    (hz : R.Q (ε,b)=0)
    (hnear : ∀ᶠ c in 𝓝 b,R.Good (ε,c) ∧ (R.Q (ε,c)=0 → c=b)) :
    IsLimitCycle (F ε) (range (fun t=>(R.path (ε,b) t).2.1)) := by
  have hg := hnear.self_of_nhds.1
  have hclosed := R.closed_of_Q hg.1 hg.2.2.2.1 hg.2.1 hg.2.2.1 hg.faithful hz
  have hC := R.periodic_orbit hg.1 hg.2.2.2.1 hg.faithful hclosed
  have hbp : (0,b) ∈ range (fun t=>(R.path (ε,b) t).2.1) := ⟨0,by simp [initial]⟩
  apply hC.limitCycle_of_return (quintic_representation (F_degree ε)) (by simpa using hg.2.2.2.1) hbp
    (g:=fun c t=>(R.path (ε,c) t).2.1) (τ:=fun c=>R.σ (ε,c))
  filter_upwards [hnear] with c hc
  have hf := hc.1.faithful
  have hcont : Continuous (R.path (ε,c)) := R.continuous.comp (continuous_const.prodMk continuous_id)
  refine ⟨hc.1.1,by simp [initial],hcont.snd.fst.continuousOn,
    R.physical_deriv hc.1.1.le hf,hc.1.2.1,by simpa using hc.1.2.2.1,?_⟩
  intro hfixed
  have hder (t : ℝ) (ht : t ∈ Icc 0 (R.σ (ε,c))) :
      HasDerivAt (R.path (ε,c)) (V (R.path (ε,c) t)) t := by rw [←hf t ht];exact R.deriv (ε,c) t
  have he := energy_identity hc.1.1.le hcont.continuousOn hder (R.path_zero (ε,c))
  have hhx := congrArg Prod.fst hfixed
  have hhy := congrArg Prod.snd hfixed
  simp only [hhx,hhy,zero_pow (by decide : (2:ℕ)≠0),zero_add,sub_self,zero_div] at he
  exact hc.2 ((mul_eq_zero.mp he.symm).resolve_left hε)
lemma cycle_near_simple {s d : ℝ} (hs : 0<s) (hzero : average s=0)
    (hd : HasDerivAt average d s) (hdne : d≠0) :
    ∀ᶠ ε in 𝓝 (0:ℝ),ε≠0 → ∃ (C : Set Plane) (b : ℝ),
      IsLimitCycle (F ε) C ∧ (0,b) ∈ C ∧ |b-s|<1/4 := by
  obtain ⟨R,_,_,hQ,hslice,hnear⟩ := return_family hs
  have hQ0 : R.Q (0,s)=0 := hslice.self_of_nhds.trans hzero
  have hdQ : HasDerivAt (fun b=>R.Q (0,b)) d s := hd.congr_of_eventuallyEq hslice
  obtain ⟨S,hS,hS0,hSz,hSu⟩ := transverse_hit hQ hdQ hdne
  rw [hQ0] at hSz hSu
  have hpt : Tendsto (fun ε : ℝ=>(ε,S ε)) (𝓝 0) (𝓝 (0,s)) := by
    simpa only [hS0,id_eq] using (continuousAt_id.prodMk hS.continuousAt).tendsto
  have hnv := hpt.eventually (hnear.and hSu).eventually_nhds
  have hclose : ∀ᶠ ε in 𝓝 (0:ℝ),|S ε-s|<1/4 :=
    (hS.continuousAt.sub continuousAt_const |>.abs).eventually (eventually_lt_nhds (by change |S 0-s|<1/4;rw [hS0];norm_num))
  filter_upwards [hSz,hnv,hclose] with ε hz hn hc hε
  have hnb := (show ContinuousAt (fun b : ℝ=>(ε,b)) (S ε) from
    continuousAt_const.prodMk continuousAt_id).eventually hn
  have hlocal : ∀ᶠ b in 𝓝 (S ε),R.Good (ε,b) ∧ (R.Q (ε,b)=0 → b=S ε) := by
    filter_upwards [hnb] with b hb
    exact ⟨hb.1,fun h=>(hb.2.mp h).symm⟩
  exact ⟨_,S ε,R.limitCycle_of_Q hε hz hlocal,⟨0,by simp [initial]⟩,hc⟩
lemma two_cycles : ∃ ε : ℝ, ∃ C D : Set Plane,IsLimitCycle (F ε) C ∧ IsLimitCycle (F ε) D ∧ C≠D := by
  have h1 : ∀ᶠ ε in 𝓝 (0:ℝ),ε≠0 → ∃ (C : Set Plane) (b : ℝ),
      IsLimitCycle (F ε) C ∧ (0,b) ∈ C ∧ |b-1|<1/4 :=
    cycle_near_simple (s:=1) (d:=6*Real.pi) (by norm_num) (by norm_num [average])
      (by convert average_deriv 1 using 1; ring) (by positivity)
  have h2 : ∀ᶠ ε in 𝓝 (0:ℝ),ε≠0 → ∃ (C : Set Plane) (b : ℝ),
      IsLimitCycle (F ε) C ∧ (0,b) ∈ C ∧ |b-2|<1/4 :=
    cycle_near_simple (s:=2) (d:=(-48)*Real.pi) (by norm_num) (by norm_num [average])
      (by convert average_deriv 2 using 1; ring) (by nlinarith [Real.pi_pos])
  have hp : ∀ᶠ ε in 𝓝[>] (0:ℝ),0<ε ∧
      (ε≠0 → ∃ (C : Set Plane) (b : ℝ),IsLimitCycle (F ε) C ∧ (0,b) ∈ C ∧ |b-1|<1/4) ∧
      (ε≠0 → ∃ (C : Set Plane) (b : ℝ),IsLimitCycle (F ε) C ∧ (0,b) ∈ C ∧ |b-2|<1/4) := by
    filter_upwards [self_mem_nhdsWithin,(h1.and h2).filter_mono inf_le_left] with ε hε hh
    exact ⟨hε,hh⟩
  obtain ⟨ε,hε,hC,hD⟩ := hp.exists
  obtain ⟨C,b,hC,hb,hb1⟩ := hC (ne_of_gt hε)
  obtain ⟨D,c,hD,hc,hc2⟩ := hD (ne_of_gt hε)
  refine ⟨ε,C,D,hC,hD,?_⟩
  intro heq
  have hbpos : (F ε).eval 0<b := by rw [F_zero];linarith [(abs_lt.mp hb1).1]
  have hcpos : (F ε).eval 0<c := by rw [F_zero];linarith [(abs_lt.mp hc2).1]
  have hpoint := hC.1.axis_unique (quintic_representation (F_degree ε)) hbpos hb (heq ▸ hc) rfl hcpos
  have he : c=b := congrArg Prod.snd hpoint
  linarith [(abs_lt.mp hb1).2,(abs_lt.mp hc2).1]
lemma sharpness : ∃ G : Polynomial ℝ,G.degree≤5 ∧ {C : Set Plane | IsLimitCycle G C}.encard=2 := by
  obtain ⟨ε,C,D,hC,hD,hne⟩ := two_cycles
  refine ⟨F ε,F_degree ε,le_antisymm (upper_bound (F ε) (F_degree ε)) ?_⟩
  rw [←Set.encard_pair hne]
  exact Set.encard_mono (pair_subset hC hD)
end QuinticLienard.Sharpness

end OAI
