import Mathlib
import OAI.Probability.LogConcave.Sampling.TerminalBackward

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function Filter Metric
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma smoothTimeClip_eventually_eq {t : ℝ} (ht : t∈Icc 0 T) :
    smoothTimeClip hT0 hT1=ᶠ[𝓝 t] id := by
  have hb : t∈ball (T/2) ((T+1)/4) := by
    rw [mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  filter_upwards [isOpen_ball.mem_nhds hb] with u hu
  have hh : timeBump hT0 hT1 u=1 := (timeBump hT0 hT1).one_of_mem_closedBall
    (show u∈closedBall (T/2) ((T+1)/4) from ball_subset_closedBall hu)
  simp [smoothTimeClip,hh]

def spatialTransport (s : Icc (0:ℝ) T) (p : ℝ × Point d) : Point d :=
  GlobalODE.flow (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ p.2 (smoothTimeClip hT0 hT1 p.1)

lemma spatialTransport_smooth (s : Icc (0:ℝ) T) :
    ContDiff ℝ (⊤:ℕ∞) (spatialTransport hF x hr hl hT0 hT1 s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (GlobalODE.smooth_flow_joint (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1)
    (fun u (_ : u∈Icc (-1) (T+1)) => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ (smoothTimeClip hT0 hT1 p.1,p.2)
    (smoothTimeClip_mem_extended hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk contDiff_snd).contDiffAt

lemma spatialTransport_eq (s t : Icc (0:ℝ) T) (y : Point d) :
    spatialTransport hF x hr hl hT0 hT1 s (t,y)=
      probabilityTransport hF x hr hl hT0 hT1 s t y := by
  rw [probabilityTransport_eq_extended]
  simp only [spatialTransport,smoothTimeClip_eq hT0 hT1 t.2]

lemma spatialTransport_initial (s : Icc (0:ℝ) T) (y : Point d) :
    spatialTransport hF x hr hl hT0 hT1 s (s,y)=y := by
  rw [spatialTransport_eq,probabilityTransport_initial]

lemma spatialTransport_deriv (s : Icc (0:ℝ) T) {t : ℝ} (ht : t∈Icc 0 T) (y : Point d) :
    HasDerivAt (fun u => spatialTransport hF x hr hl hT0 hT1 s (u,y))
      (probabilityVelocity F x r t (spatialTransport hF x hr hl hT0 hT1 s (t,y))) t := by
  have he := smoothTimeClip_eventually_eq hT0 hT1 ht
  have hclip := (hasDerivAt_id t).congr_of_eventuallyEq he
  have hh := GlobalODE.flow_deriv (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ y t (by constructor <;> linarith [ht.1,ht.2])
  have hlow : (-1:ℝ)<t := by linarith [ht.1]
  have hhigh : t<T+1 := by linarith [ht.2]
  have hflow := hh.hasDerivAt (Icc_mem_nhds hlow hhigh)
  have hs : smoothTimeClip hT0 hT1 t=t := he.eq_of_nhds
  rw [←hs] at hflow
  have hd := hflow.scomp t hclip
  simp only [hs,smoothProbabilityVelocity,one_smul] at hd
  convert hd using 1 <;> first | rfl | simp only [spatialTransport,hs]
end LogConcaveSampling

end

end

end

end OAI
