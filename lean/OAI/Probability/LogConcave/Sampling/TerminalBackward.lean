import Mathlib
import OAI.Probability.LogConcave.Dynamics.ProbabilityFlowPushforward
import OAI.Probability.LogConcave.Sampling.TimeBump
import OAI.Probability.LogConcave.Dynamics.SmoothFlowJoint

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory ProbabilityTheory
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma probabilityTransport_cocycle (s t u : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 t u
      (probabilityTransport hF x hr hl hT0 hT1 s t z)=
      probabilityTransport hF x hr hl hT0 hT1 s u z :=
  GlobalODE.flow_cocycle _ _ s t u z
lemma probabilityTransport_initial (s : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 s s z=z := GlobalODE.flow_initial _ _ s z
lemma probabilityTransport_continuous (s t : Icc (0:ℝ) T) :
    Continuous (probabilityTransport hF x hr hl hT0 hT1 s t) :=
  (GlobalODE.flow_lipschitz _ _ s t).continuous

include hF hr hl in
lemma interpolationLaw_zero : interpolationLaw F x r 0=stdGaussian (Point d) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  simp only [interpolationLaw,zero_smul,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,
    Real.sqrt_one,one_smul,zero_add]
  simpa only [measure_univ,one_smul] using (Measure.map_snd_prod (μ:=gibbs (primitivePotential F x r)) (ν:=stdGaussian (Point d)))

lemma probabilityTransport_from_zero (t : Icc (0:ℝ) T) :
    (stdGaussian (Point d)).map
      (probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t)=
        interpolationLaw F x r t := by
  by_cases ht : (t:ℝ)=0
  · have he : t=⟨0,le_rfl,hT0⟩ := Subtype.ext ht
    rw [he]
    have hz : probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ ⟨0,le_rfl,hT0⟩=id :=
      funext (probabilityTransport_initial hF x hr hl hT0 hT1 _)
    rw [hz,Measure.map_id,interpolationLaw_zero hF x hr hl]
  · have htp : 0<(t:ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have ht1 : (t:ℝ)<1 := t.2.2.trans_lt hT1
    have he : probabilityTransport hF x hr hl hT0 hT1 ⟨0,le_rfl,hT0⟩ t=
        probabilityFlow hF x hr hl htp.le ht1 := by
      funext z
      exact (GlobalODE.flow_restrict
        (clampedProbabilityVelocity_continuous hF x hr hl htp.le ht1)
        (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
        (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl htp.le ht1 u)
        (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
        (Icc_subset_Icc_right t.2.2)
        (fun u hu y => by rw [clampedProbabilityVelocity_eq F x r t htp.le hu,
          clampedProbabilityVelocity_eq F x r T hT0 ⟨hu.1,hu.2.trans t.2.2⟩])
        ⟨0,le_rfl,htp.le⟩ ⟨t,htp.le,le_rfl⟩ z).symm
    rw [he]
    exact probabilityFlow_pushforward hF x hr hl htp ht1

theorem probabilityTransport_pushforward (s t : Icc (0:ℝ) T) :
    (interpolationLaw F x r s).map (probabilityTransport hF x hr hl hT0 hT1 s t)=
      interpolationLaw F x r t := by
  rw [←probabilityTransport_from_zero hF x hr hl hT0 hT1 s,
    Measure.map_map (probabilityTransport_continuous hF x hr hl hT0 hT1 s t).measurable
      (probabilityTransport_continuous hF x hr hl hT0 hT1 _ s).measurable]
  simp only [comp_def,probabilityTransport_cocycle]
  exact probabilityTransport_from_zero hF x hr hl hT0 hT1 t
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set Function Filter
open scoped Topology NNReal

variable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
  (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0≤r)
  (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1)

lemma smoothTimeClip_mem_extended (t : ℝ) :
    smoothTimeClip hT0 hT1 t∈Ioo (-1) (T+1) := by
  have hh := smoothTimeClip_sq_lt hT0 hT1 t
  constructor <;> nlinarith

def terminalBackward (p : ℝ × Point d) : Point d :=
  GlobalODE.flow (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    ⟨T,by constructor <;> linarith⟩ p.2 (smoothTimeClip hT0 hT1 p.1)

def terminalForward (p : ℝ × Point d) : Point d :=
  GlobalODE.flow (a:= -1) (b:=T+1)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    (projIcc (-1) (T+1) (by linarith) (smoothTimeClip hT0 hT1 p.1)) p.2 T

lemma terminalBackward_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalBackward hF x hr hl hT0 hT1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (GlobalODE.smooth_flow_joint (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1)
    (fun u (_ : u∈Icc (-1) (T+1)) => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    ⟨T,by constructor <;> linarith⟩ (smoothTimeClip hT0 hT1 p.1,p.2)
    (smoothTimeClip_mem_extended hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk contDiff_snd).contDiffAt

lemma terminalForward_smooth : ContDiff ℝ (⊤:ℕ∞) (terminalForward hF x hr hl hT0 hT1) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  have hclip : ContDiff ℝ (⊤:ℕ∞) (smoothTimeClip hT0 hT1) :=
    contDiff_infty.mpr (smoothTimeClip_contDiff hT0 hT1)
  exact (GlobalODE.backward_flow_smooth (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1)
    (by linarith : (-1:ℝ)≤T+1)
    (fun u (_ : u∈Icc (-1) (T+1)) => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    ⟨T,by constructor <;> linarith⟩ (smoothTimeClip hT0 hT1 p.1,p.2)
    (smoothTimeClip_mem_extended hT0 hT1 p.1)).comp p
      ((hclip.comp contDiff_fst).prodMk contDiff_snd).contDiffAt

lemma probabilityTransport_eq_extended (s t : Icc (0:ℝ) T) (z : Point d) :
    probabilityTransport hF x hr hl hT0 hT1 s t z=
      GlobalODE.flow (a:= -1) (b:=T+1)
      (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
      (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
      ⟨s,by constructor <;> linarith [s.2.1,s.2.2]⟩ z t := by
  apply GlobalODE.flow_restrict
    (clampedProbabilityVelocity_continuous hF x hr hl hT0 hT1)
    (smoothProbabilityVelocity_smooth hF x hr hl hT0 hT1).continuous
    (fun u _ => clampedProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
    (fun u _ => smoothProbabilityVelocity_lipschitz hF x hr hl hT0 hT1 u)
  · intro u hu
    constructor <;> linarith [hu.1,hu.2]
  · intro u hu y
    rw [clampedProbabilityVelocity_eq F x r T hT0 hu]
    dsimp [smoothProbabilityVelocity]
    rw [smoothTimeClip_eq hT0 hT1 hu]

lemma terminalBackward_eq (t : Icc (0:ℝ) T) (y : Point d) :
    terminalBackward hF x hr hl hT0 hT1 (t,y)=
      probabilityTransport hF x hr hl hT0 hT1 ⟨T,hT0,le_rfl⟩ t y := by
  rw [probabilityTransport_eq_extended]
  simp only [terminalBackward,smoothTimeClip_eq hT0 hT1 t.2]
lemma terminalForward_eq (t : Icc (0:ℝ) T) (y : Point d) :
    terminalForward hF x hr hl hT0 hT1 (t,y)=
      probabilityTransport hF x hr hl hT0 hT1 t ⟨T,hT0,le_rfl⟩ y := by
  rw [probabilityTransport_eq_extended]
  simp only [terminalForward,smoothTimeClip_eq hT0 hT1 t.2,
    projIcc_of_mem _ (show (t:ℝ)∈Icc (-1) (T+1) by constructor <;> linarith [t.2.1,t.2.2])]

lemma terminalForward_backward (t : Icc (0:ℝ) T) (y : Point d) :
    terminalForward hF x hr hl hT0 hT1 (t,terminalBackward hF x hr hl hT0 hT1 (t,y))=y := by
  rw [terminalForward_eq,terminalBackward_eq,probabilityTransport_cocycle,probabilityTransport_initial]
lemma terminalBackward_forward (t : Icc (0:ℝ) T) (y : Point d) :
    terminalBackward hF x hr hl hT0 hT1 (t,terminalForward hF x hr hl hT0 hT1 (t,y))=y := by
  rw [terminalBackward_eq,terminalForward_eq,probabilityTransport_cocycle,probabilityTransport_initial]
end LogConcaveSampling

end

end

end

end OAI
