import Mathlib
import OAI.Probability.LogConcave.Numerics.NodesContinuous
import OAI.Probability.LogConcave.Sampling.CenteringJointLaw

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

def probabilityRmsBudget {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam A : ℝ≥0) (r h C : ℝ) (k n N : ℕ) : ℝ :=
  4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
    (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r)

theorem kernel_probability_errors (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},∀hT0 : 0<T,∀hT1 : T<1,∀hh : 0<h,h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s e : ProbabilityNode T h n,
      let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
      let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
      let μ := gibbs (centeringPotential F x r S)
      let forward := probabilityTransport hF x hr.le hl hT0.le hT1 S E
      let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
      (Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n N e (forward (pos y)) s-pos y‖^2) μ ∧
        (∫y,‖probabilityAnchoredPicard F x r T h n N e (forward (pos y)) s-pos y‖^2 ∂μ)≤
          (probabilityRmsBudget F x lam A r h C k n N)^2) ∧
      ∀Ψ : Point (d+d) → Point (d+d),Measurable Ψ → μ.map Ψ=μ →
      Integrable (fun y => ‖probabilityAnchoredPicard F x r T h n (N+1) s (pos (Ψ y)) e-
        forward (pos (Ψ y))‖^2) μ ∧
      (∫y,‖probabilityAnchoredPicard F x r T h n (N+1) s (pos (Ψ y)) e-
        forward (pos (Ψ y))‖^2 ∂μ)≤(probabilityRmsBudget F x lam A r h C k n (N+1))^2 := by
  obtain ⟨A,C,hC,k,hErr⟩ := probabilityAnchored_marginal_rms n hn
  refine ⟨A,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hq N s e
  dsimp only
  let S : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n s,probabilityNodeTime_mem hT0 hT1 hh hn s⟩
  let E : Icc (0:ℝ) T := ⟨probabilityNodeTime T h n e,probabilityNodeTime_mem hT0 hT1 hh hn e⟩
  let μ := gibbs (centeringPotential F x r S)
  let fw := probabilityTransport hF x hr.le hl hT0.le hT1 S E
  let bw := probabilityTransport hF x hr.le hl hT0.le hT1 E S
  let pos := fun y : Point (d+d) => (productPointEquiv d d y).1
  have hpos : Measurable pos := (productPointEquiv d d).continuous.measurable.fst
  have hfw : Continuous fw := probabilityTransport_continuous hF x hr.le hl hT0.le hT1 S E
  have hbw : Continuous bw := probabilityTransport_continuous hF x hr.le hl hT0.le hT1 E S
  have hp : μ.map pos=interpolationLaw F x r S :=
    centering_position_law hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1)
  have hfp : μ.map (fun y => fw (pos y))=interpolationLaw F x r E := by
    change μ.map (fw ∘ pos)=_
    rw [←Measure.map_map hfw.measurable hpos,hp]
    exact probabilityTransport_pushforward hF x hr.le hl hT0.le hT1 S E
  constructor
  · have he := hErr hF x hr hlam hl hd hT0 hT1 hh hsmall hq N e s
    have hm := ((probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn N e s).sub hbw).measurable
    have h := rms_bound_pullback (hfw.measurable.comp hpos) hfp hm he.1 he.2
    have hc (y : Point d) : bw (fw y)=y := by
      dsimp [bw,fw]
      rw [probabilityTransport_cocycle,probabilityTransport_initial]
    simpa only [Pi.sub_apply,Function.comp_def,hc,probabilityRmsBudget] using h
  · intro Ψ hm hlaw
    have he := hErr hF x hr hlam hl hd hT0 hT1 hh hsmall hq (N+1) s e
    have hΨ := harmonic_position_law hF x hr.le hl S.2.1 (S.2.2.trans_lt hT1) hm hlaw
    exact rms_bound_pullback (hpos.comp hm) hΨ
      ((probabilityAnchored_continuous hF x hr.le hl hT0 hT1 hh n hn (N+1) s e).sub hfw).measurable
      he.1 he.2

end LogConcaveSampling

end

end

end

end OAI
