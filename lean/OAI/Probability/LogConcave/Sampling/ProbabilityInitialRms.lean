import Mathlib
import OAI.Probability.LogConcave.Numerics.NodeLp
import OAI.Probability.LogConcave.Sampling.HarmonicStationaryMoment
import OAI.Probability.LogConcave.Analysis.GaussianAffineNormMoment

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

def probabilityInitialRms {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r : ℝ) : ℝ :=
  Real.sqrt (2*(terminalTransportConstant*(r*‖primitiveField F x r 0‖+
    (lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+2*(terminalTransportConstant*((lam:ℝ)*r^2))^2*d)

lemma probabilityInitialRms_nonneg {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r : ℝ) : 0≤probabilityInitialRms F x lam r := Real.sqrt_nonneg _

lemma probabilityInitialRms_sq {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (lam : ℝ≥0) (r : ℝ) :
    probabilityInitialRms F x lam r^2=
      2*(terminalTransportConstant*(r*‖primitiveField F x r 0‖+(lam:ℝ)*r^2*Real.pi*Real.sqrt d))^2+
      2*(terminalTransportConstant*((lam:ℝ)*r^2))^2*d := Real.sq_sqrt (by positivity)

theorem probabilityPicard_forward_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},0<T → T<1 → 0<h → h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀i : ProbabilityNode T h n,
      Integrable (fun z => ‖probabilityPicard F x r T h n N z i-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n i) z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖probabilityPicard F x r T h n N z i-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n i) z‖^2 ∂stdGaussian (Point d))≤
        (2*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*probabilityInitialRms F x lam r)^2 := by
  obtain ⟨A,hA,hA'⟩ := probabilityWeight_budget n hn
  obtain ⟨C,hC,k,hk⟩ := probability_mean_defect_rms n hn
  refine ⟨⟨A,hA⟩,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hq N i
  have hi (j : ProbabilityNode T h n) := probabilityNodeTime_mem hT0 hT1 hh hn j
  have hi' (j : ProbabilityNode T h n) : probabilityNodeTime T h n j∈Icc (0:ℝ) 1 :=
    ⟨(hi j).1,(hi j).2.trans hT1.le⟩
  let D := C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)
  have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hD : 0≤D := by dsimp [D]; positivity
  have hφ (j : ProbabilityNode T h n) := probabilityMeanVelocity_lipschitz hF x hr.le hl
    (hi j).1 ((hi j).2.trans_lt hT1)
  have hdef (j : ProbabilityNode T h n) :
      (∫z,‖FinitePicard.step (probabilityWeight T h n)
        (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
        (fun _ => z) (fun j => fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n j) z) j-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n j) z‖^2 ∂stdGaussian (Point d))≤D^2 := by
    simp_rw [probabilityPicard_exact_defect hF x hr.le hl hT0 hT1 hh n hn,
      norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow]
    rw [integral_const_mul]
    convert mul_le_mul_of_nonneg_left (hk hF x hr hlam hl hd hT0 hT1 hh hsmall j).2 (sq_nonneg r) using 1;
      first | rfl | (dsimp [D]; ring)
  have hinit (j : ProbabilityNode T h n) :
      (∫z,‖z-fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n j) z‖^2
        ∂stdGaussian (Point d))≤(probabilityInitialRms F x lam r)^2 := by
    rw [probabilityInitialRms_sq]
    exact (probabilityFlow_initial_rms hF x hr.le hl (hi' j)).2
  have he := FinitePicard.nodes_rms (ν:=stdGaussian (Point d)) (A:=⟨A,hA⟩)
    (probabilityWeight T h n) (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
    hφ (fun _ z => z) (fun j => fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n j))
    (fun _ => IsGaussian.memLp_two_id) (fun j => gaussian_lipschitz_memLp
      (fullProbabilityFlow_lipschitz hF x hr.le hl (hi' j)))
    (hA' hT0 hT1 hh) hq hD (probabilityInitialRms_nonneg F x lam r) hdef hinit N i
  simpa only [probabilityPicard,D,mul_assoc] using he
end LogConcaveSampling

end

end

end

end OAI
