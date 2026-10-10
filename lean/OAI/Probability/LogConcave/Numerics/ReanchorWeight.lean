import Mathlib
import OAI.Probability.LogConcave.Sampling.ProbabilityInitialRms

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.FinitePicard
open MeasureTheory
open scoped BigOperators

variable {I E Ω : Type*} [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E]

def reanchorWeight (w : I → I → ℝ) (s : I) : I → I → ℝ := fun i j => w i j-w s j

lemma reanchorWeight_budget (w : I → I → ℝ) {A : ℝ}
    (hw : ∀i,∑j,|w i j|≤A) (s i : I) : ∑j,|reanchorWeight w s i j|≤2*A := by
  calc
    _ ≤ ∑j,(|w i j|+|w s j|) := Finset.sum_le_sum (fun j _ => abs_sub _ _)
    _ = (∑j,|w i j|)+(∑j,|w s j|) := Finset.sum_add_distrib
    _ ≤ 2*A := by linarith [hw i,hw s]

lemma step_reanchor_defect (w : I → I → ℝ) (φ : I → E → E) (e : I → E)
    (z : E) (s i : I) :
    step (reanchorWeight w s) φ (fun _ => e s) e i-e i=
      (step w φ (fun _ => z) e i-e i)-(step w φ (fun _ => z) e s-e s) := by
  simp only [step,correction,reanchorWeight,Pi.add_apply,sub_smul,Finset.sum_sub_distrib]
  abel

omit [NormedSpace ℝ E] in
lemma integral_norm_sub_sq_bound [MeasurableSpace Ω] (ν : Measure Ω) (f g : Ω → E)
    {D H : ℝ} (hf : Integrable (fun ω => ‖f ω‖^2) ν)
    (hg : Integrable (fun ω => ‖g ω‖^2) ν)
    (hb : (∫ω,‖f ω‖^2 ∂ν)≤D) (hc : (∫ω,‖g ω‖^2 ∂ν)≤H) :
    (∫ω,‖f ω-g ω‖^2 ∂ν)≤2*D+2*H := by
  have hp (ω : Ω) : ‖f ω-g ω‖^2≤2*‖f ω‖^2+2*‖g ω‖^2 := by
    have he := norm_sub_le (f ω) (g ω)
    have hn := norm_nonneg (f ω-g ω)
    nlinarith [sq_nonneg (‖f ω‖-‖g ω‖),norm_nonneg (f ω),norm_nonneg (g ω)]
  have he := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖f ω-g ω‖))
    ((hf.const_mul 2).add (hg.const_mul 2)) (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at he
  rw [integral_add (hf.const_mul 2) (hg.const_mul 2),integral_const_mul,integral_const_mul] at he
  linarith
end LogConcaveSampling.FinitePicard

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory FinitePicard
open scoped Classical BigOperators NNReal

def probabilityAnchoredPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h : ℝ) (n N : ℕ) (s : ProbabilityNode T h n) :
    Point d → ProbabilityNode T h n → Point d :=
  nodes (reanchorWeight (probabilityWeight T h n) s)
    (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j)) (fun y _ => y) N

lemma probabilityAnchored_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h : ℝ},0≤r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h →
        A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s : ProbabilityNode T h n,
      LipschitzWith 2 (probabilityAnchoredPicard F x r T h n N s) ∧
      LipschitzWith (2*(A*probabilityMeanLipschitz lam r))
        (fun y => probabilityAnchoredPicard F x r T h n (N+1) s y-(fun _ => y)) := by
  obtain ⟨A,hA,hA'⟩ := probabilityWeight_budget n hn
  refine ⟨⟨2*A,by positivity⟩,?_⟩
  intro d F lam hF x r T h hr hl hT0 hT1 hh hq N s
  have hφ (j : ProbabilityNode T h n) := probabilityMeanVelocity_lipschitz hF x hr hl
    (probabilityNodeTime_mem hT0 hT1 hh hn j).1
    ((probabilityNodeTime_mem hT0 hT1 hh hn j).2.trans_lt hT1)
  have hw := reanchorWeight_budget (probabilityWeight T h n) (hA' hT0 hT1 hh) s
  constructor
  · simpa only [probabilityAnchoredPicard,mul_one] using
      nodes_lipschitz (A:=⟨2*A,by positivity⟩) _ _ (fun y : Point d => fun _ => y) hw hφ
        (probabilityConstantPath_lipschitz T h n) hq N
  · simpa only [probabilityAnchoredPicard,mul_one,one_mul,mul_comm] using
      nodes_correction_lipschitz (A:=⟨2*A,by positivity⟩) _ _ (fun y : Point d => fun _ => y) hw hφ
        (probabilityConstantPath_lipschitz T h n) hq N

theorem probabilityAnchored_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀{T h : ℝ},0<T → T<1 → 0<h → h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀s i : ProbabilityNode T h n,
      Integrable (fun z => ‖probabilityAnchoredPicard F x r T h n N s
          (fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n s) z) i-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n i) z‖^2) (stdGaussian (Point d)) ∧
      (∫z,‖probabilityAnchoredPicard F x r T h n N s
          (fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n s) z) i-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n i) z‖^2 ∂stdGaussian (Point d))≤
        (4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)+
          (A*probabilityMeanLipschitz lam r:ℝ≥0)^N*(2*probabilityInitialRms F x lam r))^2 := by
  obtain ⟨A,hA,hA'⟩ := probabilityWeight_budget n hn
  obtain ⟨C,hC,k,hk⟩ := probability_mean_defect_rms n hn
  refine ⟨⟨2*A,by positivity⟩,C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd T h hT0 hT1 hh hsmall hq N s i
  have hi (j : ProbabilityNode T h n) := probabilityNodeTime_mem hT0 hT1 hh hn j
  have hi' (j : ProbabilityNode T h n) : probabilityNodeTime T h n j∈Icc (0:ℝ) 1 :=
    ⟨(hi j).1,(hi j).2.trans hT1.le⟩
  let e := fun j : ProbabilityNode T h n => fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n j)
  let φ := fun j : ProbabilityNode T h n => probabilityMeanVelocity F x r (probabilityNodeTime T h n j)
  let D := C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1)
  have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) d; linarith)
  have hD : 0≤D := by dsimp [D]; positivity
  have hφ (j : ProbabilityNode T h n) := probabilityMeanVelocity_lipschitz hF x hr.le hl
    (hi j).1 ((hi j).2.trans_lt hT1)
  have hd0 (j : ProbabilityNode T h n) :
      Integrable (fun z => ‖step (probabilityWeight T h n) φ (fun _ => z) (fun j => e j z) j-e j z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖step (probabilityWeight T h n) φ (fun _ => z) (fun j => e j z) j-e j z‖^2
        ∂stdGaussian (Point d))≤D^2 := by
    dsimp only [φ,e]
    simp_rw [probabilityPicard_exact_defect hF x hr.le hl hT0 hT1 hh n hn,
      norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow]
    refine ⟨(hk hF x hr hlam hl hd hT0 hT1 hh hsmall j).1.const_mul (r^2),?_⟩
    rw [integral_const_mul]
    convert mul_le_mul_of_nonneg_left (hk hF x hr hlam hl hd hT0 hT1 hh hsmall j).2 (sq_nonneg r) using 1;
      first | rfl | (dsimp [D]; ring)
  have hdef (j : ProbabilityNode T h n) :
      (∫z,‖step (reanchorWeight (probabilityWeight T h n) s) φ (fun _ => e s z)
        (fun j => e j z) j-e j z‖^2 ∂stdGaussian (Point d))≤(2*D)^2 := by
    have heq (z : Point d) := step_reanchor_defect (probabilityWeight T h n) φ (fun j => e j z) z s j
    simp_rw [heq]
    exact (integral_norm_sub_sq_bound _ _ _ (hd0 j).1 (hd0 s).1 (hd0 j).2 (hd0 s).2).trans (by ring_nf; rfl)
  have hinit (j : ProbabilityNode T h n) :
      (∫z,‖e s z-e j z‖^2 ∂stdGaussian (Point d))≤(2*probabilityInitialRms F x lam r)^2 := by
    have hj := probabilityFlow_initial_rms hF x hr.le hl (hi' j)
    have hs := probabilityFlow_initial_rms hF x hr.le hl (hi' s)
    rw [←probabilityInitialRms_sq] at hj hs
    have heq (z : Point d) : e s z-e j z=(z-e j z)-(z-e s z) := by abel
    simp_rw [heq]
    exact (integral_norm_sub_sq_bound _ _ _ hj.1 hs.1 hj.2 hs.2).trans (by ring_nf; rfl)
  have he := nodes_rms (ν:=stdGaussian (Point d)) (A:=⟨2*A,by positivity⟩)
    (reanchorWeight (probabilityWeight T h n) s) φ hφ (fun _ => e s) e
    (fun _ => gaussian_lipschitz_memLp (fullProbabilityFlow_lipschitz hF x hr.le hl (hi' s)))
    (fun j => gaussian_lipschitz_memLp (fullProbabilityFlow_lipschitz hF x hr.le hl (hi' j)))
    (reanchorWeight_budget (probabilityWeight T h n) (hA' hT0 hT1 hh) s) hq
    (show 0≤2*D by positivity) (show 0≤2*probabilityInitialRms F x lam r by
      exact mul_nonneg (by norm_num) (probabilityInitialRms_nonneg F x lam r)) hdef hinit N i
  have heq : 2*(2*D)=4*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*h)^(n+1) := by
    dsimp [D]; ring
  rw [heq] at he
  simpa only [probabilityAnchoredPicard,nodes_eq_iterate,φ,e] using he
end LogConcaveSampling

end

end

end

end OAI
