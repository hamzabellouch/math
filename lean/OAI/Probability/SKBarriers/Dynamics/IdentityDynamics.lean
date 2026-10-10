import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ClockEndpoint
import OAI.Probability.SKBarriers.Dynamics.GreedyEventual
import OAI.Probability.SKBarriers.Dynamics.BankNumerics
import OAI.Probability.SKBarriers.Dynamics.BankDynamics

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def bankEndpointError (n : ℕ) : ℝ :=
  4*(9*Real.exp (-2*levelLogScale n)+(n:ℝ)*Real.exp (-levelLogScale n))

 theorem scheduled_bank_total {n p B : ℕ} (hB : 0<B) (c : ℕ → ℝ) (hc : ∀j,0≤c j)
    (hL : 5≤levelLogScale n) (hp : (p:ℝ)≤Real.exp (levelLogScale n))
    (hdom : (bankPrefix c B+5)*levelLogScale n≤Real.exp (levelLogScale n))
    {v : ℝ} (hv0 : 0≤v) (hv : v≤Real.exp (-(3*bankPrefix c B+20)*levelLogScale n)) :
    (8*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^3+
      48*(Fintype.card (BankIndex (scheduledBankSize c B n (p:=p))):ℝ)^2)*v+
    (∑j : Fin p,(Fintype.card (BankTuple (scheduledBankSize c B n) (blockPrior p B) j):ℝ)*
      (Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n)+
        Real.exp (-(Real.exp (-c (j.val%B)*levelLogScale n))*(scheduledBankSize c B n j))))≤
      3*Real.exp (-4*levelLogScale n) := by
  have HL := scheduled_bank_locking_cost hB c hc hL hp hv0 hv
  have HC := scheduled_bank_coverage_sum (p:=p) hB c hc (by linarith only [hL]) hdom
  have HP : 2*(p:ℝ)*Real.exp (-5*levelLogScale n)≤2*Real.exp (-4*levelLogScale n) := by
    calc
      _ ≤ 2*Real.exp (levelLogScale n)*Real.exp (-5*levelLogScale n) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  linarith only [HL,HC,HP]

 theorem identity_quenched_bound {n B H : ℕ} (hn : 0<n) (hB : 0<B)
    (β : ℝ) (J : Disorder n) (μ : ProbabilityMeasure ℝ) (t b b' q : ℝ)
    (c : ℕ → ℝ) (hc : ∀j,0≤c j)
    (hcov : ∀j<B,∀E : Config n → Prop,
      (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<Real.exp (-c j*levelLogScale n))≤
        Real.exp (-(bankPrefix c j+5)*levelLogScale n))
    (hv : replicaGibbsMass β J (lockingUnion n μ t (levelRho n) q b b')≤Real.exp (-(3*bankPrefix c B+20)*levelLogScale n))
    (hL : 5≤levelLogScale n)
    (hp : (B*greedyBlockCount B t n:ℕ)≤Real.exp (levelLogScale n))
    (hdom : (bankPrefix c B+5)*levelLogScale n≤Real.exp (levelLogScale n))
    (hsmall : 3*Real.exp (-4*levelLogScale n)<1)
    (G : GreedyScaleBounds n B H (B*greedyBlockCount B t n) t (levelRho n) (2/(n:ℝ)) b b' q)
    (hcount : ∀m≤⌈Real.exp (2*levelLogScale n)⌉₊,
      (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4)+
        (m+1)*(2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ))^(greedyBlockCount B t n)<1) :
    continuousMixedMass β J (timeScale n)≤bankEndpointError n ∧
      discreteMixedMass β J ⌊timeScale n⌋₊≤bankEndpointError n := by
  let p := B*greedyBlockCount B t n
  let K : Fin p → ℕ := scheduledBankSize c B n
  let a : Fin p → ℝ := fun j => Real.exp (-c (j.val%B)*levelLogScale n)
  let δ : Fin p → ℝ := fun j => Real.exp (-(bankPrefix c (j.val%B)+5)*levelLogScale n)
  let S := lockingUnion n μ t (levelRho n) q b b'
  have hK : ∀j,0<K j := scheduledBankSize_pos c B n
  obtain ⟨z,hz,hzmass⟩ := exists_fixed_good_bank β J K (blockPrior p B) (blockPrior_not_self p B) t q a δ
    (fun j => (Real.exp_pos _).le) S (fun j w => hcov (j.val%B) (Nat.mod_lt _ hB) (fun x => ∀i,|overlap (w i) x|≤3*t))
    (3*Real.exp (-4*levelLogScale n))
    (scheduled_bank_total hB c hc hL hp hdom (replicaGibbsMass_nonneg β J S) hv) hsmall
  let v := initialBankReference (natBankPool K z) (natBankDefault K hK z) B t q
  have HC : ∀m≤⌈Real.exp (2*levelLogScale n)⌉₊,
      (∑x,gibbs β J x*kernelEvent β J (fun y => overlap (v x) y≤0) m x)≤9*Real.exp (-2*levelLogScale n) := by
    intro m hm
    have HM := bank_stationary_crossing hn β J μ B H (greedyBlockCount B t n) m t (levelRho n) b b' q G (by simpa only [Nat.cast_mul] using hcount m hm) K hK z hz
    have HK : (m:ℝ)+1≤3*Real.exp (2*levelLogScale n) := by
      have hi : (m:ℝ)≤(⌈Real.exp (2*levelLogScale n)⌉₊:ℝ) := by exact_mod_cast hm
      exact (add_le_add hi (le_refl (1:ℝ))).trans (horizon_size_bound (by linarith only [hL]))
    change _≤((m:ℝ)+1)*(gibbsFiniteLaw β J).prob (fun x => bankCoverageBad K (blockPrior p B) t q z x ∨ bankVertexBad (fun i : BankIndex K => i.1.val) S z x) at HM
    refine HM.trans ?_
    calc
      _ ≤ (3*Real.exp (2*levelLogScale n))*(3*Real.exp (-4*levelLogScale n)) :=
        mul_le_mul HK hzmass ((gibbsFiniteLaw β J).prob_nonneg _) (by positivity)
      _ = _ := by rw [mul_mul_mul_comm,← Real.exp_add]; norm_num; ring
  have HH := mixedMass_bounds_of_crossing hn β J (levelLogScale n) (9*Real.exp (-2*levelLogScale n)) (by linarith only [hL]) (by positivity) v HC
  refine ⟨HH.1,HH.2.trans ?_⟩
  dsimp only [bankEndpointError]
  have hp0 : 0≤(n:ℝ)*Real.exp (-levelLogScale n) := by positivity
  linarith only [hp0]

end SK.Analytic

end
end

end OAI
