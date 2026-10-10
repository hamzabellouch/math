import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoupledResolve

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

def run (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) : ℕ → ℕ → State V → Output V
  | _q,0,s => finish s.B s.lam s.P []
  | q,n+1,s => match step loc distance F v M N precision q n k s with
    | .inl o => o
    | .inr t => run loc distance F v M N precision k (q+1) n t

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma run_correct (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ))
    (q n : ℕ) (s : State V) (h : Certified loc F v eta lo hi q n k s) :
    (run loc distance F v M N precision k q n s).Correct loc F v eta lo hi (q+n) k := by
  induction n generalizing q s with
  | zero => exact h.zero_false.elim
  | succ n ih =>
    have hs:=step_correct loc distance hmetric F v M eta lo hi N precision q n k s h
      hF hM hN hv hv1 hlo heta hhi hprecision hdiam
    rw [run]
    cases he : step loc distance F v M N precision q n k s with
    | inl o =>
      rw [he] at hs
      exact hs
    | inr t =>
      rw [he] at hs
      have hh := ih (q+1) t hs
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 n] using hh

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
