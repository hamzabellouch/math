import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixMultiplierGap
import OAI.Probability.SKBarriers.Replicas.PairEndpoint
import OAI.Probability.SKBarriers.Replicas.PairPenalty

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem pairConstrainedPressure_finite {N : ℕ} (hN : 0<N) (a b : ℕ) (β : ℝ)
    (m c : Fin (a+b+1) → ℝ) (hm0 : m 0=0) (hm : ∀ i, m i∈Icc (0:ℝ) 1)
    (hmono : Monotone m) (hc : ∑ i, (c i)^2=1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 (∑ i, if i.val<a then (c i)^2 else 0)))) :
    let q := ∑ i, if i.val<a then (c i)^2 else 0
    matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2*(scalarHierarchy (a+b+1) m (fun i => β*c i) scalarSpinTerminal 0-
        β^2/4*∑ i : Fin (a+b), m i.succ*
          ((finitePrefix (fun l => (c l)^2) i.succ)^2-(finitePrefix (fun l => (c l)^2) i.castSucc)^2))-
      (scalarMomentSquare (a+b+1) m (fun i => β*c i) scalarSpinTerminal scalarMagnetization ⟨a,by omega⟩ 0-q)^2/2 := by
  dsimp only
  have H := matrixConstrainedPressure_quadratic_gap hN (by norm_num : 0<2) β _ pairMultiplier hD
    (splitPairFactor a c) (zeroInitialAtoms (a+b) (splitPairMass a m))
    (zeroInitialAtoms_nonneg _ (splitPairMass_mem a m hm) (splitPairMass_mono a m (fun i => (hm i).1) hmono))
    (zeroInitialAtoms_sum _) (by intro s; rw [pairMultiplier_observable]; exact pairSpinObservable_bound s)
  dsimp only at H
  rw [pairSiteValue a b β m c hm0,pairSiteObservable a b β m c hm0,pairMultiplier_inner] at H
  have HP := splitPairFactor_penalty a m c
  rw [splitPairFactor_last a c hc] at HP
  rw [splitPairFactor_last a c hc] at H
  rw [HP] at H
  convert H using 1
  ring

end SK.Analytic

end
end

end OAI
