import OAI.Probability.FreeIsing.Ising.CopyPathVariance
import OAI.Probability.FreeIsing.Ising.CopyProductVariance

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopySpectral
open IsingObservationInnovation IsingObservationFactor ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def pathCavityProduct (hbeta : 0 ≤ beta) (t : ℝ≥0) (g : TreeAut d)
    (v : TreeVertex d) (reverse : Bool) (x : Paths d) : ℝ :=
  ∏ i : Fin v.1.length, responseAttenuation (Real.tanh beta)
    (cavityObservable hbeta t
      (g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1)))
      (g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))) x)

def pathCavityLogSum (hbeta : 0 ≤ beta) (t : ℝ≥0) (g : TreeAut d)
    (v : TreeVertex d) (reverse : Bool) (q : Paths d × (Paths d × Paths d)) : ℝ :=
  ∑ i : Fin v.1.length, cavityLogDifference hbeta t
    (g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1)))
    (g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))) q

theorem exists_cavityProduct_path_variance_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hbeta : 0 ≤ beta)
    (hthreshold : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w →
      ∀ (g : TreeAut d) (v : TreeVertex d) (reverse : Bool),
      (∫ q, (pathCavityProduct hbeta t g v reverse q.2.1 -
          pathCavityProduct hbeta t g v reverse q.2.2) ^ 2 ∂copies beta μ) ≤
        C * v.1.length * ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ ∧
      (∫ q, ((pathCavityProduct hbeta t g v reverse q.2.1) ^ 2 +
          (pathCavityProduct hbeta t g v reverse q.2.2) ^ 2) *
          (pathCavityLogSum hbeta t g v reverse q) ^ 2 ∂copies beta μ) ≤
        C * v.1.length * ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
  obtain ⟨C, hC, hpath⟩ := exists_cavityLog_path_variance_bound hμ hd hbeta hthreshold
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro t u w huw g v reverse
  have hlog : (∫ q, (pathCavityLogSum hbeta t g v reverse q) ^ 2 ∂copies beta μ) ≤
      C * v.1.length * ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
    cases reverse with
    | false => simpa only [pathCavityLogSum, Bool.false_eq_true, ↓reduceIte] using
        (hpath t u w huw g v).1
    | true => simpa only [pathCavityLogSum, ↓reduceIte] using
        (hpath t u w huw g v).2
  have hscale := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)
  have hscale' : 2 * (∫ q, (pathCavityLogSum hbeta t g v reverse q) ^ 2 ∂copies beta μ) ≤
      (2 * C) * v.1.length *
        ∫ q, (cavityLogDifference hbeta t u w q) ^ 2 ∂copies beta μ := by
    simpa only [mul_assoc] using hscale
  let a := fun i : Fin v.1.length =>
    g.toEquiv (takeVertex v (if reverse then i.1 + 1 else i.1))
  let b := fun i : Fin v.1.length =>
    g.toEquiv (takeVertex v (if reverse then i.1 else i.1 + 1))
  constructor
  · exact (integral_cavityProduct_sub_sq_le_twice_log_sum Finset.univ a b hμ hbeta t).trans hscale'
  · exact (integral_cavityProduct_log_sq_le_twice_unweighted Finset.univ a b hμ hbeta t).trans hscale'

end Problem367.IsingCopySpectral

end

end OAI
