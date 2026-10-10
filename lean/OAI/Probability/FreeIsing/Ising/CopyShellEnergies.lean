import OAI.Probability.FreeIsing.Ising.CopyProductPathBound
import OAI.Probability.FreeIsing.Ising.CopyResponseRowPaths
import OAI.Probability.FreeIsing.Trees.WeightedPathSummation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367

def nonnegativeShellSup {d : ℕ} (F : TreeVertex d → ℝ) (n : ℕ) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun v : Option (TreeShell d n) => v.elim 0 (fun v => F v))

theorem nonnegativeShellSup_nonneg {d : ℕ} (F : TreeVertex d → ℝ) (n : ℕ) :
    0 ≤ nonnegativeShellSup F n := by
  classical
  exact Finset.le_sup' (fun v : Option (TreeShell d n) => v.elim 0 (fun v => F v))
    (Finset.mem_univ none)

theorem le_nonnegativeShellSup {d : ℕ} (F : TreeVertex d → ℝ)
    (v : TreeVertex d) : F v ≤ nonnegativeShellSup F v.1.length := by
  classical
  exact Finset.le_sup' (fun w : Option (TreeShell d v.1.length) => w.elim 0 (fun w => F w))
    (Finset.mem_univ (some ⟨v, rfl⟩))

theorem nonnegativeShellSup_le {d n : ℕ} {F : TreeVertex d → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ v, v.1.length = n → F v ≤ C) :
    nonnegativeShellSup F n ≤ C := by
  classical
  apply Finset.sup'_le
  intro v _
  cases v with
  | none => exact hC
  | some v => exact hF v v.property

namespace IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingConditionalCopyBounds ConnectedHull ResponseRows IsingCopyStationarity

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def noiseShellEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (n : ℕ) : ℝ :=
  nonnegativeShellSup (noiseEnergy (μ := μ) hb t) n

def linearShellEnergy (hb : 0 ≤ beta) (t : ℝ≥0) (n : ℕ) : ℝ :=
  nonnegativeShellSup (linearEnergy (μ := μ) hb t) n

theorem pathCavityProduct_eq_pathProduct (hb : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (x : Paths d) :
    pathCavityProduct hb t (TreeAut.refl d) v true x =
      pathProduct (Real.tanh beta) (Finset.range v.1.length) (pathCavity hb t v) x := by
  simp only [pathCavityProduct, TreeAut.refl, Equiv.refl_apply, ↓reduceIte,
    pathProduct, pathCavity]
  exact Fin.prod_univ_eq_prod_range (fun i : ℕ => responseAttenuation (Real.tanh beta)
    (cavityObservable hb t (takeVertex v (i + 1)) (takeVertex v i) x)) v.1.length

theorem pathCavityLogSum_eq_pathLogDiff (hb : 0 ≤ beta) (t : ℝ≥0)
    (v : TreeVertex d) (q : CopySpace d) :
    pathCavityLogSum hb t (TreeAut.refl d) v true q =
      pathLogDiff (Real.tanh beta) (Finset.range v.1.length)
        (fun i q => pathCavity hb t v i q.2.1)
        (fun i q => pathCavity hb t v i q.2.2) q := by
  simp only [pathCavityLogSum, TreeAut.refl, Equiv.refl_apply, ↓reduceIte,
    pathLogDiff, pathCavity, cavityLogDifference, cavityLogObservable]
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    Real.log (responseAttenuation (Real.tanh beta)
      (cavityObservable hb t (takeVertex v (i + 1)) (takeVertex v i) q.2.1)) -
    Real.log (responseAttenuation (Real.tanh beta)
      (cavityObservable hb t (takeVertex v (i + 1)) (takeVertex v i) q.2.2))) v.1.length

theorem linearEnergy_le_siteVariance
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    linearEnergy (μ := μ) hb t v ≤
      ∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have hU : MemLp (fieldDifference beta (root d) t) 2 (copies beta μ) :=
    ((memLp_field_at hμ hb t _).comp_measurePreserving hl).sub
      ((memLp_field_at hμ hb t _).comp_measurePreserving hr)
  exact (integral_mul_prod_responseAttenuation_sq_le (Finset.range v.1.length)
    (Real.tanh_sq_lt_one beta).le
    (fun i _ => (measurable_cavityObservable hb t _ _).comp hl.measurable) hU).2

theorem exists_short_shell_energy_bounds
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w → ∀ n : ℕ,
      noiseShellEnergy (μ := μ) hb t n ≤
        A * (∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ) * n ∧
      linearShellEnergy (μ := μ) hb t n ≤
        A * (∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ) := by
  obtain ⟨C, hC, hbound⟩ := exists_cavityProduct_path_variance_bound hμ hd hb hcrit
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro t u w huw n
  have hS : 0 ≤ ∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hV : 0 ≤ ∫ q, (fieldDifference beta (root d) t q) ^ 2 ∂copies beta μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  constructor
  · apply nonnegativeShellSup_le (by positivity)
    intro v hv
    have hpath := (hbound t u w huw (TreeAut.refl d) v true).2
    simp_rw [pathCavityProduct_eq_pathProduct, pathCavityLogSum_eq_pathLogDiff] at hpath
    change noiseEnergy (μ := μ) hb t v ≤ _ at hpath
    calc
      _ ≤ C * (v.1.length : ℝ) * (∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ) := hpath
      _ = C * (∫ q, (cavityLogDifference hb t u w q) ^ 2 ∂copies beta μ) * n := by rw [hv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 C) hS) (Nat.cast_nonneg n)
  · apply nonnegativeShellSup_le (by positivity)
    intro v _
    exact (linearEnergy_le_siteVariance hμ hb t v).trans
      (le_mul_of_one_le_left hV (le_max_left _ _))

end IsingCopyResponseRowPaths
end Problem367

end

end OAI
