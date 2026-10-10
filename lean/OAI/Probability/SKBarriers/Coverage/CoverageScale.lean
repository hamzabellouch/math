import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageTheorem

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem stretchedLogScale_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^kappa) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num [kappa])).comp tendsto_natCast_atTop_atTop

theorem stretchedLogScale_sublinear :
    Tendsto (fun n : ℕ => (n:ℝ)^kappa/(n:ℝ)) atTop (𝓝 0) := by
  have H := (tendsto_rpow_neg_atTop (by norm_num [kappa] : 0 < 1-kappa)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply H.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  change (n:ℝ)^(-(1-kappa)) = (n:ℝ)^kappa/(n:ℝ)
  rw [show -(1-kappa) = kappa-1 by ring,Real.rpow_sub hn',Real.rpow_one]

theorem stretched_uniform_coverage {β : ℝ} (hβ : 1 < β) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ D : ℝ, 0 < D → ∃ D₃ : ℝ, 0 < D₃ ∧
      ∃ C : (n : ℕ) → Set (Disorder n), (∀ n, MeasurableSet (C n)) ∧
        Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
        ∀ n J, J ∈ C n → ∀ S : Finset (Config n),
          finiteMass (gibbs β J) (S.filter (fun x =>
            finiteMass (gibbs β J) (S.filter (fun y => q ≤ |overlap x y|)) <
              Real.exp (-D₃*((n:ℝ)^kappa)))) < Real.exp (-D*((n:ℝ)^kappa)) :=
  uniform_coverage hβ (fun n => (n:ℝ)^kappa) stretchedLogScale_tendsto stretchedLogScale_sublinear

end SK.Analytic

end
end

end

end OAI
