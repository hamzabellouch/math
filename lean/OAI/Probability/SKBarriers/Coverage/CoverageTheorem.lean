import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageLimit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

theorem uniform_coverage {β : ℝ} (hβ : 1 < β) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsub : Tendsto (fun n => L n/(n:ℝ)) atTop (𝓝 0)) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ D : ℝ, 0 < D → ∃ D₃ : ℝ, 0 < D₃ ∧
      ∃ C : (n : ℕ) → Set (Disorder n), (∀ n, MeasurableSet (C n)) ∧
        Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
        ∀ n J, J ∈ C n → ∀ S : Finset (Config n),
          finiteMass (gibbs β J) (S.filter (fun x =>
            finiteMass (gibbs β J) (S.filter (fun y => q ≤ |overlap x y|)) <
              Real.exp (-D₃*L n))) < Real.exp (-D*L n) := by
  obtain ⟨q,hq,hq1,H⟩ := uniform_coverage_pair hβ L hL hsub
  refine ⟨q,hq,hq1,?_⟩
  intro D hD
  obtain ⟨D₂,hD₂,hlim⟩ := H D hD
  let C (n : ℕ) := (coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q)ᶜ
  have hm (n : ℕ) := measurableSet_coveragePairBad n β (Real.exp (-D*L n)) (Real.exp (-D₂*L n)) q
  refine ⟨D+D₂,add_pos hD hD₂,C,(fun n => (hm n).compl),?_,?_⟩
  · have Hlim := (tendsto_const_nhds (x := (1:ℝ))).sub hlim
    simp only [sub_zero] at Hlim
    convert Hlim using 1
    funext n
    dsimp only [C]
    rw [measureReal_compl (hm n),probReal_univ]
  · intro n J hJ S
    have hpair (T : Finset (Config n)) (hT : Real.exp (-D*L n) ≤ finiteMass (gibbs β J) T) :
        Real.exp (-D₂*L n) ≤ weightedOverlapMass (conditionalWeights (gibbs β J) T) q := by
      have hraw : Real.exp (-D₂*L n)*(finiteMass (gibbs β J) T)^2 ≤
          finiteOverlapMass (gibbs β J) T q := by
        apply le_of_not_gt
        intro hbad
        exact hJ ⟨T,hT,hbad⟩
      rw [weightedOverlapMass_conditional]
      exact (le_div_iff₀ (sq_pos_of_pos ((Real.exp_pos _).trans_le hT))).mpr hraw
    have Hcov := finite_coverage_of_pair_bound (gibbs β J) (fun x => (gibbs_pos β J x).le)
      (Real.exp_pos (-D*L n)) (Real.exp_nonneg (-D₂*L n)) hpair S
    have heq : Real.exp (-D*L n)*Real.exp (-D₂*L n) = Real.exp (-(D+D₂)*L n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq] at Hcov

end SK.Analytic

end
end

end

end OAI
