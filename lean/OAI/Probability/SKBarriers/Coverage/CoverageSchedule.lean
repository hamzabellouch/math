import Mathlib
import OAI.Probability.SKBarriers.Coverage.FiniteCoverage
import OAI.Probability.SKBarriers.Dynamics.GreedyNumerics
import OAI.Probability.SKBarriers.Dynamics.BankCardinality

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

 theorem gibbs_prob_eq_finiteMass {n : ℕ} (β : ℝ) (J : Disorder n) (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob E=finiteMass (gibbs β J) (Finset.univ.filter E) := by
  unfold FiniteLaw.prob FiniteLaw.expect gibbsFiniteLaw finiteMass
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_filter]

 theorem gibbs_coverage_predicate {n : ℕ} (β : ℝ) (J : Disorder n) (q a δ : ℝ)
    (h : ∀ S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
      finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<a))<δ)
    (E : Config n → Prop) :
    (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<a)≤δ := by
  have H := h (Finset.univ.filter E)
  simp_rw [Finset.filter_filter] at H
  refine le_trans ?_ H.le
  apply le_of_eq
  rw [gibbs_prob_eq_finiteMass]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,gibbs_prob_eq_finiteMass]
  apply and_congr_right
  intro _
  apply Iff.of_eq
  apply congrArg (fun r : ℝ => r<a)
  apply congrArg (finiteMass (gibbs β J))
  ext y
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]

def coveragePrefix (f : ℝ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => coveragePrefix f j+f (coveragePrefix f j+5)+2

 theorem coveragePrefix_nonneg (f : ℝ → ℝ) (hf : ∀x,0<f x) (j : ℕ) : 0≤coveragePrefix f j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => simp only [coveragePrefix]; linarith only [ih,hf (coveragePrefix f j+5)]

 theorem bankPrefix_coverage (f : ℝ → ℝ) (j : ℕ) :
    bankPrefix (fun j => f (coveragePrefix f j+5)) j=coveragePrefix f j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [bankPrefix,coveragePrefix,ih]

 theorem exists_coverage_schedule (β q : ℝ)
    (h : ∀D : ℝ,0<D → ∃c : ℝ,0<c ∧ ∃C : (n : ℕ) → Set (Disorder n),
      (∀n,MeasurableSet (C n)) ∧ Tendsto (fun n => (disorderLaw n).real (C n)) atTop (𝓝 1) ∧
      ∀n J,J∈C n → ∀S : Finset (Config n),finiteMass (gibbs β J) (S.filter (fun x =>
        finiteMass (gibbs β J) (S.filter (fun y => q≤|overlap x y|))<Real.exp (-c*levelLogScale n)))<Real.exp (-D*levelLogScale n)) :
    ∃c : ℕ → ℝ, (∀j,0<c j) ∧ ∃C : ℕ → (n : ℕ) → Set (Disorder n),
      (∀j n,MeasurableSet (C j n)) ∧
      (∀j,Tendsto (fun n => (disorderLaw n).real (C j n)) atTop (𝓝 1)) ∧
      ∀j n J,J∈C j n → ∀E : Config n → Prop,
        (gibbsFiniteLaw β J).prob (fun x => E x ∧ (gibbsFiniteLaw β J).prob (fun y => E y ∧ q≤|overlap x y|)<Real.exp (-c j*levelLogScale n))≤
          Real.exp (-(bankPrefix c j+5)*levelLogScale n) := by
  choose f hf C hC hC1 hcov using (fun D : ℝ => h (max D 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
  let c : ℕ → ℝ := fun j => f (coveragePrefix f j+5)
  refine ⟨c,fun j => hf _,fun j => C (coveragePrefix f j+5),fun j n => hC _ n,fun j => hC1 _,?_⟩
  intro j n J hJ E
  have HD : max (coveragePrefix f j+5) 1=coveragePrefix f j+5 := max_eq_left (by linarith only [coveragePrefix_nonneg f hf j])
  have H := gibbs_coverage_predicate β J q _ _ (hcov (coveragePrefix f j+5) n J hJ) E
  simpa only [HD,c,bankPrefix_coverage] using H

end SK.Analytic

end
end

end OAI
