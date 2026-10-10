import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductBoundary

namespace OAI

/-! # Continuity sets for prescribed prime bins and product bounds -/
namespace JointDickman
open Finset Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem null_frontier_finset_inter {Ω ι : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, μ (frontier (E i)) = 0) :
    μ (frontier (⋂ i ∈ s, E i)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [mem_insert, forall_eq_or_imp] at hE
    rw [show (⋂ j ∈ insert i s, E j) = E i ∩ ⋂ j ∈ s, E j by ext x; simp]
    exact null_frontier_inter hE.1 (ih hE.2)

theorem pi_box_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (h : ℕ) (a b : Fin h → ℝ) :
    (Measure.pi (fun _ : Fin h => μ))
      (frontier (Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)))) = 0 := by
  have hsingle (i : Fin h) : μ (frontier (Set.Ioc (a i) (b i))) = 0 := by
    by_cases hab : a i < b i
    · rw [frontier_Ioc hab]
      exact Set.Countable.measure_zero (Set.Finite.countable (Set.toFinite ({a i, b i} : Set ℝ))) μ
    · rw [Set.Ioc_eq_empty_of_le (le_of_not_gt hab)]
      simp
  have hi (i : Fin h) : (Measure.pi (fun _ : Fin h => μ))
      (frontier ((fun t : Fin h → ℝ => t i) ⁻¹' Set.Ioc (a i) (b i))) = 0 := by
    apply measure_mono_null ((continuous_apply i).frontier_preimage_subset _) _
    exact Measure.pi_eval_preimage_null _ (hsingle i)
  have he : Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)) =
      ⋂ i ∈ (univ : Finset (Fin h)), (fun t : Fin h → ℝ => t i) ⁻¹' Set.Ioc (a i) (b i) := by
    ext t
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_iInter, mem_univ,
      Set.mem_preimage]
  rw [he]
  exact null_frontier_finset_inter _ _ _ (fun i _ => hi i)

noncomputable def primeBoxCutoff (h : ℕ) (a b : Fin h → ℝ) (u : ℝ) : Set (Fin h → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (a i) (b i)) ∩ {t | ∑ i, t i ≤ u}

theorem primeBoxCutoff_null_frontier (μ : Measure ℝ) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    (Measure.pi (fun _ : Fin (n+1) => μ)) (frontier (primeBoxCutoff (n+1) a b u)) = 0 :=
  null_frontier_inter (pi_box_null_frontier μ (n+1) a b) (pi_sum_sublevel_null_frontier μ n u)

theorem primeLogProduct_box_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (n : ℕ) (a b : Fin (n+1) → ℝ) (u : ℝ) :
    Tendsto (fun x => ((FiniteMeasure.pi (fun _ : Fin (n+1) => primeLogMeasure c x))
      (primeBoxCutoff (n+1) a b u) : ℝ)) atTop
      (𝓝 ((FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c))
        (primeBoxCutoff (n+1) a b u) : ℝ)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have he := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at he
    linarith [Real.log_neg hc hc1]
  have hne : (FiniteMeasure.pi (fun _ : Fin (n+1) => logarithmicPrimeMeasure c)) ≠ 0 := by
    apply (FiniteMeasure.mass_nonzero_iff _).mp
    rw [FiniteMeasure.mass_pi]
    exact prod_ne_zero_iff.mpr (fun _ _ => hm0)
  apply NNReal.tendsto_coe.mpr
  apply finiteMeasure_set_tendsto (primeLogProduct_tendsto hc hc1 (n+1)) hne
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  exact primeBoxCutoff_null_frontier _ n a b u

end JointDickman

end OAI
