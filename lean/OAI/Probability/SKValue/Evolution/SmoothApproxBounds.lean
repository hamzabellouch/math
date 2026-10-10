import Mathlib
import OAI.Probability.SKValue.Evolution.GridConvergence
import OAI.Probability.SKValue.Evolution.HeatTimeBound
import OAI.Probability.SKValue.Evolution.DerivativeLimit

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma smoothApprox_bulk_jets (γ : OrderParameter) {S : ℝ} (hS : S∈Ico (0 : ℝ) 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n t, t∈Icc (0 : ℝ) S → ∀ k ≤ m, ∀ x,
      |iteratedDeriv k (deriv (smoothApprox γ n t)) x| ≤ C := by
  let T := (S+1)/2
  have hST : S<T := by dsimp only [T]; linarith [hS.2]
  have hT1 : T<1 := by dsimp only [T]; linarith [hS.2]
  have hT : T∈Ico (0 : ℝ) 1 := ⟨hS.1.trans hST.le,hT1⟩
  obtain ⟨C,hC,hb⟩ := uniform_bulk_jets (γ.coeff T) (γ.nonneg _ hT) T m S hS.1 hST
  refine ⟨C,hC,?_⟩
  intro n t ht k hk x
  exact hb (profileCoeff (γ.grid n)) (smoothApprox γ n)
    ((smoothApprox_evolution γ n).restrict hT1.le) (profileCoeff_measurable _)
    ((profileCoeff_mono (γ.grid_mono n)).mono (by rw [γ.grid_time]; exact Icc_subset_Icc le_rfl hT1.le))
    (fun r hr ↦ by
      rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
      exact (γ.grid_le n ⟨hr.1,hr.2.trans_lt hT1⟩).trans
        (γ.monotone ⟨hr.1,hr.2.trans_lt hT1⟩ hT hr.2)) t ht k hk x

lemma smoothApprox_bulk_temporal (γ : OrderParameter) {S : ℝ} (hS : S∈Ico (0 : ℝ) 1) (m : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ n s, s∈Icc (0 : ℝ) S → ∀ t∈Icc (0 : ℝ) S, ∀ x,
      |iteratedDeriv m (deriv (smoothApprox γ n s)) x-
        iteratedDeriv m (deriv (smoothApprox γ n t)) x| ≤ L*|s-t| := by
  let T := (S+1)/2
  have hST : S<T := by dsimp only [T]; linarith [hS.2]
  have hT1 : T<1 := by dsimp only [T]; linarith [hS.2]
  have hT : T∈Ico (0 : ℝ) 1 := ⟨hS.1.trans hST.le,hT1⟩
  obtain ⟨L,hL,hb⟩ := uniform_bulk_temporal (γ.coeff T) (γ.nonneg _ hT) T m hS.1 hST
  refine ⟨L,hL,?_⟩
  intro n s hs t ht x
  exact hb (profileCoeff (γ.grid n)) (smoothApprox γ n)
    ((smoothApprox_evolution γ n).restrict hT1.le) (profileCoeff_measurable _)
    ((profileCoeff_mono (γ.grid_mono n)).mono (by rw [γ.grid_time]; exact Icc_subset_Icc le_rfl hT1.le))
    (fun r hr ↦ by
      rw [abs_of_nonneg (profileCoeff_nonneg _ _)]
      exact (γ.grid_le n ⟨hr.1,hr.2.trans_lt hT1⟩).trans
        (γ.monotone ⟨hr.1,hr.2.trans_lt hT1⟩ hT hr.2)) s hs t ht x

lemma phi_smooth_and_jet_limits (W : BrownianSpace) (γ : OrderParameter) {S : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) :
    (∀ k, TendstoUniformly (fun n (p : Icc (0 : ℝ) S×ℝ) ↦ iteratedDeriv k (smoothApprox γ n p.1) p.2)
      (fun p ↦ iteratedDeriv k (phi W γ p.1) p.2) atTop) ∧
      ∀ t∈Icc (0 : ℝ) S, ContDiff ℝ ∞ (phi W γ t) := by
  let map : Icc (0 : ℝ) S×ℝ → Ico (0 : ℝ) 1×ℝ :=
    fun p ↦ (⟨p.1,⟨p.1.property.1,p.1.property.2.trans_lt hS.2⟩⟩,p.2)
  have hlim : TendstoUniformly (fun n (p : Icc (0 : ℝ) S×ℝ) ↦ smoothApprox γ n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := (smoothApprox_tendsto W γ).comp map
  have hs (n : ℕ) (t : Icc (0 : ℝ) S) : ContDiff ℝ ∞ (smoothApprox γ n t) :=
    ((smoothApprox_evolution γ n).slices t ⟨t.property.1,t.property.2.trans hS.2.le⟩).smooth
  have hb (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : Icc (0 : ℝ) S) x,
      |iteratedDeriv (k+1) (smoothApprox γ n a) x| ≤ C := by
    obtain ⟨C,hC,hb⟩ := smoothApprox_bulk_jets γ hS k
    refine ⟨C,hC,fun n a x ↦ ?_⟩
    simpa only [iteratedDeriv_succ'] using hb n a a.property k le_rfl x
  obtain ⟨hl,hsm⟩ := uniform_all_derivative_limits (f := fun t : Icc (0 : ℝ) S ↦ phi W γ t) hlim hs hb
  exact ⟨hl,fun t ht ↦ hsm ⟨t,ht⟩⟩

lemma phi_jet_limit (W : BrownianSpace) (γ : OrderParameter) {S t : ℝ}
    (hS : S∈Ico (0 : ℝ) 1) (ht : t∈Icc (0 : ℝ) S) (k : ℕ) (x : ℝ) :
    Tendsto (fun n ↦ iteratedDeriv k (deriv (smoothApprox γ n t)) x) atTop
      (𝓝 (iteratedDeriv k (deriv (phi W γ t)) x)) := by
  simpa only [iteratedDeriv_succ'] using
    ((phi_smooth_and_jet_limits W γ hS).1 (k+1)).tendsto_at (⟨t,ht⟩,x)

end SKValue

end

end OAI
