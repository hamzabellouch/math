import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicSimplexRecurrence

namespace OAI

/-! # The ordered integral vanishes above the product-degree cutoff -/
namespace JointDickman
open Finset Filter MeasureTheory

 theorem logarithmicSimplex_eq_zero {c : ℝ} (hc : 0 < c) (n : ℕ)
    (hnc : 1 ≤ ((n+1 : ℕ) : ℝ)*c) : logarithmicSimplex (n+1) c = 0 := by
  have hs : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), c < t := by
    have hs' : ∀ᵐ t ∂(logarithmicPrimeMeasure c : Measure ℝ), t ∈ Set.Ioc c 1 := by
      rw [ae_iff]
      exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (logarithmicPrimeMeasure_support hc)
    exact hs'.mono (fun _ ht => ht.1)
  have hp : ∀ᵐ t : Fin (n+1) → ℝ ∂Measure.pi (fun _ : Fin (n+1) =>
      (logarithmicPrimeMeasure c : Measure ℝ)), ∀ i, c < t i :=
    eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae (i := i)).eventually hs)
  have hz : (Measure.pi (fun _ : Fin (n+1) => (logarithmicPrimeMeasure c : Measure ℝ)))
      (orderedTupleRegion (n+1) 1) = 0 := by
    have ha : ∀ᵐ t : Fin (n+1) → ℝ ∂Measure.pi (fun _ : Fin (n+1) =>
        (logarithmicPrimeMeasure c : Measure ℝ)), t ∉ orderedTupleRegion (n+1) 1 := by
      filter_upwards [hp] with t ht hmem
      have hh := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin (n+1))))
        univ_nonempty (fun i _ => ht i)
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
      exact (not_lt_of_ge hnc) (hh.trans_le hmem.2)
    simpa only [not_not, Set.ofPred_mem_eq] using (ae_iff.mp ha)
  simp only [logarithmicSimplex, orderedSimplexMass, measureReal_def, hz, ENNReal.toReal_zero]

noncomputable def logarithmicAvoidance (N : ℕ) (c : ℝ) : ℝ :=
  ∑ n ∈ range (N+1), (-1 : ℝ)^n * logarithmicSimplex n c

 theorem logarithmicAvoidance_zero (c : ℝ) : logarithmicAvoidance 0 c = 1 := by
  simp [logarithmicAvoidance, logarithmicSimplex_zero]

 theorem logarithmicAvoidance_initial {c : ℝ} (hc : 1 ≤ c) (N : ℕ) :
    logarithmicAvoidance N c = 1 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  induction N with
  | zero => exact logarithmicAvoidance_zero c
  | succ N ih =>
    rw [logarithmicAvoidance, sum_range_succ]
    change logarithmicAvoidance N c + _ = 1
    rw [ih, logarithmicSimplex_eq_zero hc0 N, mul_zero, add_zero]
    have hN : (1 : ℝ) ≤ (N+1 : ℕ) := by exact_mod_cast (Nat.succ_pos N)
    exact hc.trans (le_mul_of_one_le_left hc0.le hN)

end JointDickman

end OAI
