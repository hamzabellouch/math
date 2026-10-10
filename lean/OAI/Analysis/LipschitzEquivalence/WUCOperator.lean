import OAI.Analysis.LipschitzEquivalence.WUCDuals

namespace OAI

universe uE

noncomputable section
namespace LipschitzCounterexample.WeakSequences
open scoped BigOperators NNReal ENNReal Topology
open Filter
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sum_abs_le_of_signed_bound (T : ℕ → E →L[ℝ] ℝ)
    (hT : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : E,
      |∑ i ∈ Finset.range n, c i*T i x| ≤ 2*‖x‖) (n : ℕ) (x : E) :
    (∑ i ∈ Finset.range n, |T i x|) ≤ 2*‖x‖ := by
  classical
  let c : ℕ → ℝ := fun i => if 0 ≤ T i x then 1 else -1
  have hc (i : ℕ) : |c i| ≤ 1 := by unfold c; split_ifs <;> norm_num
  have he (i : ℕ) : c i*T i x = |T i x| := by
    unfold c
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]
  have h := hT n c hc x
  simpa only [he,abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (T i x)))] using h

def wucOperator (T : ℕ → E →L[ℝ] ℝ)
    (hT : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : E,
      |∑ i ∈ Finset.range n, c i*T i x| ≤ 2*‖x‖) : E →L[ℝ] RealL1 :=
  ({ toFun := fun x => ⟨fun i => T i x,memℓp_gen (by
       simp only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs]
       exact summable_of_sum_range_le (fun i => abs_nonneg _)
         (fun n => sum_abs_le_of_signed_bound T hT n x))⟩
     map_add' := by intro x y; apply lp.ext; funext i; exact map_add (T i) x y
     map_smul' := by intro c x; apply lp.ext; funext i; exact map_smul (T i) c x } : E →ₗ[ℝ] RealL1).mkContinuous 2 (by
       intro x
       rw [sumL1_norm]
       change (∑' i, ‖T i x‖) ≤ 2*‖x‖
       simp only [Real.norm_eq_abs]
       exact Real.tsum_le_of_sum_range_le (fun i => abs_nonneg _)
         (fun n => sum_abs_le_of_signed_bound T hT n x))

@[simp] theorem wucOperator_apply (T : ℕ → E →L[ℝ] ℝ) (hT) (x : E) (i : ℕ) :
    wucOperator T hT x i = T i x := rfl

theorem uniform_small_of_wuc (T : ℕ → E →L[ℝ] ℝ)
    (hT : ∀ (n : ℕ) (c : ℕ → ℝ), (∀ i, |c i| ≤ 1) → ∀ x : E,
      |∑ i ∈ Finset.range n, c i*T i x| ≤ 2*‖x‖)
    {u : ℕ → E} (hu : WeakCauchy u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ j ≥ N, ∀ k, |T j (u k)| < ε := by
  let S := wucOperator T hT
  obtain ⟨N,hN⟩ := uniform_tails_of_cauchy (fun k => S (u k))
    (schur_cauchy (hu.map S)) ε hε
  refine ⟨N,fun j hj k => ?_⟩
  have hcoord := lp.norm_apply_le_norm (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (tailL1 N (S (u k))) j
  simp only [tailL1_apply,ite_eq_left hj,Real.norm_eq_abs] at hcoord
  exact hcoord.trans_lt (hN k)

end LipschitzCounterexample.WeakSequences
end

end OAI
