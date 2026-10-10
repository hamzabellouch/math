import OAI.Probability.DilutedSpin.Core

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace DilutedSpinGlass

theorem abs_spin (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]

theorem sum_exp_pos {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    0 < ∑ i, Real.exp (f i) :=
  Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
    ⟨Classical.arbitrary ι, Finset.mem_univ _, Real.exp_pos _⟩

theorem logSumExp_stability {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) {C : ℝ} (h : ∀ i, |f i-g i| ≤ C) :
    |Real.log (∑ i, Real.exp (f i)) - Real.log (∑ i, Real.exp (g i))| ≤ C := by
  have aux (f g : ι → ℝ) (h : ∀ i, f i ≤ g i+C) :
      Real.log (∑ i, Real.exp (f i)) ≤ Real.log (∑ i, Real.exp (g i)) + C := by
    have hb : (∑ i, Real.exp (f i)) ≤ (∑ i, Real.exp (g i))*Real.exp C := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i _ => by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (h i))
    have hl := Real.log_le_log (sum_exp_pos f) hb
    rwa [Real.log_mul (sum_exp_pos g).ne' (Real.exp_pos C).ne', Real.log_exp] at hl
  exact abs_le.mpr ⟨by have := aux g f (fun i => by have := (abs_le.mp (h i)).1; linarith); linarith,
    by have := aux f g (fun i => by have := (abs_le.mp (h i)).2; linarith); linarith⟩

theorem logWeight_bound {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) :
    |logWeight theta h indices σ| ≤ (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (theta j).1 (fun l => σ (indices j l))))
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simp only [abs_mul, abs_spin, mul_one, le_refl]))

theorem logPartition_bound {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    |logPartition theta h indices - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  have hs : Real.log (∑ _σ : Fin N → Spin, Real.exp (0:ℝ)) = (N:ℝ)*Real.log 2 := by
    simp only [Real.exp_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_fun, Fintype.card_fin, show Fintype.card Spin = 2 from rfl,
      Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  simpa only [logPartition, hs, sub_zero] using
    logSumExp_stability (logWeight theta h indices) (fun _ => 0)
      (fun σ => by simpa using logWeight_bound theta h indices σ)

theorem logWeight_stability {p N k : ℕ} (theta theta' : Fin k → InteractionSample p)
    (h h' : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) :
    |logWeight theta h indices σ - logWeight theta' h' indices σ| ≤
      (∑ j, ‖(theta j).1-(theta' j).1‖) + ∑ i, |h i-h' i| := by
  have he : logWeight theta h indices σ - logWeight theta' h' indices σ =
      (∑ j, ((theta j).1-(theta' j).1) (fun l => σ (indices j l))) +
        ∑ i, (h i-h' i)*spin (σ i) := by
    simp only [logWeight, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]; ring
  rw [he]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm ((theta j).1-(theta' j).1)
        (fun l => σ (indices j l))))
  · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simp only [abs_mul, abs_spin, mul_one, le_refl]))

theorem logPartition_stability {p N k : ℕ} (theta theta' : Fin k → InteractionSample p)
    (h h' : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) :
    |logPartition theta h indices - logPartition theta' h' indices| ≤
      (∑ j, ‖(theta j).1-(theta' j).1‖) + ∑ i, |h i-h' i| :=
  logSumExp_stability _ _ (logWeight_stability theta theta' h h' indices)

noncomputable def indexAverage {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) : ℝ :=
  (∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) /
    (Fintype.card (Fin k → Fin p → Fin N):ℝ)

theorem indexAverage_bound {p N k : ℕ} (hN : 0 < N)
    (theta : Fin k → InteractionSample p) (h : Fin N → ℝ) :
    |indexAverage theta h - (N:ℝ)*Real.log 2| ≤
      (∑ j, ‖(theta j).1‖) + ∑ i, |h i| := by
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hc : (0:ℝ) < Fintype.card (Fin k → Fin p → Fin N) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [indexAverage, div_sub' (ne_of_gt hc), abs_div,
    abs_of_pos hc, div_le_iff₀ hc]
  rw [show (∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) -
      (Fintype.card (Fin k → Fin p → Fin N):ℝ) * ((N:ℝ)*Real.log 2) =
        ∑ indices : Fin k → Fin p → Fin N,
          (logPartition theta h indices - (N:ℝ)*Real.log 2) by simp [Finset.sum_sub_distrib]]
  calc
    _ ≤ ∑ _indices : Fin k → Fin p → Fin N,
        ((∑ j, ‖(theta j).1‖) + ∑ i, |h i|) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun indices _ => logPartition_bound theta h indices))
    _ = _ := by simp [mul_comm, mul_add]

theorem continuous_logPartition {p N k : ℕ} (indices : Fin k → Fin p → Fin N) :
    Continuous (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) =>
      logPartition z.1 z.2 indices) := by
  unfold logPartition
  apply Continuous.log
  · unfold logWeight
    fun_prop
  · intro z
    exact (sum_exp_pos _).ne'

theorem continuous_indexAverage {p N k : ℕ} :
    Continuous (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) =>
      indexAverage z.1 z.2) := by
  unfold indexAverage
  exact (continuous_finsetSum _ (fun indices _ => continuous_logPartition indices)).div_const _


end DilutedSpinGlass
end

end

end OAI
