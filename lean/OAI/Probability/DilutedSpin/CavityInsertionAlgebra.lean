import OAI.Probability.DilutedSpin.PhysicalCountLaw
import OAI.Probability.DilutedSpin.QSubtreePotential
import OAI.Probability.DilutedSpin.TopologyDecay

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
open _root_.MeasureTheory _root_.OAI.MeasureTheory
namespace FiniteLaw

lemma spinLog_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → Spin) → ℝ) (x : ι → ℝ) :
    spinLog F x=Real.log (∑ s : ι → Spin,(∏ i,q (x i) (s i))*Real.exp (F s)) := by
  unfold spinLog
  rw [Subsingleton.elim (finiteMapDecEq ι) (inferInstance : DecidableEq ι)]

lemma spinLog_edge {p : ℕ} (θ : Interaction p) :
    spinLog θ = fun x => Real.log (edge θ x) := by
  funext x
  rw [spinLog_eq]
  apply congrArg Real.log
  unfold edge
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

lemma spinPartition_blocks {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : ι → (κ → Spin) → ℝ) (x : ι × κ → ℝ) :
    (∑ s : ι × κ → Spin, (∏ i, q (x i) (s i))*Real.exp (∑ j,F j (fun l => s (j,l)))) =
      ∏ j : ι, ∑ s : κ → Spin,(∏ l,q (x (j,l)) (s l))*Real.exp (F j s) := by
  classical
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (Equiv.curry ι κ Spin)
  intro s
  simp only [Equiv.curry_apply,Function.curry,Real.exp_sum,Fintype.prod_prod_type,← Finset.prod_mul_distrib]
  rfl

lemma spinLog_blocks {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : ι → (κ → Spin) → ℝ) (x : ι × κ → ℝ) :
    spinLog (fun s : ι × κ → Spin => ∑ j,F j (fun l => s (j,l))) x =
      ∑ j : ι,spinLog (F j) (fun l => x (j,l)) := by
  simp only [spinLog_eq]
  rw [spinPartition_blocks,Real.log_prod]
  intro j _
  apply ne_of_gt
  apply Finset.sum_pos
  · intro s _
    exact mul_pos (Finset.prod_pos (fun l _ => q_pos _ _)) (Real.exp_pos _)
  · exact Finset.univ_nonempty

end FiniteLaw

noncomputable def cavitySiteEnergy {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (s : Fin k × Fin (p-1) → Spin) : ℝ :=
  Real.log ((∑ ε : Spin, Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2)

lemma cavitySiteEnergy_bound {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (s : Fin k × Fin (p-1) → Spin) :
    |cavitySiteEnergy θ h s| ≤ |h|+∑ j,‖(θ j).1‖ := by
  change |Real.log ((∑ ε : Spin, Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2)| ≤ _
  have hh (ε : Spin) : |h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)| ≤ |h|+∑ j,‖(θ j).1‖ := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul,abs_spin,mul_one]
    · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (θ j).1 (appendSpin (fun l => s (j,l)) ε)))
  -- This is the logarithm of the uniform two-spin exponential moment.
  have hb := (FiniteLaw.uniform : FiniteLaw Spin).logMean_stability (show (0:ℝ)<1 by norm_num)
    (g := fun _ => 0) (fun ε => by simpa only [sub_zero] using hh ε)
  simp only [FiniteLaw.logMean_const _ (one_ne_zero), sub_zero] at hb
  simpa only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
    FiniteLaw.uniform,Fintype.card_bool,← Finset.mul_sum,inv_mul_eq_div,Nat.cast_ofNat,← Finset.sum_div] using hb

lemma spinLog_cavitySiteEnergy {p k : ℕ} (θ : Fin k → InteractionSample p) (h : ℝ)
    (x : Fin k × Fin (p-1) → ℝ) :
    FiniteLaw.spinLog (cavitySiteEnergy θ h) x = siteLog θ h x := by
  classical
  have hp (s : Fin k × Fin (p-1) → Spin) :
      0 < (∑ ε : Spin,Real.exp (h*spin ε+∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))/2 :=
    div_pos (Finset.sum_pos (fun ε _ => Real.exp_pos _) Finset.univ_nonempty) (by norm_num)
  rw [FiniteLaw.spinLog_eq]
  unfold cavitySiteEnergy
  simp only [Real.exp_log (hp _)]
  unfold siteLog
  apply congrArg Real.log
  simp only [← mul_div_assoc,← Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro ε _
  simp_rw [Real.exp_add]
  rw [show (∑ s : Fin k × Fin (p-1) → Spin, (∏ i,q (x i) (s i))*
      (Real.exp (h*spin ε)*Real.exp (∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε)))) =
      Real.exp (h*spin ε)*(∑ s : Fin k × Fin (p-1) → Spin,(∏ i,q (x i) (s i))*
        Real.exp (∑ j,(θ j).1 (appendSpin (fun l => s (j,l)) ε))) by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring]
  congr 1
  rw [FiniteLaw.spinPartition_blocks (fun j (s : Fin (p-1) → Spin) => (θ j).1 (appendSpin s ε)) x,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  unfold message
  rw [Real.exp_log]
  · apply Finset.sum_congr rfl; intro s _; exact mul_comm _ _
  · exact Finset.sum_pos (fun s _ => mul_pos (Real.exp_pos _) (Finset.prod_pos (fun l _ => q_pos _ _))) Finset.univ_nonempty

end DilutedSpinGlass

end

end OAI
