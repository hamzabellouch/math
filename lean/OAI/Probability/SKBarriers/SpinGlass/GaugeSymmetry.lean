import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.LogPartition

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
def logPartitionProxy (β : ℝ) (n : ℕ) : NNReal :=
  ⟨Real.pi ^ 2 * β ^ 2 * n / 8, by positivity⟩

theorem logPartition_subGaussian {n : ℕ} (hn : 0 < n) (β : ℝ) :
    HasSubgaussianMGF
      (fun J : Disorder n => logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)
      (logPartitionProxy β n) (disorderLaw n) := by
  refine ⟨logPartition_centered_exp_integrable hn β, fun ℓ => ?_⟩
  apply (logPartition_centered_exp_integral_le hn β ℓ).trans
  apply Real.exp_le_exp.mpr
  change ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16 ≤
    (Real.pi ^ 2 * β ^ 2 * (n : ℝ) / 8) * ℓ ^ 2 / 2
  have h : 0 ≤ ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 := by positivity
  nlinarith

theorem logPartition_upper_tail {n : ℕ} (hn : 0 < n) (β u : ℝ) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ logPartition β J - ∫ K, logPartition β K ∂disorderLaw n} ≤
      Real.exp (-u ^ 2 / (2 * (logPartitionProxy β n : ℝ))) :=
  (logPartition_subGaussian hn β).measure_ge_le hu

theorem logPartition_lower_tail {n : ℕ} (hn : 0 < n) (β u : ℝ) (hu : 0 ≤ u) :
    (disorderLaw n).real {J | u ≤ (∫ K, logPartition β K ∂disorderLaw n) - logPartition β J} ≤
      Real.exp (-u ^ 2 / (2 * (logPartitionProxy β n : ℝ))) := by
  simpa only [Pi.neg_apply, neg_sub] using (logPartition_subGaussian hn β).neg.measure_ge_le hu

def gaugeConfig {n : ℕ} (v x : Config n) : Config n := fun i => v i == x i

@[simp] theorem spin_beq (b c : Bool) : spin (b == c) = spin b * spin c := by
  cases b <;> cases c <;> norm_num [spin]

@[simp] theorem gaugeConfig_involutive {n : ℕ} (v x : Config n) :
    gaugeConfig v (gaugeConfig v x) = x := by
  funext i
  cases hv : v i <;> cases hx : x i <;> simp [gaugeConfig, hv, hx]

def gaugeConfigEquiv {n : ℕ} (v : Config n) : Config n ≃ Config n :=
  { toFun := gaugeConfig v
    invFun := gaugeConfig v
    left_inv := gaugeConfig_involutive v
    right_inv := gaugeConfig_involutive v }

def gaugeDisorder {n : ℕ} (v : Config n) (J : Disorder n) : Disorder n :=
  fun e => (spin (v e.val.1) * spin (v e.val.2)) * J e

theorem gaugeDisorder_coordinate_law {n : ℕ} (v : Config n) (e : Edge n) :
    HasLaw (fun J => gaugeDisorder v J e) (gaussianReal 0 1) (disorderLaw n) := by
  have h := gaussianReal_const_mul (disorder_coordinate_law e)
    (spin (v e.val.1) * spin (v e.val.2))
  have hc : NNReal.mk ((spin (v e.val.1) * spin (v e.val.2)) ^ 2)
      (sq_nonneg _) = 1 := by
    apply Subtype.ext
    simp [NNReal.mk, mul_pow]
  simpa only [gaugeDisorder, mul_zero, hc, one_mul] using h

theorem gaugeDisorder_law {n : ℕ} (v : Config n) :
    HasLaw (gaugeDisorder v) (disorderLaw n) (disorderLaw n) := by
  apply iIndepFun.hasLaw_pi (gaugeDisorder_coordinate_law v)
  exact (disorder_independent n).comp
    (fun e z => (spin (v e.val.1) * spin (v e.val.2)) * z)
    (fun _ => measurable_const.mul measurable_id)

theorem hamiltonian_gauge {n : ℕ} (v x : Config n) (J : Disorder n) :
    hamiltonian (gaugeDisorder v J) x = hamiltonian J (gaugeConfig v x) := by
  unfold hamiltonian gaugeDisorder gaugeConfig
  simp only [spin_beq]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem partition_gauge {n : ℕ} (β : ℝ) (v : Config n) (J : Disorder n) :
    partition β (gaugeDisorder v J) = partition β J := by
  unfold partition
  simp_rw [hamiltonian_gauge]
  exact (gaugeConfigEquiv v).sum_comp (fun x => Real.exp (β * hamiltonian J x))

theorem gibbs_gauge {n : ℕ} (β : ℝ) (v x : Config n) (J : Disorder n) :
    gibbs β (gaugeDisorder v J) x = gibbs β J (gaugeConfig v x) := by
  simp only [gibbs, hamiltonian_gauge, partition_gauge]

@[simp] theorem gaugeConfig_self {n : ℕ} (v : Config n) :
    gaugeConfig v v = fun _ => true := by
  funext i
  simp [gaugeConfig]

@[simp] theorem gaugeConfig_true {n : ℕ} (v : Config n) :
    gaugeConfig v (fun _ => true) = v := by
  funext i
  cases hv : v i <;> simp [gaugeConfig, hv]

theorem gibbs_integral_gauge {n : ℕ} (β : ℝ) (v x : Config n) :
    (∫ J, gibbs β J (gaugeConfig v x) ∂disorderLaw n) =
      ∫ J, gibbs β J x ∂disorderLaw n := by
  have h := (gaugeDisorder_law v).integral_comp (continuous_gibbs β x).aestronglyMeasurable
  simpa only [Function.comp_def, gibbs_gauge] using h

theorem gibbs_integral_eq {n : ℕ} (β : ℝ) (x y : Config n) :
    (∫ J, gibbs β J x ∂disorderLaw n) = ∫ J, gibbs β J y ∂disorderLaw n := by
  have hx := gibbs_integral_gauge β x (fun _ => true)
  have hy := gibbs_integral_gauge β y (fun _ => true)
  simpa only [gaugeConfig_true] using hx.trans hy.symm

theorem gibbs_integral_uniform {n : ℕ} (β : ℝ) (x : Config n) :
    (∫ J, gibbs β J x ∂disorderLaw n) = (Fintype.card (Config n) : ℝ)⁻¹ := by
  have hs : (∑ y : Config n, ∫ J, gibbs β J y ∂disorderLaw n) = 1 := by
    rw [← integral_finsetSum]
    · simp [gibbs_sum]
    · intro y _
      exact gibbs_integrable β y
  simp_rw [gibbs_integral_eq β _ x] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card (Config n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_eq_one_div]
  apply (eq_div_iff hc).mpr
  simpa only [mul_comm] using hs

end SK

noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval

end
end
end
end

end OAI
