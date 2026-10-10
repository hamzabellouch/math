import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
def disorderPairLaw (n : ℕ) : Measure (Disorder n × Disorder n) :=
  (disorderLaw n).prod (disorderLaw n)

instance disorderLaw_isGaussian (n : ℕ) : IsGaussian (disorderLaw n) := by
  have h := (disorder_gaussian n).isGaussian_map
  change IsGaussian (Measure.map id (disorderLaw n)) at h
  rwa [Measure.map_id] at h

instance disorderPairLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderPairLaw n) := by
  unfold disorderPairLaw
  infer_instance

theorem disorderPair_fst_law (n : ℕ) :
    HasLaw (Prod.fst : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_fst.hasLaw

theorem disorderPair_snd_law (n : ℕ) :
    HasLaw (Prod.snd : Disorder n × Disorder n → Disorder n)
      (disorderLaw n) (disorderPairLaw n) :=
  measurePreserving_snd.hasLaw

theorem disorderPair_independent (n : ℕ) :
    IndepFun (Prod.fst : Disorder n × Disorder n → Disorder n)
      Prod.snd (disorderPairLaw n) := by
  apply (indepFun_iff_hasLaw_prodMk_prod (disorderPair_fst_law n)
    (disorderPair_snd_law n)).2
  exact HasLaw.id

theorem disorderPair_gaussian (n : ℕ) :
    HasGaussianLaw (fun p : Disorder n × Disorder n => p) (disorderPairLaw n) :=
  (disorderPair_independent n).hasGaussianLaw (disorderPair_fst_law n).hasGaussianLaw
    (disorderPair_snd_law n).hasGaussianLaw

theorem disorderPair_fst_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.1 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_fst_law n)

theorem disorderPair_snd_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun p : Disorder n × Disorder n => p.2 e)
      (gaussianReal 0 1) (disorderPairLaw n) :=
  (disorder_coordinate_law e).fun_comp (disorderPair_snd_law n)

theorem disorderPair_fst_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.1 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_fst_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_snd_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.2 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] =
      if e = f then 1 else 0 := by
  rw [(disorderPair_snd_law n).covariance_fun_comp
    (disorder_coordinate_law e).aemeasurable (disorder_coordinate_law f).aemeasurable]
  exact disorder_covariance e f

theorem disorderPair_cross_covariance {n : ℕ} (e f : Edge n) :
    cov[fun p : Disorder n × Disorder n => p.1 e,
      fun p : Disorder n × Disorder n => p.2 f; disorderPairLaw n] = 0 := by
  exact ((disorderPair_independent n).comp (measurable_pi_apply e)
    (measurable_pi_apply f)).covariance_eq_zero
      (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
      (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y Z W : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ) (hW : MemLp W 2 μ)
    (a b c d : ℝ) :
    cov[fun ω => a * X ω + b * Y ω, fun ω => c * Z ω + d * W ω; μ] =
      a * c * cov[X, Z; μ] + a * d * cov[X, W; μ] +
      b * c * cov[Y, Z; μ] + b * d * cov[Y, W; μ] := by
  change cov[(fun ω => a * X ω) + (fun ω => b * Y ω),
    (fun ω => c * Z ω) + (fun ω => d * W ω); μ] = _
  rw [covariance_add_left (hX.const_mul a) (hY.const_mul b)
      ((hZ.const_mul c).add (hW.const_mul d)),
    covariance_add_right (hX.const_mul a) (hZ.const_mul c) (hW.const_mul d),
    covariance_add_right (hY.const_mul b) (hZ.const_mul c) (hW.const_mul d)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

def mixDisorder {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) : Disorder n :=
  a • p.1 + b • p.2

def mixDisorderCLM (n : ℕ) (a b : ℝ) : (Disorder n × Disorder n) →L[ℝ] Disorder n :=
  a • ContinuousLinearMap.fst ℝ (Disorder n) (Disorder n) +
  b • ContinuousLinearMap.snd ℝ (Disorder n) (Disorder n)

@[simp] theorem mixDisorderCLM_apply {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) :
    mixDisorderCLM n a b p = mixDisorder a b p := rfl

theorem mixDisorder_gaussian (n : ℕ) (a b : ℝ) :
    HasGaussianLaw (mixDisorder (n := n) a b) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (mixDisorderCLM n a b)

theorem mixDisorder_mean {n : ℕ} (a b : ℝ) (e : Edge n) :
    (∫ p, mixDisorder a b p e ∂disorderPairLaw n) = 0 := by
  change (∫ p : Disorder n × Disorder n, a * p.1 e + b * p.2 e ∂disorderPairLaw n) = 0
  rw [integral_add
    ((disorderPair_fst_coordinate_law e).hasGaussianLaw.integrable.const_mul a)
    ((disorderPair_snd_coordinate_law e).hasGaussianLaw.integrable.const_mul b),
    integral_const_mul, integral_const_mul,
    (disorderPair_fst_coordinate_law e).integral_eq,
    (disorderPair_snd_coordinate_law e).integral_eq]
  simp

theorem mixDisorder_covariance {n : ℕ} (a b c d : ℝ) (e f : Edge n) :
    cov[fun p => mixDisorder a b p e, fun p => mixDisorder c d p f; disorderPairLaw n] =
      (a * c + b * d) * (if e = f then 1 else 0) := by
  change cov[fun p : Disorder n × Disorder n => a * p.1 e + b * p.2 e,
    fun p : Disorder n × Disorder n => c * p.1 f + d * p.2 f; disorderPairLaw n] = _
  rw [covariance_linear_combination
    (disorderPair_fst_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law e).hasGaussianLaw.memLp_two
    (disorderPair_fst_coordinate_law f).hasGaussianLaw.memLp_two
    (disorderPair_snd_coordinate_law f).hasGaussianLaw.memLp_two,
    disorderPair_fst_covariance, disorderPair_snd_covariance, disorderPair_cross_covariance]
  rw [covariance_comm (fun p : Disorder n × Disorder n => p.2 e),
    disorderPair_cross_covariance]
  ring

theorem mixDisorder_coordinate_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (e : Edge n) :
    HasLaw (fun p => mixDisorder a b p e) (gaussianReal 0 1) (disorderPairLaw n) := by
  have hg := (mixDisorder_gaussian n a b).eval e
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, mixDisorder_mean,
    ← covariance_self hg.aemeasurable, mixDisorder_covariance]
  simp only [ite_true, mul_one]
  have h : a * a + b * b = 1 := by nlinarith [hab]
  rw [h]
  norm_num

theorem mixDisorder_law {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    HasLaw (mixDisorder (n := n) a b) (disorderLaw n) (disorderPairLaw n) := by
  apply iIndepFun.hasLaw_pi (fun e => mixDisorder_coordinate_law a b hab e)
  apply (mixDisorder_gaussian n a b).iIndepFun_of_covariance_eq_zero
  intro e f hef
  rw [mixDisorder_covariance, ite_eq_right hef, mul_zero]

def rotateDisorder {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    Disorder n × Disorder n :=
  (mixDisorder (Real.cos θ) (Real.sin θ) p,
    mixDisorder (- Real.sin θ) (Real.cos θ) p)

def rotateDisorderCLM (n : ℕ) (θ : ℝ) :
    (Disorder n × Disorder n) →L[ℝ] Disorder n × Disorder n :=
  (mixDisorderCLM n (Real.cos θ) (Real.sin θ)).prod
    (mixDisorderCLM n (- Real.sin θ) (Real.cos θ))

@[simp] theorem rotateDisorderCLM_apply {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    rotateDisorderCLM n θ p = rotateDisorder θ p := rfl

theorem rotateDisorder_gaussian (n : ℕ) (θ : ℝ) :
    HasGaussianLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) :=
  (disorderPair_gaussian n).map_fun (rotateDisorderCLM n θ)

theorem rotateDisorder_law (n : ℕ) (θ : ℝ) :
    HasLaw (rotateDisorder (n := n) θ) (disorderPairLaw n) (disorderPairLaw n) := by
  have hind : IndepFun (mixDisorder (n := n) (Real.cos θ) (Real.sin θ))
      (mixDisorder (- Real.sin θ) (Real.cos θ)) (disorderPairLaw n) := by
    apply (rotateDisorder_gaussian n θ).indepFun_of_covariance_eval
    intro e f
    rw [mixDisorder_covariance]
    ring
  exact hind.hasLaw_prod
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))
    (mixDisorder_law _ _ (by nlinarith [Real.sin_sq_add_cos_sq θ]))

def directionalEnergy {n : ℕ} (β : ℝ) (J K : Disorder n) : ℝ :=
  β * ∑ x : Config n, gibbs β J x * hamiltonian K x

theorem directionalEnergy_exp_le {n : ℕ} (β ℓ : ℝ) (J K : Disorder n) :
    Real.exp (ℓ * directionalEnergy β J K) ≤
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x) := by
  have h := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := gibbs β J) (p := fun x => ℓ * β * hamiltonian K x)
    (fun x _ => le_of_lt (gibbs_pos β J x)) (gibbs_sum β J)
    (fun _ _ => Set.mem_univ _)
  simpa only [smul_eq_mul, ← Finset.mul_sum, directionalEnergy, mul_assoc,
    mul_left_comm (gibbs β J _)] using h

theorem continuous_hamiltonian {n : ℕ} (x : Config n) :
    Continuous (fun J : Disorder n => hamiltonian J x) := by
  unfold hamiltonian
  fun_prop

theorem continuous_partition {n : ℕ} (β : ℝ) :
    Continuous (partition (n := n) β) := by
  unfold partition
  exact continuous_finsetSum _ (fun x _ =>
    Real.continuous_exp.comp (continuous_const.mul (continuous_hamiltonian x)))

theorem continuous_gibbs {n : ℕ} (β : ℝ) (x : Config n) :
    Continuous (fun J : Disorder n => gibbs β J x) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_hamiltonian x))).div
    (continuous_partition β) (fun J => ne_of_gt (partition_pos β J))

theorem gibbs_le_one {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J x ≤ 1 := by
  rw [← gibbs_sum β J]
  exact Finset.single_le_sum (fun z _ => le_of_lt (gibbs_pos β J z)) (Finset.mem_univ x)

theorem gibbs_integrable {n : ℕ} (β : ℝ) (x : Config n) :
    Integrable (fun J : Disorder n => gibbs β J x) (disorderLaw n) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_gibbs β x).aestronglyMeasurable
  filter_upwards [] with J
  simpa only [Real.norm_eq_abs, abs_of_pos (gibbs_pos β J x)] using gibbs_le_one β J x

theorem continuous_directionalEnergy {n : ℕ} (β : ℝ) :
    Continuous (fun p : Disorder n × Disorder n => directionalEnergy β p.1 p.2) := by
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun x _ =>
    ((continuous_gibbs β x).comp continuous_fst).mul
      ((continuous_hamiltonian x).comp continuous_snd))

theorem directionalEnergy_exp_integrable {n : ℕ} (β ℓ : ℝ) (J : Disorder n) :
    Integrable (fun K : Disorder n => Real.exp (ℓ * directionalEnergy β J K))
      (disorderLaw n) := by
  have hsum : Integrable (fun K : Disorder n =>
      ∑ x : Config n, gibbs β J x * Real.exp (ℓ * β * hamiltonian K x))
      (disorderLaw n) :=
    integrable_finsetSum _ (fun x _ =>
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _)
  apply hsum.mono'
  · exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_directionalEnergy β).comp (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
  · filter_upwards [] with K
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ J K

theorem directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n)
    (β ℓ : ℝ) (J : Disorder n) :
    (∫ K : Disorder n, Real.exp (ℓ * directionalEnergy β J K) ∂disorderLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hsum (x : Config n) : Integrable (fun K : Disorder n =>
      gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) (disorderLaw n) :=
    (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β)).const_mul _
  calc
    _ ≤ ∫ K : Disorder n, (∑ x : Config n,
        gibbs β J x * Real.exp (ℓ * β * hamiltonian K x)) ∂disorderLaw n :=
      integral_mono (directionalEnergy_exp_integrable β ℓ J)
        (integrable_finsetSum _ (fun x _ => hsum x)) (directionalEnergy_exp_le β ℓ J)
    _ = _ := by
      rw [integral_finsetSum _ (fun x _ => hsum x)]
      simp_rw [integral_const_mul, hamiltonian_exp_integral hn]
      rw [← Finset.sum_mul, gibbs_sum, one_mul]

theorem directionalEnergy_pair_exp_integrable {n : ℕ} (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) := by
  have hsum : Integrable (fun p : Disorder n × Disorder n =>
      ∑ x : Config n, gibbs β p.1 x * Real.exp (ℓ * β * hamiltonian p.2 x))
      (disorderPairLaw n) := by
    apply integrable_finsetSum
    intro x _
    exact (gibbs_integrable β x).mul_prod
      (gaussian_exp_integrable (hamiltonian_gaussian x) (ℓ * β))
  apply hsum.mono'
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy β))).aestronglyMeasurable
  · filter_upwards [] with p
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      directionalEnergy_exp_le β ℓ p.1 p.2

theorem directionalEnergy_pair_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β p.1 p.2) ∂disorderPairLaw n) ≤
      Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [disorderPairLaw, integral_prod _ (directionalEnergy_pair_exp_integrable β ℓ)]
  calc
    _ ≤ ∫ _J : Disorder n,
        Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂disorderLaw n :=
      integral_mono (directionalEnergy_pair_exp_integrable β ℓ).integral_prod_left
        (integrable_const _) (directionalEnergy_exp_integral_le hn β ℓ)
    _ = _ := by simp

theorem hamiltonian_mix {n : ℕ} (a b : ℝ) (p : Disorder n × Disorder n) (x : Config n) :
    hamiltonian (mixDisorder a b p) x =
      a * hamiltonian p.1 x + b * hamiltonian p.2 x := by
  simp only [hamiltonian, mixDisorder, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end SK
end
end
end

end OAI
