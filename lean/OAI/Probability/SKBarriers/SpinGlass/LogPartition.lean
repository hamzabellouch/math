import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.DisorderPairs

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK
def logPartition {n : ℕ} (β : ℝ) (J : Disorder n) : ℝ := Real.log (partition β J)

theorem continuous_logPartition {n : ℕ} (β : ℝ) :
    Continuous (logPartition (n := n) β) :=
  (continuous_partition β).log (fun J => ne_of_gt (partition_pos β J))

theorem logPartition_hasDerivAt {n : ℕ} (β : ℝ) (J : ℝ → Disorder n)
    (K : Disorder n) (s : ℝ)
    (hJ : ∀ x, HasDerivAt (fun t => hamiltonian (J t) x) (hamiltonian K x) s) :
    HasDerivAt (fun t => logPartition β (J t)) (directionalEnergy β (J s) K) s := by
  have hp : HasDerivAt (fun t => partition β (J t))
      (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) * (β * hamiltonian K x)) s := by
    exact HasDerivAt.fun_sum (fun x _ => ((hJ x).const_mul β).exp)
  have hl := hp.log (ne_of_gt (partition_pos β (J s)))
  have heq : (∑ x : Config n, Real.exp (β * hamiltonian (J s) x) *
      (β * hamiltonian K x)) / partition β (J s) =
      directionalEnergy β (J s) K := by
    simp only [directionalEnergy, gibbs, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq] at hl
  exact hl

theorem continuous_rotateDisorder (n : ℕ) :
    Continuous (fun q : ℝ × (Disorder n × Disorder n) => rotateDisorder q.1 q.2) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem rotation_logPartition_hasDerivAt {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) (s : ℝ) :
    HasDerivAt (fun t => logPartition β (rotateDisorder (θ * t) p).1)
      (θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) s := by
  have hd : HasDerivAt (fun t => logPartition β (rotateDisorder t p).1)
      (directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) (θ * s) := by
    apply logPartition_hasDerivAt
    intro x
    simp only [rotateDisorder, hamiltonian_mix]
    exact ((Real.hasDerivAt_cos _).mul_const _).add
      ((Real.hasDerivAt_sin _).mul_const _)
  simpa only [Function.comp_def, mul_one, mul_comm] using
    hd.comp s ((hasDerivAt_id s).const_mul θ)

theorem continuous_rotation_path {n : ℕ} (θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => rotateDisorder (θ * s) p) := by
  unfold rotateDisorder mixDisorder
  fun_prop

theorem continuous_rotation_energy {n : ℕ} (β θ : ℝ) (p : Disorder n × Disorder n) :
    Continuous (fun s : ℝ => directionalEnergy β (rotateDisorder (θ * s) p).1
      (rotateDisorder (θ * s) p).2) :=
  (continuous_directionalEnergy β).comp (continuous_rotation_path θ p)

theorem rotation_logPartition_integral {n : ℕ} (β θ : ℝ)
    (p : Disorder n × Disorder n) :
    logPartition β (rotateDisorder θ p).1 - logPartition β p.1 =
      ∫ s : ℝ in 0..1,
        θ * directionalEnergy β (rotateDisorder (θ * s) p).1
          (rotateDisorder (θ * s) p).2 := by
  have hc : Continuous (fun s : ℝ =>
      θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => rotation_logPartition_hasDerivAt β θ p s) (hc.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, rotateDisorder, mixDisorder, Real.cos_zero,
    Real.sin_zero, zero_smul, one_smul, add_zero] using h.symm

def unitIntervalLaw : Measure ℝ := volume.restrict (Set.Ioc 0 1)

instance unitIntervalLaw_probability : IsProbabilityMeasure unitIntervalLaw := by
  constructor
  simp [unitIntervalLaw]

theorem continuous_unitInterval_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f unitIntervalLaw :=
  hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem unitInterval_integral (f : ℝ → ℝ) :
    (∫ s, f s ∂unitIntervalLaw) = ∫ s : ℝ in 0..1, f s := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

theorem rotation_exp_jensen {n : ℕ} (β θ ℓ : ℝ) (p : Disorder n × Disorder n) :
    Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)) ≤
      ∫ s, Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) ∂unitIntervalLaw := by
  have hc : Continuous (fun s : ℝ => ℓ * θ *
      directionalEnergy β (rotateDisorder (θ * s) p).1
        (rotateDisorder (θ * s) p).2) :=
    continuous_const.mul (continuous_rotation_energy β θ p)
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _))
    (continuous_unitInterval_integrable hc)
    (continuous_unitInterval_integrable (Real.continuous_exp.comp hc))
  convert h using 2
  rw [unitInterval_integral, rotation_logPartition_integral,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem rotated_directionalEnergy_exp_integrable {n : ℕ} (β ℓ s : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2))
      (disorderPairLaw n) := by
  have hp := (rotateDisorder_law n s).measurePreserving (rotateDisorderCLM n s).continuous.measurable
  exact hp.integrable_comp_of_integrable (directionalEnergy_pair_exp_integrable β ℓ)

theorem rotated_directionalEnergy_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ s : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * directionalEnergy β (rotateDisorder s p).1 (rotateDisorder s p).2)
        ∂disorderPairLaw n) ≤ Real.exp ((ℓ * β) ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hm : AEStronglyMeasurable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) (disorderPairLaw n) :=
    (Real.continuous_exp.comp
      (continuous_const.mul (continuous_directionalEnergy (n := n) β))).aestronglyMeasurable
  have heq := (rotateDisorder_law n s).integral_comp (f := fun p =>
      Real.exp (ℓ * directionalEnergy β p.1 p.2)) hm
  change (∫ p, ((fun q : Disorder n × Disorder n =>
    Real.exp (ℓ * directionalEnergy β q.1 q.2)) ∘ rotateDisorder s) p
      ∂disorderPairLaw n) ≤ _
  rw [heq]
  exact directionalEnergy_pair_exp_integral_le hn β ℓ

def rotationIntegrand {n : ℕ} (β θ ℓ : ℝ) (s : ℝ) (p : Disorder n × Disorder n) : ℝ :=
  Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * s) p).1
    (rotateDisorder (θ * s) p).2)

theorem continuous_rotationIntegrand {n : ℕ} (β θ ℓ : ℝ) :
    Continuous (Function.uncurry (rotationIntegrand (n := n) β θ ℓ)) := by
  have hm : Continuous (fun q : ℝ × (Disorder n × Disorder n) => (θ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hr := (continuous_rotateDisorder n).comp hm
  dsimp only [Function.comp_def] at hr
  have hd : Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
      directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
        (rotateDisorder (θ * q.1) q.2).2) :=
    (continuous_directionalEnergy (n := n) β).comp hr
  change Continuous (fun q : ℝ × (Disorder n × Disorder n) =>
    Real.exp (ℓ * θ * directionalEnergy β (rotateDisorder (θ * q.1) q.2).1
      (rotateDisorder (θ * q.1) q.2).2))
  exact Real.continuous_exp.comp (continuous_const.mul hd)

theorem rotationIntegrand_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) := by
  have hm : AEStronglyMeasurable (Function.uncurry (rotationIntegrand (n := n) β θ ℓ))
      (unitIntervalLaw.prod (disorderPairLaw n)) :=
    (continuous_rotationIntegrand (n := n) β θ ℓ).aestronglyMeasurable
  apply (integrable_prod_iff hm).2
  constructor
  · exact ae_of_all _ (fun s => rotated_directionalEnergy_exp_integrable β (ℓ * θ) (θ * s))
  · have hmeas := hm.norm.integral_prod_right'
    apply (integrable_const (Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4))).mono' hmeas
    filter_upwards [] with s
    have hn0 : 0 ≤ ∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n :=
      integral_nonneg (fun _ => norm_nonneg _)
    change |∫ p, ‖rotationIntegrand β θ ℓ s p‖ ∂disorderPairLaw n| ≤ _
    rw [abs_of_nonneg hn0]
    simp only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s)

theorem rotation_exp_integrable {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
  have hright := (rotationIntegrand_integrable hn β θ ℓ).integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  apply hright.mono' hc.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.uncurry_apply_pair, rotationIntegrand, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)] using
    rotation_exp_jensen β θ ℓ p

theorem rotation_exp_integral_le {n : ℕ} (hn : 0 < n) (β θ ℓ : ℝ) :
    (∫ p : Disorder n × Disorder n,
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))
        ∂disorderPairLaw n) ≤
      Real.exp (ℓ ^ 2 * θ ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) := by
  have hf := rotationIntegrand_integrable hn β θ ℓ
  have hright : Integrable (fun p : Disorder n × Disorder n =>
      ∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) (disorderPairLaw n) :=
    hf.integral_prod_right
  have hc : Continuous (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact ((continuous_logPartition β).comp
      ((rotateDisorderCLM n θ).continuous.fst)).sub
      ((continuous_logPartition β).comp continuous_fst)
  have hleft : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β (rotateDisorder θ p).1 - logPartition β p.1)))
      (disorderPairLaw n) := by
    apply hright.mono' hc.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [rotationIntegrand, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using rotation_exp_jensen β θ ℓ p
  calc
    _ ≤ ∫ p, (∫ s, rotationIntegrand β θ ℓ s p ∂unitIntervalLaw) ∂disorderPairLaw n :=
      integral_mono hleft hright (rotation_exp_jensen β θ ℓ)
    _ = ∫ s, (∫ p, rotationIntegrand β θ ℓ s p ∂disorderPairLaw n) ∂unitIntervalLaw :=
      (integral_integral_swap hf).symm
    _ ≤ ∫ _s, Real.exp ((ℓ * θ * β) ^ 2 * ((n : ℝ) - 1) / 4) ∂unitIntervalLaw :=
      integral_mono hf.integral_prod_left (integrable_const _)
        (fun s => rotated_directionalEnergy_exp_integral_le hn β (ℓ * θ) (θ * s))
    _ = _ := by
      simp only [integral_const, probReal_univ, one_smul]
      congr 1
      ring

@[simp] theorem rotateDisorder_pi_div_two_fst {n : ℕ} (p : Disorder n × Disorder n) :
    (rotateDisorder (Real.pi / 2) p).1 = p.2 := by
  funext e
  simp [rotateDisorder, mixDisorder]

theorem logPartition_difference_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.2 - logPartition β p.1))) (disorderPairLaw n) := by
  simpa only [rotateDisorder_pi_div_two_fst] using
    rotation_exp_integrable hn β (Real.pi / 2) ℓ

theorem logPartition_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n => Real.exp (ℓ * logPartition β J)) (disorderLaw n) := by
  have hp := logPartition_difference_exp_integrable hn β ℓ
  obtain ⟨J, hJ⟩ := hp.prod_right_ae.exists
  have hi := hJ.const_mul (Real.exp (ℓ * logPartition β J))
  convert hi using 1
  funext K
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_integrable {n : ℕ} (hn : 0 < n) (β : ℝ) :
    Integrable (logPartition (n := n) β) (disorderLaw n) := by
  have hp := logPartition_exp_integrable hn β 1
  have hm := logPartition_exp_integrable hn β (-1)
  apply (hp.add hm).mono' (continuous_logPartition β).aestronglyMeasurable
  filter_upwards [] with J
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have h := Real.add_one_le_exp (-logPartition β J)
    have he := Real.exp_pos (1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith
  · have h := Real.add_one_le_exp (logPartition β J)
    have he := Real.exp_pos (-1 * logPartition β J)
    simp only [Pi.add_apply, one_mul, neg_one_mul] at *
    linarith

theorem logPartition_centered_exp_jensen {n : ℕ} (hn : 0 < n) (β ℓ : ℝ)
    (J : Disorder n) :
    Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ≤
      ∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n := by
  have hl : Integrable (fun K : Disorder n => ℓ * (logPartition β J - logPartition β K))
      (disorderLaw n) := ((integrable_const _).sub (logPartition_integrable hn β)).const_mul ℓ
  have he : Integrable (fun K : Disorder n =>
      Real.exp (ℓ * (logPartition β J - logPartition β K))) (disorderLaw n) := by
    have h := (logPartition_exp_integrable hn β (-ℓ)).const_mul
      (Real.exp (ℓ * logPartition β J))
    convert h using 1
    funext K
    rw [← Real.exp_add]
    congr 1
    ring
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => Set.mem_univ _)) hl he
  convert hj using 2
  rw [integral_const_mul, integral_sub (integrable_const _) (logPartition_integrable hn β)]
  simp

theorem logPartition_centered_exp_integrable {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    Integrable (fun J : Disorder n =>
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)))
      (disorderLaw n) := by
  have h := (logPartition_exp_integrable hn β ℓ).const_mul
    (Real.exp (-ℓ * ∫ K, logPartition β K ∂disorderLaw n))
  convert h using 1
  funext J
  rw [← Real.exp_add]
  congr 1
  ring

theorem logPartition_centered_exp_integral_le {n : ℕ} (hn : 0 < n) (β ℓ : ℝ) :
    (∫ J : Disorder n,
      Real.exp (ℓ * (logPartition β J - ∫ K, logPartition β K ∂disorderLaw n)) ∂disorderLaw n) ≤
      Real.exp (ℓ ^ 2 * Real.pi ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 16) := by
  have hf : Integrable (fun p : Disorder n × Disorder n =>
      Real.exp (ℓ * (logPartition β p.1 - logPartition β p.2))) (disorderPairLaw n) := by
    convert logPartition_difference_exp_integrable hn β (-ℓ) using 1
    funext p
    congr 1
    ring
  calc
    _ ≤ ∫ J, (∫ K, Real.exp (ℓ * (logPartition β J - logPartition β K)) ∂disorderLaw n)
        ∂disorderLaw n := integral_mono (logPartition_centered_exp_integrable hn β ℓ)
          hf.integral_prod_left (logPartition_centered_exp_jensen hn β ℓ)
    _ = ∫ p : Disorder n × Disorder n,
        Real.exp ((-ℓ) * (logPartition β (rotateDisorder (Real.pi / 2) p).1 -
          logPartition β p.1)) ∂disorderPairLaw n := by
      rw [← integral_prod _ hf]
      apply integral_congr_ae
      filter_upwards [] with p
      rw [rotateDisorder_pi_div_two_fst]
      congr 1
      ring
    _ ≤ Real.exp ((-ℓ) ^ 2 * (Real.pi / 2) ^ 2 * β ^ 2 * ((n : ℝ) - 1) / 4) :=
      rotation_exp_integral_le hn β (Real.pi / 2) (-ℓ)
    _ = _ := by congr 1; ring

end SK
end
end
end

end OAI
