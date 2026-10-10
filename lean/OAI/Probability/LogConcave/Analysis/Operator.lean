import Mathlib
import OAI.Probability.LogConcave.Analysis.ProposalLog
import OAI.Probability.LogConcave.Analysis.EulerDrift

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma gaussian_noise_product (n : ℕ) :
    (Measure.pi (fun _ : Fin n => stdGaussian E)).map (toLp 2) =
      stdGaussian (PiLp 2 (fun _ : Fin n => E)) := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_pi,charFun_stdGaussian,← Complex.exp_sum]
  congr 1
  rw [← Complex.ofReal_pow, PiLp.norm_sq_eq_of_L2]
  simp only [Complex.ofReal_sum,Complex.ofReal_pow]
  rw [← Finset.sum_neg_distrib,Finset.sum_div]

lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) : Integrable f μ :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x))

def operator (T : E → E) (σ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  ∫ z, f (T x+σ • z) ∂stdGaussian E

lemma measurable_operator {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) : Measurable (operator T σ f) := by
  exact (hf.comp ((hT.comp measurable_fst).add (measurable_snd.const_smul σ))).stronglyMeasurable.integral_prod_right'.measurable

omit [BorelSpace E] in
lemma operator_bound (T : E → E) (σ : ℝ) {f : E → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (x : E) : |operator T σ f x| ≤ B := by
  have hn := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (f := fun z => f (T x+σ • z))
    (Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hb (T x+σ • z)))
  simpa only [operator,Real.norm_eq_abs,probReal_univ,mul_one] using hn

omit [BorelSpace E] in
lemma operator_zero (T : E → E) (σ : ℝ) : operator T σ (fun _ => 0) = fun _ => 0 := by
  funext x
  simp [operator]

theorem iterated_defect {T : E → E} (hT : Measurable T) (σ : ℝ)
    (μ : Measure E) [IsProbabilityMeasure μ] {D : ℝ}
    (hD : ∀ (f : E → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B →
      (∀ x, |f x| ≤ B) → |(∫ x, operator T σ f x ∂μ)-∫ x, f x ∂μ| ≤ B*D)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |f x| ≤ B)
    (n : ℕ) :
    |(∫ x, ((operator T σ)^[n] f) x ∂μ)-∫ x, f x ∂μ| ≤ (n:ℝ)*B*D := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hm := measurable_operator hT σ hf
      have hbound := operator_bound T σ hb
      have ha := ih hm hbound
      have hd := hD f hf B hB hb
      have ht := abs_sub_le (∫ x, ((operator T σ)^[n] (operator T σ f)) x ∂μ)
        (∫ x, operator T σ f x ∂μ) (∫ x, f x ∂μ)
      push_cast
      nlinarith only [ha,hd,ht]

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma measurable_iterate {T : E → E} (hT : Measurable T) (σ : ℝ) (n : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] {x : Ω → E} (hx : Measurable x)
    {g : Ω → Fin n → E} (hg : ∀ i, Measurable (fun z => g z i)) :
    Measurable (fun z => iterate T σ n (x z) (g z)) := by
  induction n with
  | zero => exact hx
  | succ n ih =>
      exact (hT.comp (ih (fun i => hg i.castSucc))).add ((hg (Fin.last n)).const_smul σ)

lemma integral_iterate {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (n : ℕ) (x : E) :
    (∫ g : Fin n → E, f (iterate T σ n x g) ∂Measure.pi (fun _ => stdGaussian E)) =
      ((operator T σ)^[n] f) x := by
  induction n generalizing f with
  | zero => simp [iterate]
  | succ n ih =>
      have hm : Measurable (fun p : E × (Fin n → E) => f (T (iterate T σ n x p.2)+σ • p.1)) := by
        exact hf.comp ((hT.comp (measurable_iterate hT σ n measurable_const
          (fun i => (measurable_pi_apply i).comp measurable_snd))).add (measurable_fst.const_smul σ))
      have hi := bounded_integrable (μ := (stdGaussian E).prod (Measure.pi (fun _ : Fin n => stdGaussian E)))
        hm (fun p => hb (T (iterate T σ n x p.2)+σ • p.1))
      have he : (∫ g : Fin (n+1) → E, f (iterate T σ (n+1) x g) ∂Measure.pi (fun _ => stdGaussian E)) =
          ∫ p : E × (Fin n → E), f (T (iterate T σ n x p.2)+σ • p.1)
            ∂(stdGaussian E).prod (Measure.pi (fun _ => stdGaussian E)) := by
        rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => stdGaussian E) (Fin.last n)).symm).integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
          Equiv.coe_fn_mk,Fin.insertNth_last',iterate,Fin.snoc_castSucc,Fin.snoc_last]
      rw [he,integral_prod_symm _ hi]
      change (∫ g : Fin n → E, operator T σ f (iterate T σ n x g) ∂Measure.pi (fun _ => stdGaussian E)) = _
      rw [ih (measurable_operator hT σ hf) (operator_bound T σ hb),Function.iterate_succ_apply]

lemma integral_iterate_gaussian {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (n : ℕ) (x : E) :
    (∫ g : PiLp 2 (fun _ : Fin n => E), f (iterate T σ n x g) ∂stdGaussian _) =
      ((operator T σ)^[n] f) x := by
  rw [← gaussian_noise_product (E := E) n,integral_map (measurable_toLp 2 (Fin n → E)).aemeasurable]
  · exact integral_iterate hT σ hf hb n x
  · exact (hf.comp (measurable_iterate hT σ n measurable_const
      (fun i => (PiLp.proj 2 (fun _ : Fin n => E) i : PiLp 2 (fun _ : Fin n => E) →L[ℝ] E).continuous.measurable))).aestronglyMeasurable

omit [BorelSpace E] in
lemma iterate_operator_bound (T : E → E) (σ : ℝ) {f : E → ℝ} {B : ℝ}
    (hb : ∀ x, |f x| ≤ B) (n : ℕ) : ∀ x, |((operator T σ)^[n] f) x| ≤ B := by
  induction n generalizing f with
  | zero => exact hb
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (operator_bound T σ hb)

lemma measurable_iterate_operator {T : E → E} (hT : Measurable T) (σ : ℝ)
    {f : E → ℝ} (hf : Measurable f) (n : ℕ) : Measurable ((operator T σ)^[n] f) := by
  induction n generalizing f with
  | zero => exact hf
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact ih (measurable_operator hT σ hf)

lemma iterate_operator_modulus {q : ℝ≥0} {T : E → E} (hT : LipschitzWith q T)
    (σ : ℝ) {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    {δ ε : ℝ} (hmod : ∀ x y, dist x y < δ → |f x-f y| ≤ ε)
    (n : ℕ) {x y : E} (hxy : (q:ℝ)^n*dist x y < δ) :
    |((operator T σ)^[n] f) x-((operator T σ)^[n] f) y| ≤ ε := by
  have hi (x : E) : Integrable (fun g : Fin n → E => f (iterate T σ n x g))
      (Measure.pi (fun _ => stdGaussian E)) := bounded_integrable (μ := Measure.pi (fun _ : Fin n => stdGaussian E))
    (hf.comp (measurable_iterate hT.continuous.measurable σ n measurable_const
      (fun i => measurable_pi_apply i))) (fun g => hb (iterate T σ n x g))
  rw [← integral_iterate hT.continuous.measurable σ hf hb n x,
    ← integral_iterate hT.continuous.measurable σ hf hb n y,← integral_sub (hi x) (hi y)]
  have hh := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin n => stdGaussian E))
    (f := fun g => f (iterate T σ n x g)-f (iterate T σ n y g))
    (Filter.Eventually.of_forall (fun g => by
      rw [Real.norm_eq_abs]
      exact hmod _ _ ((initial_contraction hT σ n x y g).trans_lt hxy)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_collapse (μ : Measure E) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → E → E} (hT : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ) (N : ℕ → ℕ)
    (hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0))
    {f : E → ℝ} (hf : UniformContinuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x₀ : E) :
    Tendsto (fun k => (∫ x, ((operator (T k) (σ k))^[N k] f) x ∂μ)-
      ((operator (T k) (σ k))^[N k] f) x₀) atTop (𝓝 0) := by
  let F := fun k x => ((operator (T k) (σ k))^[N k] f) x-
    ((operator (T k) (σ k))^[N k] f) x₀
  have hm k : Measurable (F k) :=
    (measurable_iterate_operator (hT k).continuous.measurable (σ k) hf.continuous.measurable (N k)).sub measurable_const
  have hpoint (x : E) : Tendsto (fun k => F k x) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by positivity)
    have hd : Tendsto (fun k => (q k:ℝ)^(N k)*dist x x₀) atTop (𝓝 0) := by
      simpa only [zero_mul] using hq.mul_const (dist x x₀)
    filter_upwards [hd.eventually (gt_mem_nhds hδ)] with k hk
    rw [dist_zero_right,Real.norm_eq_abs]
    have hh := iterate_operator_modulus (hT k) (σ k) hf.continuous.measurable hb
      (fun a b hab => (le_of_lt (hmod hab) : dist (f a) (f b) ≤ ε/2)) (N k) hk
    exact hh.trans_lt (by linarith)
  have hh := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ => (0:ℝ)) (fun _ => (2*B:ℝ))
    (fun k => (hm k).aestronglyMeasurable) (integrable_const _) (fun k => ?_) ?_
  · have he (k : ℕ) : (∫ x, F k x ∂μ) =
        (∫ x, ((operator (T k) (σ k))^[N k] f) x ∂μ)-((operator (T k) (σ k))^[N k] f) x₀ := by
      rw [show F k = (fun x => ((operator (T k) (σ k))^[N k] f) x-
          ((operator (T k) (σ k))^[N k] f) x₀) from rfl,
        integral_sub (bounded_integrable
          (measurable_iterate_operator (hT k).continuous.measurable (σ k) hf.continuous.measurable (N k))
          (iterate_operator_bound (T k) (σ k) hb (N k))) (integrable_const _),
        integral_const,probReal_univ,one_smul]
    simpa only [he,integral_zero] using hh
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by
      have h₁ := iterate_operator_bound (T k) (σ k) hb (N k) x
      have h₂ := iterate_operator_bound (T k) (σ k) hb (N k) x₀
      linarith)
  · filter_upwards [] with x
    exact hpoint x

theorem expectations_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → E → E} (hT : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ) (N : ℕ → ℕ)
    (hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0))
    {D : ℕ → ℝ} (hD : Tendsto (fun k => (N k:ℝ)*D k) atTop (𝓝 0))
    (hstep : ∀ k (f : E → ℝ), Measurable f → ∀ B : ℝ, 0 ≤ B →
      (∀ x, |f x| ≤ B) → |(∫ x, operator (T k) (σ k) f x ∂μ)-∫ x, f x ∂μ| ≤ B*D k)
    {f : E → ℝ} (hf : UniformContinuous f) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |f x| ≤ B) (x₀ : E) :
    Tendsto (fun k => ((operator (T k) (σ k))^[N k] f) x₀) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have ha : Tendsto (fun k => (∫ x, ((operator (T k) (σ k))^[N k] f) x ∂μ)-∫ x, f x ∂μ)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hz : Tendsto (fun k => B*((N k:ℝ)*D k)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hD.const_mul B
    apply squeeze_zero (fun _ => norm_nonneg _) ?_ hz
    intro k
    simpa only [Real.norm_eq_abs,mul_assoc,mul_comm (N k:ℝ) B] using
      iterated_defect (hT k).continuous.measurable (σ k) μ (hstep k)
        hf.continuous.measurable hB hb (N k)
  have hb := integral_collapse μ hT σ N hq hf hb x₀
  have ht := (ha.sub hb).add_const (∫ x, f x ∂μ)
  convert! ht using 1
  · funext k; ring_nf
  · simp only [sub_self,zero_add]

end EulerGeometry
end LogConcaveSampling

namespace LogConcaveSampling
namespace EulerGeometry
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma compact_test_lipschitz {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨K,hK⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by norm_num))
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ f 0)).trans (hK 0)
  exact ⟨⟨K,hK0⟩,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num))
    (fun x => hK x)⟩

theorem poincare_of_euler_approximation (μ : Measure E) [IsProbabilityMeasure μ]
    {q : ℕ → ℝ≥0} {T : ℕ → E → E}
    (hT : ∀ k, ContDiff ℝ 1 (T k)) (hl : ∀ k, LipschitzWith (q k) (T k))
    (σ : ℕ → ℝ≥0) (N : ℕ → ℕ) (x₀ : E) {C : ℝ}
    (hC : ∀ k, (σ k:ℝ)^2*energy (q k) (N k) ≤ C)
    (hconv : ∀ f : E → ℝ, UniformContinuous f → (∃ B, ∀ x, |f x| ≤ B) →
      Tendsto (fun k => ((operator (T k) (σ k))^[N k] f) x₀) atTop (𝓝 (∫ x, f x ∂μ)))
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Var[f;μ] ≤ (Real.pi^2/8)*C*∫ x, ‖fderiv ℝ f x‖^2 ∂μ := by
  obtain ⟨K,hK⟩ := compact_test_lipschitz hf hc
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hf.continuous
  have hb : ∀ x, |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB
  have hd := hf.continuous_fderiv (by norm_num)
  obtain ⟨D,hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous hd
  have hf2 : HasCompactSupport (fun x => (f x)^2) :=
    hc.comp_left (g := fun y : ℝ => y^2) (by norm_num)
  have hd2 : HasCompactSupport (fun x => ‖fderiv ℝ f x‖^2) :=
    (hc.fderiv ℝ).norm.comp_left (g := fun y : ℝ => y^2) (by norm_num)
  have hb2 (x : E) : |(f x)^2| ≤ B^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg (f 0)).trans (hb 0))).mpr (hb x)
  have hd2b (x : E) : |‖fderiv ℝ f x‖^2| ≤ D^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hD x) 2
  have hm : MemLp f 2 μ := MemLp.of_bound hf.continuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall hB)
  have hfconv := hconv f (hc.uniformContinuous_of_continuous hf.continuous) ⟨B,hb⟩
  have hf2conv := hconv (fun x => (f x)^2)
    (hf2.uniformContinuous_of_continuous (hf.continuous.pow 2)) ⟨B^2,hb2⟩
  have hdconv := hconv (fun x => ‖fderiv ℝ f x‖^2)
    (hd2.uniformContinuous_of_continuous (hd.norm.pow 2)) ⟨D^2,hd2b⟩
  rw [variance_eq_sub hm]
  apply le_of_tendsto_of_tendsto (hf2conv.sub (hfconv.pow 2))
    (hdconv.const_mul ((Real.pi^2/8)*C))
  filter_upwards [] with k
  let X := fun g : PiLp 2 (fun _ : Fin (N k) => E) => iterate (T k) (σ k) (N k) x₀ g
  let A : ℝ≥0 := σ k * ⟨Real.sqrt (energy (q k) (N k)),Real.sqrt_nonneg _⟩
  have hX : ContDiff ℝ 1 X := contDiff_noise (hT k) (σ k) (N k) x₀
  have hXL : LipschitzWith A X := noise_lipschitz (hl k) (σ k) (N k) x₀
  have hp := GaussianPoincare.variance_lipschitz_image hX hXL hf hK
  have hmap {g : E → ℝ} (hg : Measurable g) {b : ℝ} (hb : ∀ x, |g x| ≤ b) :
      (∫ y, g y ∂(stdGaussian _).map X) = ((operator (T k) (σ k))^[N k] g) x₀ := by
    rw [integral_map hX.continuous.aemeasurable hg.aestronglyMeasurable]
    exact integral_iterate_gaussian (hT k).continuous.measurable (σ k) hg hb (N k) x₀
  have : IsProbabilityMeasure ((stdGaussian _).map X) := inferInstance
  have hmf : MemLp f 2 ((stdGaussian _).map X) := MemLp.of_bound
    hf.continuous.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hdm := hmap (g := fun x => ‖fderiv ℝ f x‖^2) (hd.norm.pow 2).measurable hd2b
  rw [variance_eq_sub hmf] at hp
  simp only [Pi.pow_apply] at hp
  rw [hmap (hf.continuous.measurable.pow_const 2) hb2,
    hmap hf.continuous.measurable hb,hdm] at hp
  have hA : (A:ℝ)^2 ≤ C := by
    change ((σ k:ℝ)*Real.sqrt (energy (q k) (N k)))^2 ≤ C
    rw [mul_pow,Real.sq_sqrt (energy_nonneg (q := (q k:ℝ)) (N k))]
    exact hC k
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hA (by positivity)) (by
      rw [← hdm]
      exact integral_nonneg (fun _ => sq_nonneg _)))

end EulerGeometry
end LogConcaveSampling
namespace LogConcaveSampling
namespace EulerGeometry
open Filter
open scoped Topology

theorem exists_consistent_schedule {R : ℝ → ℝ} (hR : Tendsto R (𝓝 0) (𝓝 0))
    (hR0 : ∀ s, 0 ≤ R s) {a : ℝ} (ha : 0 < a) :
    ∃ (N : ℕ → ℕ) (s : ℕ → ℝ),
      (∀ k, 0 < s k ∧ s k ≤ 1 ∧ (s k)^2 ≤ a ∧ (N k:ℝ)*(s k)^2=(k:ℝ)+1) ∧
      Tendsto (fun k => (N k:ℝ)*(2*(s k)^2*R (s k))) atTop (𝓝 0) := by
  have hex (k : ℕ) : ∃ n : ℕ, ∃ s : ℝ,
      (0 < s ∧ s ≤ 1 ∧ s^2 ≤ a ∧ (n:ℝ)*s^2=(k:ℝ)+1) ∧
      (n:ℝ)*(2*s^2*R s) ≤ 1/((k:ℝ)+1) := by
    let h : ℕ → ℝ := fun n => ((k:ℝ)+1)/((n:ℝ)+1)
    have ht : Tendsto h atTop (𝓝 0) := by
      simpa only [h,mul_one_div,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((k:ℝ)+1)
    have hs : Tendsto (fun n => Real.sqrt (h n)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero] using ht.sqrt
    have hr := hR.comp hs
    have hb : 0 < 1/(2*((k:ℝ)+1)^2) := by positivity
    obtain ⟨n,hn⟩ := ((ht.eventually (gt_mem_nhds ha)).and
      ((hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).and
        (hr.eventually (gt_mem_nhds hb)))).exists
    have hp : 0 < h n := by dsimp [h]; positivity
    refine ⟨n+1,Real.sqrt (h n),⟨Real.sqrt_pos.mpr hp,hn.2.1.le,?_,?_⟩,?_⟩
    · rw [Real.sq_sqrt hp.le]
      exact hn.1.le
    · rw [Real.sq_sqrt hp.le]
      dsimp [h]
      push_cast
      field_simp
    · rw [Real.sq_sqrt hp.le]
      have hh := mul_le_mul_of_nonneg_left hn.2.2.le (show 0 ≤ 2*((k:ℝ)+1) by positivity)
      have he : (n+1:ℝ)*(2*h n*R (Real.sqrt (h n))) = 2*((k:ℝ)+1)*R (Real.sqrt (h n)) := by
        dsimp [h]
        field_simp
      push_cast
      rw [he]
      convert! hh using 1
      field_simp
  choose N s hs using hex
  refine ⟨N,s,(fun k => (hs k).1),?_⟩
  apply squeeze_zero (fun k => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _)) (hR0 _))) (fun k => (hs k).2)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma contraction_geometric_bound {m h : ℝ} (_hm : 0 < m) (hh : 0 ≤ 1-m*h)
    (n k : ℕ) (hn : (n:ℝ)*h=(k:ℝ)+1) :
    (1-m*h)^n ≤ (Real.exp (-m))^(k+1) := by
  have hq : 1-m*h ≤ Real.exp (-m*h) := by
    nlinarith only [Real.add_one_le_exp (-m*h)]
  have hp := pow_le_pow_left₀ hh hq n
  rw [← Real.exp_nat_mul] at hp
  rw [← Real.exp_nat_mul]
  convert! hp using 1
  congr 1
  push_cast
  linear_combination m*hn

lemma schedule_contraction_tendsto {m : ℝ} (hm : 0 < m)
    (N : ℕ → ℕ) (s : ℕ → ℝ)
    (hq : ∀ k, 0 ≤ 1-m*(s k)^2)
    (hn : ∀ k, (N k:ℝ)*(s k)^2=(k:ℝ)+1) :
    Tendsto (fun k => (1-m*(s k)^2)^(N k)) atTop (𝓝 0) := by
  have he := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-m)).le
    (show Real.exp (-m) < 1 by simpa only [Real.exp_lt_one_iff] using neg_neg_of_pos hm)).comp
      (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun k => pow_nonneg (hq k) _) (fun k => contraction_geometric_bound hm (hq k) (N k) k (hn k)) he

end EulerGeometry
end LogConcaveSampling
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

lemma euler_noise_energy_bound {m h : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ) :
    2*h*EulerGeometry.energy (1-m*h) n ≤ 2/m := by
  have hq : 0 ≤ 1-m*h := by nlinarith
  have hq1 : 1-m*h < 1 := by nlinarith
  have hden : 0 < 1-(1-m*h)^2 := by nlinarith
  have he := mul_le_mul_of_nonneg_left (EulerGeometry.energy_le hq hq1 n) (by positivity : 0 ≤ 2*h)
  have hd : 2*h*(1-(1-m*h)^2)⁻¹ ≤ 2/m := by
    rw [← div_eq_mul_inv,div_le_div_iff₀ hden hm]
    have hp : m*h ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hm.le hh.le) (sub_nonneg.mpr hp)]
  exact he.trans hd

lemma euler_operator_gibbs_defect {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ 2 H) {M : ℝ≥0} (hM : LipschitzWith M (gradient H))
    [IsProbabilityMeasure (gibbs H)]
    (hp0 : partition H ≠ 0) (hpt : partition H ≠ ⊤)
    (hi : Integrable (fun z => ‖gradient H z‖^2) (gibbs H))
    {s : ℝ} (hs : s ≠ 0) (hs1 : |s| ≤ 1)
    {g : Point d → ℝ} (hg : Measurable g) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ z, |g z| ≤ B) :
    |(∫ z, EulerGeometry.operator (eulerDrift H (s^2)) (Real.sqrt 2*s) g z ∂gibbs H)-
      ∫ z, g z ∂gibbs H| ≤ B*(2*s^2*EulerDefect.rate H s) := by
  have he := EulerDefect.one_step_gibbs_defect hH hM hp0 hpt hi hs hs1 hg hB hb
  have hgm : Measurable (fun p : Point d × Point d => g (EulerDefect.proposal H s p.1 p.2)) :=
    hg.comp (EulerDefect.measurable_joint_map hH s).snd
  rw [integral_prod _ (EulerGeometry.bounded_integrable hgm
    (fun p => hb (EulerDefect.proposal H s p.1 p.2)))] at he
  exact he

theorem Primitive.poincare_compact {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) {f : Point d → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Var[f;gibbs (primitivePotential F x r)] ≤
      (Real.pi^2/8)*(2/(1-(lam:ℝ)*r^2))*∫ z, ‖fderiv ℝ f z‖^2 ∂gibbs (primitivePotential F x r) := by
  let H := primitivePotential F x r
  let m : ℝ := 1-(lam:ℝ)*r^2
  have hm : 0 < m := sub_pos.mpr hl
  have hm1 : m ≤ 1 := by
    dsimp [m]
    nlinarith [mul_nonneg lam.coe_nonneg (sq_nonneg r)]
  have hH : ContDiff ℝ 2 H := hF.contDiff_potential x r
  have hg := hF.gradient_potential_lipschitz x hr
  have hi := hF.gradient_sq_integrable x hr hl
  have hp0 : partition H ≠ 0 := (partition_pos_of_continuous hH.continuous).ne'
  have hpt : partition H ≠ ⊤ := partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr hl)
  have : IsProbabilityMeasure (gibbs H) := probability_gibbs_of_partition hp0 hpt
  obtain ⟨N,s,hs,hD⟩ := EulerGeometry.exists_consistent_schedule
    (EulerDefect.rate_tendsto hH hg hi) (EulerDefect.rate_nonneg H) (a := 1) (by norm_num)
  let q : ℕ → ℝ≥0 := fun k => ⟨1-m*(s k)^2,by
    have hp := (hs k).2.2.1
    have hz := sq_nonneg (s k)
    nlinarith⟩
  let σ : ℕ → ℝ≥0 := fun k => ⟨Real.sqrt 2*s k,mul_nonneg (Real.sqrt_nonneg _) (hs k).1.le⟩
  let T := fun k => eulerDrift H ((s k)^2)
  have hTL (k : ℕ) : LipschitzWith (q k) (T k) := by
    have hh := hF.eulerDrift_lipschitz x hr (sq_nonneg (s k)) (hs k).2.2.1
    apply hh.weaken
    change 1-(s k)^2+(s k)^2*((lam:ℝ)*r^2) ≤ 1-m*(s k)^2
    dsimp [m]
    nlinarith
  have hTC (k : ℕ) : ContDiff ℝ 1 (T k) := hF.contDiff_eulerDrift x r ((s k)^2)
  have hq : Tendsto (fun k => (q k:ℝ)^(N k)) atTop (𝓝 0) :=
    EulerGeometry.schedule_contraction_tendsto hm N s (fun k => (q k).coe_nonneg)
      (fun k => (hs k).2.2.2)
  have hstep (k : ℕ) (g : Point d → ℝ) (hg' : Measurable g) (B : ℝ) (hB : 0 ≤ B)
      (hb : ∀ z, |g z| ≤ B) :
      |(∫ z, EulerGeometry.operator (T k) (σ k) g z ∂gibbs H)-∫ z, g z ∂gibbs H| ≤
        B*(2*(s k)^2*EulerDefect.rate H (s k)) := by
    exact euler_operator_gibbs_defect hH hg hp0 hpt hi (hs k).1.ne'
      (by rw [abs_of_pos (hs k).1]; exact (hs k).2.1) hg' hB hb
  have hconv (g : Point d → ℝ) (hg' : UniformContinuous g) (hb : ∃ B, ∀ z, |g z| ≤ B) :
      Tendsto (fun k => ((EulerGeometry.operator (T k) (σ k))^[N k] g) 0)
        atTop (𝓝 (∫ z, g z ∂gibbs H)) := by
    obtain ⟨B,hb⟩ := hb
    exact EulerGeometry.expectations_tendsto (gibbs H) hTL (fun k => (σ k:ℝ)) N hq hD hstep
      hg' ((abs_nonneg (g 0)).trans (hb 0)) hb 0
  apply EulerGeometry.poincare_of_euler_approximation (gibbs H) hTC hTL σ N 0
    (C := 2/m) ?_ hconv hf hc
  intro k
  change (Real.sqrt 2*s k)^2*EulerGeometry.energy (1-m*(s k)^2) (N k) ≤ 2/m
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  exact euler_noise_energy_bound hm hm1 (sq_pos_of_pos (hs k).1) (hs k).2.2.1 (N k)

end LogConcaveSampling

namespace LogConcaveSampling
namespace PoincareCutoff
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def bump : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
def cutoff (n : ℕ) (x : E) : ℝ := (bump (E := E)) (((n:ℝ)+1)⁻¹ • x)

lemma cutoff_smooth (n : ℕ) : ContDiff ℝ 1 (cutoff (E := E) n) :=
  ((bump (E := E)).contDiff).comp (contDiff_id.const_smul _)

lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff (E := E) n) := by
  exact (bump (E := E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((n:ℝ)+1)⁻¹) (by positivity))

lemma cutoff_nonneg (n : ℕ) (x : E) : 0 ≤ cutoff n x := (bump (E := E)).nonneg
lemma cutoff_le_one (n : ℕ) (x : E) : cutoff n x ≤ 1 := (bump (E := E)).le_one
lemma cutoff_abs (n : ℕ) (x : E) : |cutoff n x| ≤ 1 := by
  rw [abs_of_nonneg (cutoff_nonneg n x)]
  exact cutoff_le_one n x

lemma cutoff_tendsto (x : E) : Tendsto (fun n => cutoff n x) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0))
  have hh := (((bump (E := E)).contDiff (n := 1)).continuous.tendsto (0:E)).comp
    (show Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹ • x) atTop (𝓝 (0:E)) by simpa only [zero_smul] using ht.smul_const x)
  have he : (bump (E := E)) (0:E) = 1 :=
    (bump (E := E)).one_of_mem_closedBall (by simp [bump])
  simpa only [cutoff,he,Function.comp_def] using hh

lemma exists_derivative_bound : ∃ K : ℝ≥0, ∀ n x,
    ‖fderiv ℝ (cutoff (E := E) n) x‖ ≤ (K:ℝ)*((n:ℝ)+1)⁻¹ := by
  have hc : ContDiff ℝ 1 (bump (E := E)) := (bump (E := E)).contDiff
  obtain ⟨B,hB⟩ := ((bump (E := E)).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hc.continuous_fderiv (by norm_num))
  let K : ℝ≥0 := ⟨B,(norm_nonneg (fderiv ℝ (bump (E := E)) 0)).trans (hB 0)⟩
  have hl : LipschitzWith K (bump (E := E)) :=
    lipschitzWith_of_nnnorm_fderiv_le (hc.differentiable (by norm_num)) (fun x => hB x)
  refine ⟨K,fun n x => ?_⟩
  have hs : LipschitzWith (K * ‖((n:ℝ)+1)⁻¹‖₊) (cutoff (E := E) n) :=
    hl.comp (lipschitzWith_smul (((n:ℝ)+1)⁻¹) (β := E))
  have hd := norm_fderiv_le_of_lipschitz ℝ hs (x₀ := x)
  simpa only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ ((n:ℝ)+1)⁻¹)] using hd

lemma cutoff_derivative_tendsto {K : ℝ≥0}
    (hK : ∀ n x, ‖fderiv ℝ (cutoff (E := E) n) x‖ ≤ (K:ℝ)*((n:ℝ)+1)⁻¹) (x : E) :
    Tendsto (fun n => fderiv ℝ (cutoff n) x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun n : ℕ => (K:ℝ)*((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (K:ℝ)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hK n x) ht

def truncation (f : E → ℝ) (n : ℕ) : E → ℝ := fun x => cutoff n x*f x

lemma truncation_smooth {f : E → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ContDiff ℝ 1 (truncation f n) := (cutoff_smooth n).mul hf

lemma truncation_compact (f : E → ℝ) (n : ℕ) : HasCompactSupport (truncation f n) :=
  (cutoff_compact n).mul_right

lemma truncation_tendsto (f : E → ℝ) (x : E) :
    Tendsto (fun n => truncation f n x) atTop (𝓝 (f x)) := by
  simpa only [truncation,one_mul] using (cutoff_tendsto x).mul_const (f x)

lemma truncation_derivative {f : E → ℝ} (hf : ContDiff ℝ 1 f) (n : ℕ) (x : E) :
    fderiv ℝ (truncation f n) x = cutoff n x • fderiv ℝ f x + f x • fderiv ℝ (cutoff n) x :=
  fderiv_fun_mul ((cutoff_smooth n).differentiable (by norm_num) x)
    (hf.differentiable (by norm_num) x)

lemma truncation_derivative_tendsto {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x : E) :
    Tendsto (fun n => fderiv ℝ (truncation f n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  obtain ⟨K,hK⟩ := exists_derivative_bound (E := E)
  simp_rw [truncation_derivative hf]
  simpa only [one_smul,smul_zero,add_zero] using
    ((cutoff_tendsto x).smul_const (fderiv ℝ f x)).add
      ((cutoff_derivative_tendsto hK x).const_smul (f x))

lemma truncation_abs (f : E → ℝ) (n : ℕ) (x : E) : |truncation f n x| ≤ |f x| := by
  rw [truncation,abs_mul]
  exact (mul_le_mul_of_nonneg_right (cutoff_abs n x) (abs_nonneg _)).trans_eq (one_mul _)

lemma truncation_derivative_bound {f : E → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hK : ∀ n x, ‖fderiv ℝ (cutoff (E := E) n) x‖ ≤ (K:ℝ)*((n:ℝ)+1)⁻¹) (n : ℕ) (x : E) :
    ‖fderiv ℝ (truncation f n) x‖ ≤ ‖fderiv ℝ f x‖ + (K:ℝ)*|f x| := by
  rw [truncation_derivative hf]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
  have hle : ((n:ℝ)+1)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hd := (hK n x).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hle K.coe_nonneg)
  calc
    _ ≤ 1*‖fderiv ℝ f x‖+|f x| * (K:ℝ) := add_le_add
      (mul_le_mul_of_nonneg_right (cutoff_abs n x) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
    _ = _ := by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem extend (μ : Measure E) [IsProbabilityMeasure μ] {β : ℝ}
    (hP : ∀ (g : E → ℝ), ContDiff ℝ 1 g → HasCompactSupport g →
      Var[g;μ] ≤ β*∫ x, ‖fderiv ℝ g x‖^2 ∂μ)
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hm : MemLp f 2 μ)
    (hd : Integrable (fun x => ‖fderiv ℝ f x‖^2) μ) :
    Var[f;μ] ≤ β*∫ x, ‖fderiv ℝ f x‖^2 ∂μ := by
  obtain ⟨K,hK⟩ := exists_derivative_bound (E := E)
  have hi : Integrable f μ := hm.integrable (by norm_num)
  have h2 : Integrable (fun x => (f x)^2) μ := hm.integrable_sq
  have ht1 : Tendsto (fun n => ∫ x, truncation f n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (truncation_smooth hf n).continuous.aestronglyMeasurable)
      hi.abs (fun n => Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using truncation_abs f n))
      (Filter.Eventually.of_forall (truncation_tendsto f))
  have ht2 : Tendsto (fun n => ∫ x, (truncation f n x)^2 ∂μ) atTop (𝓝 (∫ x, (f x)^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (f x)^2)
      (fun n => ((truncation_smooth hf n).continuous.pow 2).aestronglyMeasurable) h2
    · intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [sq_abs,Pi.pow_apply] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (truncation_abs f n x)
    · exact Filter.Eventually.of_forall (fun x => (truncation_tendsto f x).pow 2)
  have htd : Tendsto (fun n => ∫ x, ‖fderiv ℝ (truncation f n) x‖^2 ∂μ)
      atTop (𝓝 (∫ x, ‖fderiv ℝ f x‖^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => 2*(‖fderiv ℝ f x‖^2+(K:ℝ)^2*(f x)^2))
      (fun n => (((truncation_smooth hf n).continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable)
      ((hd.add (h2.const_mul ((K:ℝ)^2))).const_mul 2)
    · intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change ‖fderiv ℝ (truncation f n) x‖^2 ≤ _
      have hh := truncation_derivative_bound hf hK n x
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
      nlinarith [sq_nonneg (‖fderiv ℝ f x‖-(K:ℝ)*|f x|),sq_abs (f x)]
    · exact Filter.Eventually.of_forall (fun x => (truncation_derivative_tendsto hf x).norm.pow 2)
  rw [variance_eq_sub hm]
  simp only [Pi.pow_apply]
  apply le_of_tendsto_of_tendsto (ht2.sub (ht1.pow 2)) (htd.const_mul β)
  filter_upwards [] with n
  have hp := hP (truncation f n) (truncation_smooth hf n) (truncation_compact f n)
  have hmt : MemLp (truncation f n) 2 μ := hm.norm.mono'
    (truncation_smooth hf n).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using truncation_abs f n))
  simpa only [variance_eq_sub hmt,Pi.pow_apply] using hp

end PoincareCutoff
end LogConcaveSampling

end UpperProof
end
end
end

end OAI
