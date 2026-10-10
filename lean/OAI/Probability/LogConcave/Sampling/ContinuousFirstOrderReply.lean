import Mathlib
import OAI.Probability.LogConcave.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling

theorem Admissible.continuous_firstOrderReply {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Continuous (firstOrderReply V) := by
  have hg : Continuous (gradient V) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp
      (hV.smooth.continuous_fderiv (by norm_num))
  exact hV.smooth.continuous.prodMk hg

theorem OracleAlgorithm.measurable_history {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) {V : Point d → ℝ} (hV : Admissible V) (n : ℕ) :
    Measurable (fun ω => A.history V ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      by_cases hn : n < q
      · have hr : Measurable (fun ω =>
            firstOrderReply V (A.query ⟨n, hn⟩ (ω, A.history V ω n))) :=
          hV.continuous_firstOrderReply.measurable.comp
            ((A.query_measurable ⟨n, hn⟩).comp (measurable_id.prodMk ih))
        apply Measurable.of_eval
        intro i
        by_cases hi : i = ⟨n, hn⟩
        · simpa [history, hn, Function.update_apply, hi] using hr
        · simpa [history, hn, Function.update_apply, hi, Function.comp_def] using
            (measurable_pi_apply i).comp ih
      · simpa [history, hn] using ih

theorem OracleAlgorithm.measurable_run {Ω : Type*} [MeasurableSpace Ω] {d q : ℕ}
    (A : OracleAlgorithm Ω d q) {V : Point d → ℝ} (hV : Admissible V) :
    Measurable (A.run V) :=
  A.output_measurable.comp (measurable_id.prodMk (A.measurable_history hV q))

theorem queryComplexity_le_of_canSample {d q : ℕ} (h : CanSample d q) :
    queryComplexity d ≤ (q : ℕ∞) :=
  sInf_le ⟨q, h, rfl⟩

end LogConcaveSampling

namespace LogConcaveSampling
open scoped RealInnerProductSpace

theorem quadratic_lower_bound_of_hasDerivAt {f g h : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (ha : ∀ t, a ≤ h t) :
    f 0 + g 0 + a / 2 ≤ f 1 := by
  have hd : ∀ t, HasDerivAt (fun s => g s - a * s) (h t - a) t := fun t => by
    convert! (hg t).sub ((hasDerivAt_id t).const_mul a) using 1
    simp
  have hm : Monotone (fun t => g t - a * t) :=
    monotone_of_hasDerivAt_nonneg hd (fun t => sub_nonneg.mpr (ha t))
  have hgt : ∀ t, 0 ≤ t → g 0 + a * t ≤ g t := by
    intro t ht
    have hh := hm ht
    dsimp at hh
    linarith
  have he : ∀ t, HasDerivAt (fun s => f s - g 0 * s - a / 2 * s ^ 2)
      (g t - g 0 - a * t) t := fun t => by
    convert! ((hf t).sub ((hasDerivAt_id t).const_mul (g 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (a / 2)) using 1
    simp
    ring
  have hem : MonotoneOn (fun t => f t - g 0 * t - a / 2 * t ^ 2) (Set.Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => (he t).continuousAt.continuousWithinAt)
      (fun t _ => (he t).hasDerivWithinAt)
      (fun t ht => by
        have ht0 : 0 ≤ t := Set.mem_Ici.mp (interior_subset ht)
        have := hgt t ht0
        linarith)
  have hend := hem (by simp : (0 : ℝ) ∈ Set.Ici 0) (by simp : (1 : ℝ) ∈ Set.Ici 0)
      (by norm_num : (0 : ℝ) ≤ 1)
  dsimp at hend
  norm_num at hend
  linarith

theorem quadratic_bounds_of_hasDerivAt {f g h : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (hb : ∀ t, a ≤ h t ∧ h t ≤ b) :
    f 0 + g 0 + a / 2 ≤ f 1 ∧ f 1 ≤ f 0 + g 0 + b / 2 := by
  refine ⟨quadratic_lower_bound_of_hasDerivAt hf hg (fun t => (hb t).1), ?_⟩
  have hn := quadratic_lower_bound_of_hasDerivAt
    (fun t => (hf t).neg) (fun t => (hg t).neg)
    (a := -b) (fun t => neg_le_neg (hb t).2)
  dsimp at hn
  linarith

theorem Admissible.contDiff_gradient {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : ContDiff ℝ 1 (gradient V) := by
  exact (InnerProductSpace.toDual ℝ (Point d)).symm.contDiff.comp
    (hV.smooth.fderiv_right (by norm_num))

theorem Admissible.quadratic_bounds {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) (x : Point d) :
    ‖x‖ ^ 2 / 2 ≤ V x ∧ V x ≤ ‖x‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => V (t • x)
  let g : ℝ → ℝ := fun t => inner ℝ x (gradient V (t • x))
  let h : ℝ → ℝ := fun t => inner ℝ x (fderiv ℝ (gradient V) (t • x) x)
  have hp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => s • x) x t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hdg := hV.contDiff_gradient.differentiable (by norm_num)
  have hf : ∀ t, HasDerivAt f (g t) t := by
    intro t
    have hh := ((hV.smooth.differentiable (by norm_num) (t • x)).hasFDerivAt).comp_hasDerivAt t (hp t)
    convert! hh using 1
    change inner ℝ x (gradient V (t • x)) = fderiv ℝ V (t • x) x
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hg : ∀ t, HasDerivAt g (h t) t := by
    intro t
    have hh := (hdg (t • x)).hasFDerivAt.comp_hasDerivAt t (hp t)
    simpa [g, h, Function.comp_def] using
      (hasDerivAt_const t x).inner ℝ hh
  have ht := quadratic_bounds_of_hasDerivAt hf hg
    (fun t => hV.hessian_bounds (t • x) x)
  dsimp only [f, g] at ht
  rw [zero_smul, one_smul, hV.value_zero, hV.gradient_zero, inner_zero_right, zero_add] at ht
  constructor <;> linarith [ht.1, ht.2]

theorem integrable_gaussian_envelope (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Point d => Real.exp (-b * ‖x‖ ^ 2)) := by
  have hg := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Point d) (b := (b : ℂ)) (by exact hb) 0 0).norm
  convert! hg using 1
  funext x
  simp [Complex.norm_exp, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

theorem Admissible.integrable_exp_neg {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : Integrable (fun x => Real.exp (-V x)) := by
  apply (integrable_gaussian_envelope d (b := 1 / 2) (by norm_num)).mono'
    ((Real.continuous_exp.comp hV.smooth.continuous.neg).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, Pi.neg_apply]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have := (hV.quadratic_bounds x).1
    linarith

theorem Admissible.partition_ne_top {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : partition V ≠ ⊤ := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    hV.integrable_exp_neg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (Real.exp_pos (-V x)).le)).2
      hV.integrable_exp_neg

theorem Admissible.partition_pos {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : 0 < partition V := by
  have hm : Measurable (gibbsDensity V) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hV.smooth.continuous.neg)).measurable
  rw [partition, lintegral_pos_iff_support hm]
  have hs : Function.support (gibbsDensity V) = Set.univ := by
    ext x
    simp [Function.mem_support, gibbsDensity, not_le_of_gt (Real.exp_pos (-V x))]
  rw [hs]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

theorem Admissible.isProbabilityMeasure_gibbs {d : ℕ} {V : Point d → ℝ}
    (hV : Admissible V) : IsProbabilityMeasure (gibbs V) := by
  constructor
  rw [gibbs, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hV.partition_pos.ne' hV.partition_ne_top

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
