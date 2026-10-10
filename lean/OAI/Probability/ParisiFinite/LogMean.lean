import Mathlib
import OAI.Probability.ParisiFinite.Shape

namespace OAI

/-! Log Mean. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace ParisiFinite

 

def logMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (a : ℝ)
    (f : Ω → ℝ) : ℝ :=
  if a = 0 then ∫ z, f z ∂μ else Real.log (∫ z, Real.exp (a * f z) ∂μ) / a

 
def step (a s : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  logMean (gaussianReal 0 1) a (fun z => f (x + s * z))

 
def terminal (β x : ℝ) : ℝ := Real.log (2 * Real.cosh (β * x)) / β

lemma integral_exp_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable (fun z => Real.exp (f z)) μ) :
    0 < ∫ z, Real.exp (f z) ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (Real.exp_pos _).le) hf).2
  have h : Function.support (fun z => Real.exp (f z)) = Set.univ := by
    ext z
    simp [Function.mem_support, (Real.exp_pos (f z)).ne']
  rw [h, measure_univ]
  exact zero_lt_one

@[simp] lemma logMean_zero {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) : logMean μ 0 f = ∫ z, f z ∂μ := by simp [logMean]

@[simp] lemma logMean_const {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a c : ℝ) : logMean μ a (fun _ => c) = c := by
  by_cases ha : a = 0
  · simp [ha, logMean]
  · simp [logMean, ha, Real.log_exp, mul_div_cancel_left₀ _ ha]

lemma logMean_add_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun z => Real.exp (a * f z)) μ)
    (c : ℝ) : logMean μ a (fun z => f z + c) = logMean μ a f + c := by
  by_cases ha : a = 0
  · simp [logMean, ha, integral_add hf (integrable_const c)]
  · have hp := integral_exp_pos he
    simp only [logMean, ha, ↓reduceIte]
    simp_rw [mul_add, Real.exp_add]
    rw [integral_mul_const, Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp

 
lemma logMean_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hef : Integrable (fun z => Real.exp (a * f z)) μ)
    (heg : Integrable (fun z => Real.exp (a * g z)) μ)
    (hfg : ∀ z, f z ≤ g z) : logMean μ a f ≤ logMean μ a g := by
  by_cases h0 : a = 0
  · simp only [logMean, h0, ↓reduceIte]
    exact integral_mono hf hg hfg
  · simp only [logMean, h0, ↓reduceIte]
    apply div_le_div_of_nonneg_right _ ha
    apply Real.log_le_log (integral_exp_pos hef)
    exact integral_mono hef heg fun z => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hfg z) ha)

 
lemma integrable_exp_abs (c : ℝ) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (gaussianReal 0 1) := by
  apply ((integrable_exp_mul_gaussianReal c).add
    (integrable_exp_mul_gaussianReal (-c))).mono'
    (by fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hz]
    have he : c * -z = -c * z := by ring
    rw [he]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

lemma shift_norm_le {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (x s z : ℝ) : |f (x + s * z)| ≤ |f x| + (L : ℝ) * |s| * |z| := by
  have h := hf.dist_le_mul (x + s * z) x
  simp only [Real.dist_eq, add_sub_cancel_left, abs_mul] at h
  have htri := abs_add_le (f (x + s * z) - f x) (f x)
  rw [sub_add_cancel] at htri
  nlinarith

lemma integrable_shift {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (x s : ℝ) : Integrable (fun z => f (x + s * z)) (gaussianReal 0 1) := by
  have hi : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := 0) (v := 1) 1)).abs
  apply ((integrable_const |f x|).add (hi.const_mul ((L : ℝ) * |s|))).mono'
    (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  exact ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using shift_norm_le hf x s z

lemma integrable_exp_shift {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a x s : ℝ) : Integrable (fun z => Real.exp (a * f (x + s * z)))
      (gaussianReal 0 1) := by
  apply ((integrable_exp_abs (|a| * (L : ℝ) * |s|)).const_mul
    (Real.exp (|a| * |f x|))).mono'
    (Real.continuous_exp.comp ((hf.continuous.comp (show Continuous (fun z : ℝ => x + s * z) by fun_prop)).const_mul a)).aestronglyMeasurable
  filter_upwards with z
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (shift_norm_le hf x s z) (abs_nonneg a)
  have h' : a * f (x + s * z) ≤ |a| * |f (x + s * z)| := by
    simpa only [abs_mul] using le_abs_self (a * f (x + s * z))
  nlinarith

 
lemma step_integrals {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s x : ℝ) :
    Integrable (fun z => f (x + s * z)) (gaussianReal 0 1) ∧
    Integrable (fun z => Real.exp (a * f (x + s * z))) (gaussianReal 0 1) ∧
    0 < ∫ z, Real.exp (a * f (x + s * z)) ∂gaussianReal 0 1 :=
  ⟨integrable_shift hf x s, integrable_exp_shift hf a x s,
    integral_exp_pos (integrable_exp_shift hf a x s)⟩

lemma logMean_le_add {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hef : Integrable (fun z => Real.exp (a * f z)) μ)
    (heg : Integrable (fun z => Real.exp (a * g z)) μ)
    (c : ℝ) (hfg : ∀ z, f z ≤ g z + c) : logMean μ a f ≤ logMean μ a g + c := by
  have hec : Integrable (fun z => Real.exp (a * (g z + c))) μ := by
    simpa only [mul_add, Real.exp_add] using heg.mul_const (Real.exp (a * c))
  exact (logMean_mono ha hf (hg.add (integrable_const c)) hef hec hfg).trans_eq
    (logMean_add_const hg heg c)

lemma logMean_stable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hef : Integrable (fun z => Real.exp (a * f z)) μ)
    (heg : Integrable (fun z => Real.exp (a * g z)) μ)
    (c : ℝ) (hfg : ∀ z, |f z - g z| ≤ c) :
    |logMean μ a f - logMean μ a g| ≤ c := by
  rw [abs_le]
  constructor
  · have h := logMean_le_add ha hg hf heg hef c (fun z => by
      have hz := (abs_le.mp (hfg z)).1
      linarith)
    linarith
  · have h := logMean_le_add ha hf hg hef heg c (fun z => by
      have hz := (abs_le.mp (hfg z)).2
      linarith)
    linarith

 
lemma step_lipschitz {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {a : ℝ} (ha : 0 ≤ a) (s : ℝ) : LipschitzWith L (step a s f) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  simp only [Real.norm_eq_abs, step]
  apply logMean_stable ha (integrable_shift hf x s) (integrable_shift hf y s)
    (integrable_exp_shift hf a x s) (integrable_exp_shift hf a y s)
  intro z
  have h := hf.dist_le_mul (x + s * z) (y + s * z)
  simpa only [Real.dist_eq, add_sub_add_right_eq_sub] using h

lemma hasDerivAt_terminal {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (terminal β) (Real.tanh (β * x)) x := by
  have hc : HasDerivAt (fun y : ℝ => 2 * Real.cosh (β * y))
      (2 * (Real.sinh (β * x) * β)) x := by
    simpa using ((Real.hasDerivAt_cosh (β * x)).comp x
      ((hasDerivAt_id x).const_mul β)).const_mul (2 : ℝ)
  have hh := (hc.log (mul_pos (by norm_num) (Real.cosh_pos _)).ne').div_const β
  have he : (2 * (Real.sinh (β * x) * β) / (2 * Real.cosh (β * x))) / β =
      Real.tanh (β * x) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [he] at hh
  exact hh

lemma terminal_lipschitz {β : ℝ} (hβ : 0 < β) : LipschitzWith 1 (terminal β) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_terminal hβ x).differentiableAt)
  intro x
  rw [(hasDerivAt_terminal hβ x).deriv]
  exact_mod_cast (Real.abs_tanh_lt_one (β * x)).le

@[simp] lemma step_zero_width (a : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    step a 0 f x = f x := by
  simp [step]

@[simp] lemma terminal_zero (β : ℝ) : terminal β 0 = Real.log 2 / β := by
  simp [terminal]

lemma terminal_even (β x : ℝ) : terminal β (-x) = terminal β x := by
  simp [terminal, mul_neg]

lemma integral_exp_linear (a : ℝ) :
    (∫ z : ℝ, Real.exp (a * z) ∂gaussianReal 0 1) = Real.exp (a ^ 2 / 2) := by
  have h := mgf_gaussianReal (μ := 0) (v := 1) (X := fun z : ℝ => z) (p := gaussianReal 0 1)
    (by simp) a
  simpa [mgf] using h

lemma exp_terminal {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    Real.exp (β * terminal β x) = 2 * Real.cosh (β * x) := by
  unfold terminal
  have he : β * (Real.log (2 * Real.cosh (β * x)) / β) =
      Real.log (2 * Real.cosh (β * x)) := by field_simp
  rw [he, Real.exp_log (mul_pos (by norm_num) (Real.cosh_pos _))]

lemma exp_terminal_shift {β : ℝ} (hβ : 0 < β) (x s z : ℝ) :
    Real.exp (β * terminal β (x + s * z)) =
      Real.exp (β * x) * Real.exp ((β * s) * z) +
      Real.exp (-(β * x)) * Real.exp ((-(β * s)) * z) := by
  rw [exp_terminal hβ, Real.cosh_eq]
  have h₁ : β * (x + s * z) = β * x + (β * s) * z := by ring
  have h₂ : -(β * (x + s * z)) = -(β * x) + (-(β * s)) * z := by ring
  rw [h₂, h₁, Real.exp_add, Real.exp_add]
  ring

lemma integral_exp_terminal {β : ℝ} (hβ : 0 < β) (x s : ℝ) :
    (∫ z, Real.exp (β * terminal β (x + s * z)) ∂gaussianReal 0 1) =
      (2 * Real.cosh (β * x)) * Real.exp ((β * s) ^ 2 / 2) := by
  simp_rw [exp_terminal_shift hβ]
  rw [integral_add ((integrable_exp_mul_gaussianReal (β * s)).const_mul _)
    ((integrable_exp_mul_gaussianReal (-(β * s))).const_mul _)]
  rw [integral_const_mul, integral_const_mul, integral_exp_linear, integral_exp_linear]
  rw [neg_sq, Real.cosh_eq]
  ring

 

lemma step_terminal {β : ℝ} (hβ : 0 < β) (s x : ℝ) :
    step β s (terminal β) x = terminal β x + β * s ^ 2 / 2 := by
  unfold step logMean
  rw [ite_eq_right hβ.ne', integral_exp_terminal hβ,
    Real.log_mul (mul_pos (by norm_num) (Real.cosh_pos _)).ne' (Real.exp_pos _).ne',
    Real.log_exp]
  unfold terminal
  field_simp

 

abbrev Schedule := List (ℝ≥0 × ℝ≥0)

 
def recursion (β : ℝ) : Schedule → ℝ → ℝ
  | [] => terminal β
  | (a, d) :: ls => step a (Real.sqrt d) (recursion β ls)

 
def penalty (t : ℝ) : Schedule → ℝ
  | [] => 0
  | (a, d) :: ls => a * ((t + d) ^ 2 - t ^ 2) / 4 + penalty (t + d) ls

def width (ls : Schedule) : ℝ := (ls.map (fun l => (l.2 : ℝ))).sum

 
def Admissible (β : ℝ) (ls : Schedule) : Prop :=
  width ls = 1 ∧ ls.Pairwise (fun a b => a.1 ≤ b.1) ∧ ∀ l ∈ ls, (l.1 : ℝ) ≤ β

def functional (β : ℝ) (ls : Schedule) : ℝ := recursion β ls 0 - penalty 0 ls

lemma recursion_lipschitz {β : ℝ} (hβ : 0 < β) (ls : Schedule) :
    LipschitzWith 1 (recursion β ls) := by
  induction ls with
  | nil => exact terminal_lipschitz hβ
  | cons l ls ih => exact step_lipschitz ih l.1.coe_nonneg _

lemma recursion_integrals {β : ℝ} (hβ : 0 < β) (ls : Schedule) (a s x : ℝ) :
    Integrable (fun z => recursion β ls (x + s * z)) (gaussianReal 0 1) ∧
    Integrable (fun z => Real.exp (a * recursion β ls (x + s * z))) (gaussianReal 0 1) ∧
    0 < ∫ z, Real.exp (a * recursion β ls (x + s * z)) ∂gaussianReal 0 1 :=
  step_integrals (recursion_lipschitz hβ ls) a s x

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal Topology
namespace ParisiFinite

lemma step_add_const {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a s c x : ℝ) : step a s (fun y => f y + c) x = step a s f x + c :=
  logMean_add_const (integrable_shift hf x s) (integrable_exp_shift hf a x s) c

lemma step_mean (s : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    step 0 s f x = ∫ z, f (x + s * z) ∂gaussianReal 0 1 := by simp [step]

 
def replicaSymmetricSchedule (β : ℝ≥0) (q : ℝ≥0) : Schedule :=
  [(0, q), (β, 1 - q)]

lemma replicaSymmetric_admissible (β q : ℝ≥0) (hq : q ≤ 1) :
    Admissible β (replicaSymmetricSchedule β q) := by
  simp [Admissible, replicaSymmetricSchedule, width, NNReal.coe_sub hq]

lemma replicaSymmetric_recursion {β : ℝ≥0} (hβ : 0 < β) (q : ℝ≥0) (hq : q ≤ 1) (x : ℝ) :
    recursion β (replicaSymmetricSchedule β q) x =
      step 0 (Real.sqrt q) (terminal β) x + β * (1 - q) / 2 := by
  have hβ' : (0 : ℝ) < β := hβ
  have htail : (fun y => step (β : ℝ) (Real.sqrt (↑(1-q) : ℝ)) (terminal β) y) =
      fun y => terminal β y + (β : ℝ) * (1 - q) / 2 := by
    funext y
    rw [step_terminal hβ', Real.sq_sqrt (NNReal.coe_nonneg _), NNReal.coe_sub hq]
    norm_num
  change step 0 (Real.sqrt q) (fun y => step (β : ℝ)
    (Real.sqrt (↑(1 - q) : ℝ)) (terminal β) y) x = _
  rw [htail, step_add_const (terminal_lipschitz hβ')]

lemma replicaSymmetric_penalty (β q : ℝ≥0) (hq : q ≤ 1) :
    penalty 0 (replicaSymmetricSchedule β q) = β * (1 - (q : ℝ)^2) / 4 := by
  simp [replicaSymmetricSchedule, penalty, NNReal.coe_sub hq]

 

lemma replicaSymmetric_functional {β : ℝ≥0} (hβ : 0 < β) (q : ℝ≥0) (hq : q ≤ 1) :
    functional β (replicaSymmetricSchedule β q) =
      (∫ z : ℝ, terminal β (Real.sqrt q * z) ∂gaussianReal 0 1) +
        β * (1 - (q : ℝ)) ^ 2 / 4 := by
  rw [functional, replicaSymmetric_recursion hβ q hq, replicaSymmetric_penalty β q hq,
    step_mean]
  simp only [zero_add]
  ring

end ParisiFinite

 

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace ParisiInterpolation
open SKGaussian SKQAOA

variable {κ : Type*} [Fintype κ]

lemma memLp_coordinate (k : κ) :
    MemLp (fun x : κ → ℝ => x k) 2 (gaussianLaw κ) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)

lemma covariance_coordinate [DecidableEq κ] (i j : κ) :
    covariance (fun x : κ → ℝ => x i) (fun x => x j) (gaussianLaw κ) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hm := measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i
    have h := covariance_map (X := id) (Y := id) (Z := fun x : κ → ℝ => x i)
      measurable_id.aestronglyMeasurable measurable_id.aestronglyMeasurable
      hm.aemeasurable
    rw [hm.map_eq] at h
    calc
      _ = covariance id id (gaussianReal 0 1) := h.symm
      _ = 1 := by
        rw [covariance_self measurable_id.aemeasurable, variance_id_gaussianReal]
        rfl
  · rw [ite_eq_right hij]
    have hi : iIndepFun (fun i (x : κ → ℝ) => x i) (gaussianLaw κ) :=
      iIndepFun_pi (X := fun _ : κ => id) (fun _ => measurable_id.aemeasurable)
    exact (hi.indepFun hij).covariance_eq_zero (memLp_coordinate i) (memLp_coordinate j)

lemma covariance_field {ι : Type*} (A : ι → κ → ℝ) (i j : ι) :
    covariance (fun x => field A x i) (fun x => field A x j) (gaussianLaw κ) =
      ∑ k, A i k * A j k := by
  classical
  have hm (i : ι) (k : κ) : MemLp (fun x : κ → ℝ => A i k * x k) 2 (gaussianLaw κ) :=
    (memLp_coordinate k).const_mul (A i k)
  have hf (i : ι) : (fun x => field A x i) = ∑ k, fun x => A i k * x k := by
    ext x
    simp [field]
  have hsum (i : ι) : MemLp (∑ k, fun x : κ → ℝ => A i k * x k) 2 (gaussianLaw κ) := by
    rw [← hf i]
    exact memLp_finsetSum Finset.univ (fun k _ => hm i k)
  rw [hf i, hf j, covariance_sum_left (hm i) (hsum j)]
  apply Finset.sum_congr rfl
  intro k _
  rw [covariance_sum_right (hm j) (hm i k)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, covariance_coordinate]
  simp

 

lemma hamiltonian_covariance {n : ℕ} (hn : 0 < n) (σ τ : Configuration n) :
    covariance (fun J => hamiltonian n J σ) (fun J => hamiltonian n J τ)
      (disorderLaw n) = (overlapSum σ τ ^ 2 - (n : ℝ)) / (2 * (n : ℝ)) := by
  have h := covariance_field (skCoeff n) σ τ
  simp_rw [field_skCoeff] at h
  exact h.trans (coeff_covariance hn σ τ)

 
def overlap {n : ℕ} (σ τ : Configuration n) : ℝ := overlapSum σ τ / n

lemma normalized_hamiltonian_covariance {n : ℕ} (hn : 0 < n) (σ τ : Configuration n) :
    covariance (fun J => hamiltonian n J σ) (fun J => hamiltonian n J τ)
      (disorderLaw n) / n = (overlap σ τ ^ 2 - 1 / (n : ℝ)) / 2 := by
  rw [hamiltonian_covariance hn]
  unfold overlap
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

end ParisiInterpolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace ParisiInterpolation
open SKGaussian
variable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]

def rotate (A B : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) : ℝ :=
  Real.cos t * A i k + Real.sin t * B i k

def increment (A : ι → κ → ℝ) (i j : ι) : ℝ :=
  ∑ k, (A i k - A j k) ^ 2

def expected (A : ι → κ → ℝ) : ℝ :=
  ∫ x, logPartition (field A x) ∂gaussianLaw κ

 

lemma hasDerivAt_expected_rotate (A B : ι → κ → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0) (t : ℝ) :
    HasDerivAt (fun s => expected (rotate A B s))
      (∫ x, (1 / 2 : ℝ) * ∑ i, ∑ j,
        weight (field (rotate A B t) x) i * weight (field (rotate A B t) x) j *
          (Real.sin t * Real.cos t * (increment B i j - increment A i j))
        ∂gaussianLaw κ) t := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let A' : ι → Fin (Fintype.card κ) → ℝ := fun i k => A i (e k)
  let B' : ι → Fin (Fintype.card κ) → ℝ := fun i k => B i (e k)
  have hAB' : ∀ i j, ∑ k, A' i k * B' j k = 0 := by
    intro i j
    exact (e.sum_comp (fun k => A i k * B j k)).trans (hAB i j)
  have h := hasDerivAt_expected_rotated A' B' t
  rw [integral_weightedMean_eq_pairwise] at h
  simp_rw [rotated_increment_covariance A' B' hAB'] at h
  have hinc (C : ι → κ → ℝ) (i j : ι) :
      (∑ k, (C i (e k) - C j (e k)) ^ 2) = increment C i j :=
    e.sum_comp (fun k => (C i k - C j k) ^ 2)
  change HasDerivAt (fun s => ∫ x,
    logPartition (linearField (fun i k => rotate A B s i (e k)) x)
    ∂standardLaw (Fintype.card κ)) _ t at h
  have he (s : ℝ) : (∫ x,
      logPartition (linearField (fun i k => rotate A B s i (e k)) x)
      ∂standardLaw (Fintype.card κ)) = expected (rotate A B s) :=
    integral_reindex_field (rotate A B s) logPartition
  simp_rw [he] at h
  convert h using 1
  symm
  change (∫ x, (1 / 2 : ℝ) * ∑ i, ∑ j,
    weight (linearField (fun i k => rotate A B t i (e k)) x) i *
      weight (linearField (fun i k => rotate A B t i (e k)) x) j *
      (Real.sin t * Real.cos t *
        ((∑ k, (B i (e k) - B j (e k)) ^ 2) -
         (∑ k, (A i (e k) - A j (e k)) ^ 2)))
    ∂standardLaw (Fintype.card κ)) = _
  simp_rw [hinc]
  exact integral_reindex_field (rotate A B t) (fun y =>
    (1 / 2 : ℝ) * ∑ i, ∑ j, weight y i * weight y j *
      (Real.sin t * Real.cos t * (increment B i j - increment A i j)))

omit [Fintype ι] [Nonempty ι] in
lemma continuous_field (A : ι → κ → ℝ) : Continuous (field A) := by
  unfold field
  fun_prop

lemma integrable_weight_pair (A : ι → κ → ℝ) (i j : ι) :
    Integrable (fun x => weight (field A x) i * weight (field A x) j) (gaussianLaw κ) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_weight i).comp (continuous_field A)).mul
      ((continuous_weight j).comp (continuous_field A))).aestronglyMeasurable
  filter_upwards with x
  simp only [Function.comp_apply, Pi.mul_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le)]
  exact (mul_le_of_le_one_left (weight_pos _ _).le (weight_le_one _ _)).trans
    (weight_le_one _ _)

 
def replicaAverage (A : ι → κ → ℝ) (K : ι → ι → ℝ) (x : κ → ℝ) : ℝ :=
  ∑ i, ∑ j, weight (field A x) i * weight (field A x) j * K i j

lemma integrable_replicaAverage (A : ι → κ → ℝ) (K : ι → ι → ℝ) :
    Integrable (replicaAverage A K) (gaussianLaw κ) := by
  apply integrable_finsetSum
  intro i _
  exact integrable_finsetSum _ fun j _ => (integrable_weight_pair A i j).mul_const (K i j)

@[simp] lemma replicaAverage_const (A : ι → κ → ℝ) (x : κ → ℝ) (c : ℝ) :
    replicaAverage A (fun _ _ => c) x = c := by
  simp only [replicaAverage, mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sum_weight, one_mul]

omit [Nonempty ι] in
lemma replicaAverage_sub (A : ι → κ → ℝ) (K L : ι → ι → ℝ) (x : κ → ℝ) :
    replicaAverage A (fun i j => K i j - L i j) x =
      replicaAverage A K x - replicaAverage A L x := by
  simp [replicaAverage, mul_sub, Finset.sum_sub_distrib]

omit [Nonempty ι] in
lemma replicaAverage_const_mul (A : ι → κ → ℝ) (K : ι → ι → ℝ) (x : κ → ℝ) (c : ℝ) :
    replicaAverage A (fun i j => c * K i j) x = c * replicaAverage A K x := by
  simp only [replicaAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma replicaAverage_nonneg (A : ι → κ → ℝ) {K : ι → ι → ℝ}
    (hK : ∀ i j, 0 ≤ K i j) (x : κ → ℝ) : 0 ≤ replicaAverage A K x := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (weight_pos _ _).le (weight_pos _ _).le) (hK i j)

def replicaMean (A : ι → κ → ℝ) (K : ι → ι → ℝ) : ℝ :=
  ∫ x, replicaAverage A K x ∂gaussianLaw κ

@[simp] lemma replicaMean_const (A : ι → κ → ℝ) (c : ℝ) :
    replicaMean A (fun _ _ => c) = c := by
  simp [replicaMean]

lemma replicaMean_sub (A : ι → κ → ℝ) (K L : ι → ι → ℝ) :
    replicaMean A (fun i j => K i j - L i j) = replicaMean A K - replicaMean A L := by
  simp only [replicaMean, replicaAverage_sub]
  exact integral_sub (integrable_replicaAverage A K) (integrable_replicaAverage A L)

omit [Nonempty ι] in
lemma replicaMean_const_mul (A : ι → κ → ℝ) (K : ι → ι → ℝ) (c : ℝ) :
    replicaMean A (fun i j => c * K i j) = c * replicaMean A K := by
  simp only [replicaMean, replicaAverage_const_mul, integral_const_mul]

lemma replicaMean_nonneg (A : ι → κ → ℝ) {K : ι → ι → ℝ}
    (hK : ∀ i j, 0 ≤ K i j) : 0 ≤ replicaMean A K :=
  integral_nonneg (replicaAverage_nonneg A hK)

lemma hasDerivAt_expected_rotate_mean (A B : ι → κ → ℝ)
    (hAB : ∀ i j, ∑ k, A i k * B j k = 0) (t : ℝ) :
    HasDerivAt (fun s => expected (rotate A B s))
      (Real.sin t * Real.cos t / 2 *
        replicaMean (rotate A B t) (fun i j => increment B i j - increment A i j)) t := by
  have h := hasDerivAt_expected_rotate A B hAB t
  convert h using 1
  change _ = ∫ x, (1 / 2 : ℝ) * replicaAverage (rotate A B t)
    (fun i j => (Real.sin t * Real.cos t) * (increment B i j - increment A i j)) x
    ∂gaussianLaw κ
  simp only [replicaAverage_const_mul, integral_const_mul, replicaMean]
  ring

end ParisiInterpolation

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace ParisiInterpolation
open SKGaussian SKQAOA

 
def siteCoeff (n : ℕ) (β q : ℝ) (σ : Configuration n) (i : Fin n) : ℝ :=
  β * Real.sqrt q * spin σ i

 

def siteLift (n : ℕ) (β q : ℝ) (σ : Configuration n) : Fin n ⊕ Edge n → ℝ :=
  Sum.elim (siteCoeff n β q σ) (fun _ => 0)

def skLift (n : ℕ) (β : ℝ) (σ : Configuration n) : Fin n ⊕ Edge n → ℝ :=
  Sum.elim (fun _ => 0) (fun e => β * skCoeff n σ e)

lemma lifts_orthogonal (n : ℕ) (β q : ℝ) (σ τ : Configuration n) :
    (∑ k, siteLift n β q σ k * skLift n β τ k) = 0 := by
  simp [siteLift, skLift, Fintype.sum_sum_type]

lemma spin_increment {n : ℕ} (σ τ : Configuration n) :
    (∑ i, (spin σ i - spin τ i) ^ 2) = 2 * (n : ℝ) - 2 * overlapSum σ τ := by
  have he (i : Fin n) : (spin σ i - spin τ i)^2 = 2 - 2 * (spin σ i * spin τ i) := by
    nlinarith [spin_sq σ i, spin_sq τ i]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [overlapSum, mul_comm]

lemma siteCoeff_increment {n : ℕ} {q : ℝ} (hq : 0 ≤ q) (β : ℝ) (σ τ : Configuration n) :
    increment (siteCoeff n β q) σ τ = β ^ 2 * q * (2 * (n : ℝ) - 2 * overlapSum σ τ) := by
  unfold increment siteCoeff
  rw [scaled_increment, spin_increment]
  rw [mul_pow, Real.sq_sqrt hq]

lemma siteLift_increment {n : ℕ} {q : ℝ} (hq : 0 ≤ q) (β : ℝ) (σ τ : Configuration n) :
    increment (siteLift n β q) σ τ = β ^ 2 * q * (2 * (n : ℝ) - 2 * overlapSum σ τ) := by
  simpa only [increment, siteLift, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    sub_self, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, add_zero] using
    siteCoeff_increment hq β σ τ

lemma skLift_increment {n : ℕ} (hn : 0 < n) (β : ℝ) (σ τ : Configuration n) :
    increment (skLift n β) σ τ = β ^ 2 * ((n : ℝ) - overlapSum σ τ ^ 2 / n) := by
  simp only [increment, skLift, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    sub_self, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, zero_add]
  rw [scaled_increment, coeff_increment hn]

lemma interpolation_increment {n : ℕ} (hn : 0 < n) {q : ℝ} (hq : 0 ≤ q)
    (β : ℝ) (σ τ : Configuration n) :
    increment (skLift n β) σ τ - increment (siteLift n β q) σ τ =
      β ^ 2 * n * ((1 - q) ^ 2 - (overlap σ τ - q) ^ 2) := by
  rw [skLift_increment hn, siteLift_increment hq]
  unfold overlap
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

 

def interpolatedPressure (n : ℕ) (β q t : ℝ) : ℝ :=
  expected (rotate (siteLift n β q) (skLift n β) t)

 

def remainder (n : ℕ) (β q t : ℝ) : ℝ :=
  replicaMean (rotate (siteLift n β q) (skLift n β) t)
    (fun σ τ => (overlap σ τ - q) ^ 2)

lemma remainder_nonneg (n : ℕ) (β q t : ℝ) : 0 ≤ remainder n β q t :=
  replicaMean_nonneg _ (fun _ _ => sq_nonneg _)

lemma hasDerivAt_interpolatedPressure {n : ℕ} (hn : 0 < n) (β : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (t : ℝ) :
    HasDerivAt (interpolatedPressure n β q)
      (β ^ 2 * n * (Real.sin t * Real.cos t) / 2 *
        ((1 - q) ^ 2 - remainder n β q t)) t := by
  have h := hasDerivAt_expected_rotate_mean (siteLift n β q) (skLift n β)
    (lifts_orthogonal n β q) t
  simp_rw [interpolation_increment hn hq] at h
  rw [replicaMean_const_mul, replicaMean_sub, replicaMean_const] at h
  change HasDerivAt (fun s => expected (rotate (siteLift n β q) (skLift n β) s)) _ t
  convert h using 1
  simp only [remainder]
  ring

end ParisiInterpolation

end

end OAI
