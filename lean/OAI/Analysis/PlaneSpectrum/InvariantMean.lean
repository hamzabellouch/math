import Mathlib

namespace OAI

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
/-! A discrete abelian invariant mean, constructed from weighted cube
averages. Repeated group elements keep their multiplicities. -/
noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

local instance (α : Type*) : DecidableEq α := Classical.decEq α

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

/-- Translation acts on all bounded functions because the domain is discrete. -/
def shift (g : G) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply (g x : G) (f : G →ᵇ ℝ) : shift g f x = f (x+g) := rfl

lemma shift_comm (g h : G) (f : G →ᵇ ℝ) : shift g (shift h f) = shift h (shift g f) := by
  ext x
  simp only [shift_apply, add_assoc, add_comm g h]

@[simp] lemma shift_add (g : G) (f h : G →ᵇ ℝ) : shift g (f+h) = shift g f + shift g h := by
  ext x
  rfl

@[simp] lemma shift_sub (g : G) (f h : G →ᵇ ℝ) : shift g (f-h) = shift g f - shift g h := by
  ext x
  rfl

@[simp] lemma shift_smul (g : G) (c : ℝ) (f : G →ᵇ ℝ) : shift g (c • f) = c • shift g f := by
  ext x
  rfl

lemma shift_norm_le (g : G) (f : G →ᵇ ℝ) : ‖shift g f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

/-- A single cyclic Cesàro average, always with a positive denominator. -/
def single (g : G) (n : ℕ) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (n+1), shift (k • g) f

@[simp] lemma single_apply (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n f x = ((n+1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n+1), f (x+k • g) := by
  simp [single]

lemma single_norm_le (g : G) (n : ℕ) (f : G →ᵇ ℝ) : ‖single g n f‖ ≤ ‖f‖ := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  calc
    ‖single g n f‖ = ((n+1 : ℕ) : ℝ)⁻¹ * ‖∑ k ∈ Finset.range (n+1), shift (k • g) f‖ := by
      rw [single, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (∑ _k ∈ Finset.range (n+1), ‖f‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => shift_norm_le _ _)
    _ = ‖f‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

@[simp] lemma single_add (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f+h) = single g n f + single g n h := by
  simp only [single, shift_add, Finset.sum_add_distrib, smul_add]

@[simp] lemma single_sub (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f-h) = single g n f - single g n h := by
  simp only [single, shift_sub, Finset.sum_sub_distrib, smul_sub]

@[simp] lemma single_smul (g : G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    single g n (c • f) = c • single g n f := by
  simp only [single, shift_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

lemma single_shift (g h : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift h f) = shift h (single g n f) := by
  ext x
  simp only [single_apply, shift_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  abel

lemma single_const (g : G) (n : ℕ) (c : ℝ) :
    single g n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  ext x
  simp only [single_apply, BoundedContinuousFunction.const_apply, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]

lemma single_nonneg (g : G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ single g n f x := by
  intro x
  rw [single_apply]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun k hk => hf _

lemma single_telescope (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift g f - f) x =
      ((n+1 : ℕ) : ℝ)⁻¹ * (f (x+(n+1) • g) - f x) := by
  rw [single_apply]
  congr 1
  have he (k : ℕ) : (shift g f - f) (x+k • g) =
      f (x+(k+1) • g) - f (x+k • g) := by
    simp only [BoundedContinuousFunction.sub_apply, shift_apply, add_nsmul, one_nsmul, add_assoc]
  simp_rw [he]
  simpa only [zero_nsmul, add_zero] using Finset.sum_range_sub (fun k => f (x+k • g)) (n+1)

lemma single_coboundary_norm (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖single g n (shift g f - f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [single_telescope, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ)⁻¹)]
  have hb : |f (x+(n+1) • g) - f x| ≤ 2 * ‖f‖ := by
    calc
      _ ≤ |f (x+(n+1) • g)| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = _ := by ring
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Multiplicities in the cube are explicitly retained through composition. -/
def cube : List G → ℕ → (G →ᵇ ℝ) → (G →ᵇ ℝ)
  | [], _, f => f
  | g::L, n, f => single g n (cube L n f)

lemma cube_norm_le (L : List G) (n : ℕ) (f : G →ᵇ ℝ) : ‖cube L n f‖ ≤ ‖f‖ := by
  induction L with
  | nil => exact le_rfl
  | cons g L ih => exact (single_norm_le g n _).trans ih

lemma cube_shift (L : List G) (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    cube L n (shift g f) = shift g (cube L n f) := by
  induction L with
  | nil => rfl
  | cons h L ih => simp only [cube, ih, single_shift]

@[simp] lemma cube_add (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f+h) = cube L n f + cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_add]

@[simp] lemma cube_sub (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f-h) = cube L n f - cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_sub]

@[simp] lemma cube_smul (L : List G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    cube L n (c • f) = c • cube L n f := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_smul]

lemma cube_const (L : List G) (n : ℕ) (c : ℝ) :
    cube L n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_const]

lemma cube_nonneg (L : List G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ cube L n f x := by
  induction L with
  | nil => exact hf
  | cons g L ih => exact single_nonneg g n _ ih

/-- Each listed generator has the same boundary bound, independently of the
length of the list and without an injective image assumption. -/
lemma cube_coboundary_norm (L : List G) (g : G) (hg : g ∈ L) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖cube L n (shift g f-f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  induction L with
  | nil => simp at hg
  | cons h L ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [cube, cube_sub, cube_shift]
      apply (single_coboundary_norm g n _).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cube_norm_le L n f) (by norm_num)) (by positivity)
    · exact (single_norm_le h n _).trans (ih hg)

/-- The directed weighted-cube averages. -/
def approx (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ℝ :=
  cube i.1.toList i.2 f 0

lemma approx_norm_le (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ‖approx i f‖ ≤ ‖f‖ :=
  ((cube i.1.toList i.2 f).norm_coe_le_norm 0).trans (cube_norm_le _ _ _)

/-- One fixed ultrafilter is used for all functions. -/
def averagingUF (G : Type*) [AddCommGroup G] : Ultrafilter (Finset G × ℕ) :=
  Ultrafilter.of atTop

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma averagingUF_le : (averagingUF G : Filter (Finset G × ℕ)) ≤ atTop :=
  Ultrafilter.of_le _

lemma approx_has_limit (f : G →ᵇ ℝ) :
    ∃ r : ℝ, Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 r) := by
  have hb : (Ultrafilter.map (fun i => approx i f) (averagingUF G) : Filter ℝ) ≤
      𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro i
    exact abs_le.mp (approx_norm_le i f)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (fun i => approx i f) (averagingUF G)) hb
  exact ⟨r, hr⟩

/-- The invariant mean, as the limit of the multiplicity-preserving averages. -/
def mean (f : G →ᵇ ℝ) : ℝ :=
  (averagingUF G : Filter _).limUnder (fun i => approx i f)

lemma tendsto_approx (f : G →ᵇ ℝ) :
    Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 (mean f)) :=
  tendsto_nhds_limUnder (approx_has_limit f)

lemma mean_add (f h : G →ᵇ ℝ) : mean (f+h) = mean f + mean h := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).add (tendsto_approx h) using 1
  simp only [approx, cube_add, BoundedContinuousFunction.add_apply]

lemma mean_smul (c : ℝ) (f : G →ᵇ ℝ) : mean (c • f) = c * mean f := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).const_mul c using 1
  simp only [approx, cube_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]

lemma mean_const (c : ℝ) : mean (BoundedContinuousFunction.const G c) = c := by
  apply Tendsto.limUnder_eq
  convert (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
    (averagingUF G : Filter _) (𝓝 c)) using 1
  simp only [approx, cube_const, BoundedContinuousFunction.const_apply]

lemma mean_nonneg (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  exact ge_of_tendsto (tendsto_approx f) (Filter.Eventually.of_forall fun i =>
    cube_nonneg i.1.toList i.2 f hf 0)

lemma mean_norm_le (f : G →ᵇ ℝ) : ‖mean f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_approx f).norm
    (Filter.Eventually.of_forall fun i => approx_norm_le i f)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma eventually_mem (g : G) : ∀ᶠ i : Finset G × ℕ in (averagingUF G : Filter _), g ∈ i.1 := by
  classical
  apply Filter.Eventually.filter_mono averagingUF_le
  apply Filter.eventually_atTop.mpr
  refine ⟨({g}, 0), fun i hi => ?_⟩
  exact hi.1 (Finset.mem_singleton_self g)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma tendsto_index : Tendsto (fun i : Finset G × ℕ => i.2)
    (averagingUF G : Filter _) atTop := by
  apply Tendsto.mono_left _ averagingUF_le
  apply tendsto_atTop.mpr
  intro n
  apply Filter.eventually_atTop.mpr
  exact ⟨(∅, n), fun i hi => hi.2⟩

omit [DiscreteTopology G] in
lemma tendsto_boundary (f : G →ᵇ ℝ) :
    Tendsto (fun i : Finset G × ℕ => 2 * ‖f‖ / (i.2+1 : ℕ))
      (averagingUF G : Filter _) (𝓝 0) := by
  have hn : Tendsto (fun i : Finset G × ℕ => ((i.2+1 : ℕ) : ℝ))
      (averagingUF G : Filter _) atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp tendsto_index)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hn).const_mul (2 * ‖f‖)

lemma mean_shift (g : G) (f : G →ᵇ ℝ) : mean (shift g f) = mean f := by
  have hz : Tendsto (fun i : Finset G × ℕ => approx i (shift g f) - approx i f)
      (averagingUF G : Filter _) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_boundary f)
    filter_upwards [eventually_mem g] with i hi
    have h := ((cube i.1.toList i.2 (shift g f-f)).norm_coe_le_norm 0).trans
      (cube_coboundary_norm i.1.toList g (Finset.mem_toList.mpr hi) i.2 f)
    simpa only [cube_sub, BoundedContinuousFunction.sub_apply, approx] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique ((tendsto_approx _).sub (tendsto_approx _)) hz)

/-- A normalized positive shift-invariant continuous real linear functional. -/
def meanCLM : (G →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := mean, map_add' := mean_add, map_smul' := mean_smul }
    1 (by intro f; change ‖mean f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using mean_norm_le f)

@[simp] lemma meanCLM_apply (f : G →ᵇ ℝ) : meanCLM f = mean f := rfl

def realPart (f : G →ᵇ ℂ) : G →ᵇ ℝ := Complex.reCLM.compLeftContinuousBounded G f

def imagPart (f : G →ᵇ ℂ) : G →ᵇ ℝ := Complex.imCLM.compLeftContinuousBounded G f

omit [AddCommGroup G] [DiscreteTopology G] in
@[simp] lemma realPart_apply (f : G →ᵇ ℂ) (x : G) : realPart f x = (f x).re := rfl
omit [AddCommGroup G] [DiscreteTopology G] in
@[simp] lemma imagPart_apply (f : G →ᵇ ℂ) (x : G) : imagPart f x = (f x).im := rfl

/-- Complexification of the same (not a separately chosen) real mean. -/
def cmean (f : G →ᵇ ℂ) : ℂ := (mean (realPart f) : ℂ) + (mean (imagPart f) : ℂ) * Complex.I

lemma cmean_add (f h : G →ᵇ ℂ) : cmean (f+h) = cmean f + cmean h := by
  have hr : realPart (f+h) = realPart f + realPart h := by ext x; simp
  have hi : imagPart (f+h) = imagPart f + imagPart h := by ext x; simp
  simp only [cmean, hr, hi, mean_add, Complex.ofReal_add]
  ring

lemma cmean_smul (c : ℂ) (f : G →ᵇ ℂ) : cmean (c • f) = c * cmean f := by
  have hr : realPart (c • f) = c.re • realPart f - c.im • imagPart f := by
    ext x; simp [Complex.mul_re]
  have hi : imagPart (c • f) = c.re • imagPart f + c.im • realPart f := by
    ext x; simp [Complex.mul_im]
  have hs (f h : G →ᵇ ℝ) : mean (f-h) = mean f - mean h := meanCLM.map_sub f h
  apply Complex.ext <;>
    simp [cmean, hr, hi, hs, mean_smul, mean_add, Complex.mul_re, Complex.mul_im]

omit [AddCommGroup G] [DiscreteTopology G] in
lemma realPart_norm_le (f : G →ᵇ ℂ) : ‖realPart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact (Complex.abs_re_le_norm (f x)).trans (f.norm_coe_le_norm x)

omit [AddCommGroup G] [DiscreteTopology G] in
lemma imagPart_norm_le (f : G →ᵇ ℂ) : ‖imagPart f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  exact (Complex.abs_im_le_norm (f x)).trans (f.norm_coe_le_norm x)

lemma cmean_norm_le (f : G →ᵇ ℂ) : ‖cmean f‖ ≤ 2 * ‖f‖ := by
  calc
    _ ≤ ‖(mean (realPart f) : ℂ)‖ + ‖(mean (imagPart f) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖mean (realPart f)‖ + ‖mean (imagPart f)‖ := by simp
    _ ≤ ‖f‖ + ‖f‖ := add_le_add ((mean_norm_le _).trans (realPart_norm_le f))
        ((mean_norm_le _).trans (imagPart_norm_le f))
    _ = _ := by ring

def cmeanCLM : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := cmean, map_add' := cmean_add, map_smul' := cmean_smul }
    2 (by intro f; exact cmean_norm_le f)

@[simp] lemma cmeanCLM_apply (f : G →ᵇ ℂ) : cmeanCLM f = cmean f := rfl

lemma cmean_const (z : ℂ) : cmean (BoundedContinuousFunction.const G z) = z := by
  have hr : realPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.re := rfl
  have hi : imagPart (BoundedContinuousFunction.const G z) = BoundedContinuousFunction.const G z.im := rfl
  simp only [cmean, hr, hi, mean_const, Complex.re_add_im]

/-- Complex translation; no ordinary measurability is asserted or needed. -/
def cshift (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma cshift_apply (g x : G) (f : G →ᵇ ℂ) : cshift g f x = f (x+g) := rfl

lemma cmean_shift (g : G) (f : G →ᵇ ℂ) : cmean (cshift g f) = cmean f := by
  have hr : realPart (cshift g f) = shift g (realPart f) := rfl
  have hi : imagPart (cshift g f) = shift g (imagPart f) := rfl
  simp only [cmean, hr, hi, mean_shift]

open MeasureTheory AddCircle

/-- Pullback along the dense algebraic circle embedding. -/
def circlePull (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => f (ρ x)) ‖f‖ (fun _x => f.norm_coe_le_norm _)

@[simp] lemma circlePull_apply (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) (x : G) :
    circlePull ρ f x = f (ρ x) := rfl

lemma circlePull_norm_le (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    ‖circlePull ρ f‖ ≤ ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  exact fun x => f.norm_coe_le_norm _

def circleMean (ρ : G →+ UnitAddCircle) : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  cmeanCLM.comp (LinearMap.mkContinuous
    ({ toFun := circlePull ρ
       map_add' := by intro f h; ext x; rfl
       map_smul' := by intro c f; ext x; rfl } : C(UnitAddCircle, ℂ) →ₗ[ℂ] (G →ᵇ ℂ))
    1 (by intro f; change ‖circlePull ρ f‖ ≤ 1 * ‖f‖
          simpa only [one_mul] using circlePull_norm_le ρ f))

@[simp] lemma circleMean_apply (ρ : G →+ UnitAddCircle) (f : C(UnitAddCircle, ℂ)) :
    circleMean ρ f = cmean (circlePull ρ f) := rfl

/-- Normalized Haar integral on the ordinary circle. -/
def circleIntegral : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂haarAddCircle
      map_add' := by
        intro f h
        exact integral_add (BoundedContinuousFunction.mkOfCompact f |>.integrable _)
          (BoundedContinuousFunction.mkOfCompact h |>.integrable _)
      map_smul' := by intro c f; exact integral_smul c f }
    1 (by
      intro f
      change ‖∫ x, f x ∂haarAddCircle‖ ≤ 1 * ‖f‖
      simpa only [one_mul, BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_apply] using
        (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_norm haarAddCircle)

@[simp] lemma circleIntegral_apply (f : C(UnitAddCircle, ℂ)) :
    circleIntegral f = ∫ x, f x ∂haarAddCircle := rfl

/-- An ordinary nonconstant Fourier monomial has zero mean as soon as its
half-period is represented in the discrete group. -/
lemma circleMean_fourier_nonzero (ρ : G →+ UnitAddCircle) {n : ℤ} (hn : n ≠ 0)
    (hρ : ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle)) : circleMean ρ (fourier n) = 0 := by
  obtain ⟨g, hg⟩ := hρ
  have he : cshift g (circlePull ρ (fourier n)) = -(circlePull ρ (fourier n)) := by
    ext x
    simp only [cshift_apply, circlePull_apply, map_add, hg, BoundedContinuousFunction.neg_apply]
    exact fourier_add_half_inv_index hn zero_lt_one _
  have hm := cmean_shift g (circlePull ρ (fourier n))
  rw [he] at hm
  have hn' : cmean (-circlePull ρ (fourier n)) = -cmean (circlePull ρ (fourier n)) :=
    cmeanCLM.map_neg _
  rw [hn'] at hm
  apply neg_eq_self.mp at hm
  exact hm

theorem circleMean_eq_integral (ρ : G →+ UnitAddCircle)
    (hρ : ∀ n : ℤ, n ≠ 0 → ∃ g, ρ g = ((1 / 2 / n : ℝ) : UnitAddCircle))
    (f : C(UnitAddCircle, ℂ)) : cmean (circlePull ρ f) = ∫ x, f x ∂haarAddCircle := by
  have he : circleMean ρ = circleIntegral := by
    apply ContinuousLinearMap.ext_on (s := Set.range (@fourier 1))
    · exact Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
    · rintro _ ⟨n, rfl⟩
      by_cases hn : n = 0
      · subst n
        have hp : circlePull ρ (fourier 0) = BoundedContinuousFunction.const G 1 := by
          ext x; simp
        simp only [circleMean_apply, hp, cmean_const, circleIntegral_apply]
        simp
      · rw [circleMean_fourier_nonzero ρ hn (hρ n hn), circleIntegral_apply]
        exact (integral_eq_zero_of_add_right_eq_neg
          (fourier_add_half_inv_index hn zero_lt_one)).symm
  exact DFunLike.congr_fun he f

/-- The real algebraic field and the literal discrete quotient F/Z. -/
abbrev AF := algebraicClosure ℚ ℝ

def PeriodGroup := AF ⧸ AddSubgroup.zmultiples (1 : AF) deriving AddCommGroup
instance : TopologicalSpace PeriodGroup := ⊥
instance : DiscreteTopology PeriodGroup := ⟨rfl⟩

def periodMk : AF →+ PeriodGroup := QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : AF))

/-- The ordinary circle quotient map, before passage to F/Z. -/
def fieldCircle : AF →+ UnitAddCircle :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp
    (algebraicClosure ℚ ℝ).subtype.toAddMonoidHom

@[simp] lemma fieldCircle_apply (t : AF) : fieldCircle t = ((t : ℝ) : UnitAddCircle) := rfl

/-- F/Z embeds in the ordinary circle; no ordinary topology is imposed on its source. -/
def periodMap : PeriodGroup →+ UnitAddCircle :=
  QuotientAddGroup.lift (AddSubgroup.zmultiples (1 : AF)) fieldCircle (by
    rw [AddSubgroup.zmultiples_le]
    change (((1 : AF) : ℝ) : UnitAddCircle) = 0
    exact (QuotientAddGroup.eq_zero_iff (1 : ℝ)).mpr (AddSubgroup.mem_zmultiples 1))

@[simp] lemma periodMap_apply (t : AF) :
    periodMap (QuotientAddGroup.mk t) = ((t : ℝ) : UnitAddCircle) := rfl

lemma periodMap_half_period (n : ℤ) : ∃ g, periodMap g = ((1 / 2 / n : ℝ) : UnitAddCircle) := by
  refine ⟨QuotientAddGroup.mk (1 / 2 / n : AF), ?_⟩
  rw [periodMap_apply]
  congr 1

/-- The exact identification of the chosen mean on ordinary continuous
periodic functions asserted in spectral.tex113–123. -/
theorem ordinary_mean_integral (f : C(UnitAddCircle, ℂ)) :
    cmean (circlePull periodMap f) = ∫ x, f x ∂haarAddCircle :=
  circleMean_eq_integral periodMap (fun n _ => periodMap_half_period n) f

lemma mean_mono (f h : G →ᵇ ℝ) (hf : ∀ x, f x ≤ h x) : mean f ≤ mean h := by
  have hn : 0 ≤ mean (h-f) := mean_nonneg _ (fun x => sub_nonneg.mpr (hf x))
  have he : mean (h-f) = mean h - mean f := meanCLM.map_sub h f
  rw [he] at hn
  exact sub_nonneg.mp hn

lemma mean_abs_le (f h : G →ᵇ ℝ) (hf : ∀ x, |f x| ≤ h x) : |mean f| ≤ mean h := by
  apply abs_le.mpr
  constructor
  · have he : mean (-h) = -mean h := meanCLM.map_neg h
    rw [← he]
    exact mean_mono _ _ (fun x => (abs_le.mp (hf x)).1)
  · exact mean_mono _ _ (fun x => (abs_le.mp (hf x)).2)

section WeakMean
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Norm of a bounded vector field, still an arbitrary bounded function on
this discrete domain. -/
def normFn (V : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun x => ‖V x‖) ‖V‖ (fun x => by simpa only [norm_norm] using V.norm_coe_le_norm x)

omit [AddCommGroup G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma normFn_apply (V : G →ᵇ H) (x : G) : normFn V x = ‖V x‖ := rfl

def pairing (V : G →ᵇ H) (v : H) : G →ᵇ ℝ :=
  (innerSL ℝ v).compLeftContinuousBounded G V

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma pairing_apply (V : G →ᵇ H) (v : H) (x : G) : pairing V v x = inner ℝ v (V x) := rfl

omit [CompleteSpace H] in
lemma pairing_mean_bound (V : G →ᵇ H) (v : H) :
    |mean (pairing V v)| ≤ ‖v‖ * mean (normFn V) := by
  rw [← mean_smul]
  apply mean_abs_le
  intro x
  exact norm_inner_le_norm (𝕜 := ℝ) v (V x)

def pairingMean (V : G →ᵇ H) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => mean (pairing V v)
      map_add' := by
        intro v w
        have he : pairing V (v+w) = pairing V v + pairing V w := by
          ext x; simp [inner_add_left]
        rw [he, mean_add]
      map_smul' := by
        intro c v
        have he : pairing V (c • v) = c • pairing V v := by
          ext x; simp [real_inner_smul_left]
        rw [he, mean_smul]
        rfl }
    (mean (normFn V)) (by
      intro v
      change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
      simpa only [mul_comm] using pairing_mean_bound V v)

/-- Hilbert-space weak mean; it exists by the proved scalar mean and Riesz,
without any real-variable measurability assumption on V. -/
def weakMean (V : G →ᵇ H) : H := (InnerProductSpace.toDual ℝ H).symm (pairingMean V)

lemma weakMean_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (weakMean V) v = mean (pairing V v) :=
  InnerProductSpace.toDual_symm_apply

lemma weakMean_norm_bound (V : G →ᵇ H) : ‖weakMean V‖ ≤ mean (normFn V) := by
  rw [weakMean, LinearIsometryEquiv.norm_map]
  apply (pairingMean V).opNorm_le_bound (mean_nonneg _ (fun x => by rw [normFn_apply]; exact norm_nonneg _))
  intro v
  change |mean (pairing V v)| ≤ mean (normFn V) * ‖v‖
  simpa only [mul_comm] using pairing_mean_bound V v

lemma weakMean_add (V W : G →ᵇ H) : weakMean (V+W) = weakMean V + weakMean W := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_add_left, weakMean_pair, weakMean_pair, weakMean_pair]
  have he : pairing (V+W) v = pairing V v + pairing W v := by
    ext x; simp [inner_add_right]
  rw [he, mean_add]

lemma weakMean_sub (V W : G →ᵇ H) : weakMean (V-W) = weakMean V - weakMean W := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_sub_left, weakMean_pair, weakMean_pair, weakMean_pair]
  have he : pairing (V-W) v = pairing V v - pairing W v := by
    ext x; simp [inner_sub_right]
  rw [he]
  exact meanCLM.map_sub _ _

lemma weakMean_shift (V : G →ᵇ H) (g : G) :
    weakMean (V.compContinuous ⟨fun x => x+g, continuous_of_discreteTopology⟩) = weakMean V := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, weakMean_pair]
  exact mean_shift g (pairing V v)

lemma weakMean_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (V : G →ᵇ H) :
    weakMean (L.compLeftContinuousBounded G V) = L (weakMean V) := by
  apply ext_inner_right ℝ
  intro v
  rw [weakMean_pair, ← L.adjoint_inner_right, weakMean_pair]
  congr 1
  ext x
  exact (L.adjoint_inner_left (V x) v).symm

end WeakMean

section Periodization
variable {H : Type*} [NormedAddCommGroup H]

/-- Periodization is defined for all functions; bounded support below ensures
that these sums are finite and uniformly bounded. -/
def periodSum (h : AF → H) (t : AF) : H := ∑' k : ℤ, h (t + k)

lemma periodSum_periodic (h : AF → H) : Function.Periodic (periodSum h) 1 := by
  intro t
  unfold periodSum
  calc
    (∑' k : ℤ, h (t+1+k)) = ∑' k : ℤ, h (t+((k+1 : ℤ) : AF)) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring
    _ = ∑' k : ℤ, h (t+k) := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => h (t+k))

/-- Literal quotient-valued periodization. -/
def periodLift (h : AF → H) : PeriodGroup → H := (periodSum_periodic h).lift

@[simp] lemma periodLift_mk (h : AF → H) (t : AF) :
    periodLift h (QuotientAddGroup.mk t) = periodSum h t := rfl

/-- A uniform finite interval of integers contains all summands after the
argument has been moved to [0,1). -/
lemma period_term_zero {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    {t : AF} (ht0 : 0 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)) : h (t+k) = 0 := by
  apply hs
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  rcases hk with hk | hk
  · have hk' : (k : ℝ) < -(N : ℝ)-2 := by exact_mod_cast hk
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+2 < (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_pos] <;> linarith

lemma periodSum_norm_le {h : AF → H} {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (t : AF) :
    ‖periodSum h t‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  let t' : AF := t - (⌊(t : ℝ)⌋ : ℤ)
  have ht0 : 0 ≤ (t' : ℝ) := Int.fract_nonneg (t : ℝ)
  have ht1 : (t' : ℝ) < 1 := Int.fract_lt_one (t : ℝ)
  have he : periodSum h t = periodSum h t' := by
    simpa only [t', mul_one] using
      ((periodSum_periodic h).sub_int_mul_eq (x := t) ⌊(t : ℝ)⌋).symm
  rw [he, periodSum, tsum_eq_sum (period_term_zero hs ht0 ht1)]
  calc
    _ ≤ ∑ k ∈ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2), ‖h (t'+k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2), B :=
      Finset.sum_le_sum (fun k _ => hb (t'+k))
    _ = _ := by simp

/-- Every bounded, boundedly supported vector function has a bounded
periodization on the discrete quotient F/Z. -/
def periodBCF (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : PeriodGroup →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (periodLift h)
    ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B) (fun x => by
      induction x using QuotientAddGroup.induction_on with
      | H t => exact periodSum_norm_le hs hb t)

/-- Absolute finiteness of each period sum. -/
lemma period_summable {h : AF → H} {N : ℕ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0) (t : AF) :
    Summable (fun k : ℤ => h (t+k)) := by
  obtain ⟨M, hM⟩ := exists_nat_gt |(t : ℝ)|
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  apply hs
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  change (N : ℝ) < |(t : ℝ)+(k : ℝ)|
  have hM1 := (abs_lt.mp hM).1
  have hM2 := (abs_lt.mp hM).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

lemma periodSum_add {h j : AF → H} {N M : ℕ}
    (hh : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hj : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0) (t : AF) :
    periodSum (h+j) t = periodSum h t + periodSum j t :=
  (period_summable hh t).tsum_add (period_summable hj t)

lemma periodSum_shift (h : AF → H) (s t : AF) :
    periodSum (fun x => h (x+s)) t = periodSum h (t+s) := by
  unfold periodSum
  congr 1
  ext k
  abel_nf

@[simp] lemma periodBCF_mk (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (t : AF) :
    periodBCF h hs hb (QuotientAddGroup.mk t) = periodSum h t := rfl

lemma periodBCF_norm_le (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖periodBCF h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply BoundedContinuousFunction.norm_le (mul_nonneg (Nat.cast_nonneg _) hB) |>.mpr
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact periodSum_norm_le hs hb t

/-- The scalar invariant integral in the manuscript, literally the invariant
mean of the period sum on F/Z. -/
def integralReal (h : AF → ℝ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : ℝ := mean (periodBCF h hs hb)

def integralComplex (h : AF → ℂ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : ℂ := cmean (periodBCF h hs hb)

lemma integralReal_nonneg (h : AF → ℝ) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hp : ∀ t, 0 ≤ h t) : 0 ≤ integralReal h hs hb := by
  apply mean_nonneg
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact tsum_nonneg (fun k => hp (t+k))

lemma integralReal_shift (h : AF → ℝ) (s : AF) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (hss : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → h (t+s) = 0)
    (hbs : ∀ t, ‖h (t+s)‖ ≤ C) :
    integralReal (fun t => h (t+s)) hss hbs = integralReal h hs hb := by
  have he : periodBCF (fun t => h (t+s)) hss hbs =
      shift (G := PeriodGroup) (periodMk s) (periodBCF h hs hb) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact periodSum_shift h s t
  unfold integralReal
  rw [he, mean_shift]

lemma integralReal_mono (h j : AF → ℝ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (hle : ∀ t, h t ≤ j t) :
    integralReal h hs hb ≤ integralReal j js jb := by
  apply mean_mono
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (period_summable hs t).tsum_le_tsum (fun k => hle (t+k)) (period_summable js t)

variable [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Hilbert-space weak invariant integral of bounded, boundedly supported
functions, with no ordinary real-variable measurability hypothesis. -/
def weakIntegral (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) : H := weakMean (periodBCF h hs hb)

lemma weakIntegral_pair (h : AF → H) {N M : ℕ} {B C : ℝ} (v : H)
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (vs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → inner ℝ v (h t) = 0)
    (vb : ∀ t, ‖inner ℝ v (h t)‖ ≤ C) :
    inner ℝ (weakIntegral h hs hb) v = integralReal (fun t => inner ℝ v (h t)) vs vb := by
  rw [weakIntegral, weakMean_pair]
  unfold integralReal
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact (innerSL ℝ v).map_tsum (period_summable hs t)

lemma weakIntegral_norm_bound (h : AF → H) {N : ℕ} {B : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B) (hB : 0 ≤ B) :
    ‖weakIntegral h hs hb‖ ≤ (Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B := by
  apply (weakMean_norm_bound _).trans
  rw [← mean_const (G := PeriodGroup) ((Finset.Icc (-(N : ℤ)-2) ((N : ℤ)+2)).card * B)]
  apply mean_mono
  intro x
  exact ((periodBCF h hs hb).norm_coe_le_norm x).trans (periodBCF_norm_le h hs hb hB)

lemma weakIntegral_shift (h : AF → H) (s : AF) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (hss : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → h (t+s) = 0)
    (hbs : ∀ t, ‖h (t+s)‖ ≤ C) :
    weakIntegral (fun t => h (t+s)) hss hbs = weakIntegral h hs hb := by
  have he : periodBCF (fun t => h (t+s)) hss hbs =
      (periodBCF h hs hb).compContinuous
        (⟨fun x : PeriodGroup => x+periodMk s,
          continuous_of_discreteTopology⟩) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact periodSum_shift h s t
  unfold weakIntegral
  rw [he, weakMean_shift]

lemma weakIntegral_sub (h j : AF → H) {N M L : ℕ} {B C Q : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C)
    (ds : ∀ t : AF, (L : ℝ) < |(t : ℝ)| → h t-j t = 0)
    (db : ∀ t, ‖h t-j t‖ ≤ Q) :
    weakIntegral (fun t => h t-j t) ds db = weakIntegral h hs hb - weakIntegral j js jb := by
  have he : periodBCF (fun t => h t-j t) ds db = periodBCF h hs hb - periodBCF j js jb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (period_summable hs t).tsum_sub (period_summable js t)
  unfold weakIntegral
  rw [he, weakMean_sub]

lemma weakIntegral_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J]
    [CompleteSpace J] (L : H →L[ℝ] J) (h : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → L (h t) = 0)
    (jb : ∀ t, ‖L (h t)‖ ≤ C) :
    weakIntegral (fun t => L (h t)) js jb = L (weakIntegral h hs hb) := by
  have he : periodBCF (fun t => L (h t)) js jb =
      L.compLeftContinuousBounded PeriodGroup (periodBCF h hs hb) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact (L.map_tsum (period_summable hs t)).symm
  unfold weakIntegral
  rw [he, weakMean_map]

end Periodization
section OrdinaryIntegral
open ContinuousMap TopologicalSpace

/-- Compact support makes all local norm sums finite, before any interchange
of sums, evaluations or integrals. -/
lemma compact_local_summable (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (K : Compacts ℝ) :
    Summable (fun k : ℤ => ‖(f.comp (ContinuousMap.addRight k)).restrict K‖) := by
  obtain ⟨C, hC⟩ := K.isCompact.isBounded.exists_norm_le
  obtain ⟨M, hM⟩ := exists_nat_gt C
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.finite_toSet (Finset.Icc
    (-((N+M : ℕ) : ℤ)-2) (((N+M : ℕ) : ℤ)+2)))
  intro k hk
  by_contra hn
  apply hk
  rw [norm_eq_zero]
  ext x
  apply hs
  change (N : ℝ) < |(x : ℝ)+(k : ℝ)|
  have hx : |(x : ℝ)| < (M : ℝ) := lt_of_le_of_lt (hC x x.property) hM
  simp only [Finset.mem_coe, Finset.mem_Icc, not_and_or, not_le] at hn
  have hx1 := (abs_lt.mp hx).1
  have hx2 := (abs_lt.mp hx).2
  rcases hn with hn | hn
  · have hk' : (k : ℝ) < -((N : ℝ)+M)-2 := by exact_mod_cast hn
    rw [abs_of_neg] <;> linarith
  · have hk' : (N : ℝ)+M+2 < (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_pos] <;> linarith

/-- The ordinary continuous periodic function associated with a test
function. Continuous-map summation agrees pointwise by local finiteness. -/
def ordinaryPeriod (f : C(ℝ, ℂ)) : C(UnitAddCircle, ℂ) :=
  ⟨(f.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩

lemma ordinaryPeriod_apply (f : C(ℝ, ℂ)) {N : ℕ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (t : ℝ) :
    ordinaryPeriod f (t : UnitAddCircle) = ∑' k : ℤ, f (t+k) := by
  change (∑' k : ℤ, f.comp (ContinuousMap.addRight (k • (1 : ℝ)) )) t = _
  have hf := ContinuousMap.summable_of_locally_summable_norm (compact_local_summable f hs)
  simpa only [zsmul_eq_mul, mul_one, ContinuousMap.comp_apply,
    ContinuousMap.addRight, ContinuousMap.coe_mk] using (ContinuousMap.tsum_apply hf t).symm

/-- Exact agreement of the manuscript's invariant integral with the usual
Lebesgue integral on every continuous boundedly supported test function. -/
theorem integralComplex_ordinary (f : C(ℝ, ℂ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralComplex (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  have he : periodBCF (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      circlePull periodMap (ordinaryPeriod f) := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t =>
      change (∑' k : ℤ, f ((t+k : AF) : ℝ)) = ordinaryPeriod f ((t : ℝ) : UnitAddCircle)
      rw [ordinaryPeriod_apply f hs]
      rfl
  unfold integralComplex
  rw [he, ordinary_mean_integral]
  have hf := Real.fourierCoeff_tsum_comp_add (compact_local_summable f hs) 0
  simpa only [fourierCoeff, neg_zero, fourier_zero, one_smul, Int.cast_zero,
    Real.fourier_real_eq_integral_exp_smul, mul_zero, zero_mul, Complex.exp_zero, Complex.ofReal_zero,
    ordinaryPeriod, ContinuousMap.coe_mk] using hf

lemma integralComplex_re (h : AF → ℂ) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (rs : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → (h t).re = 0)
    (rb : ∀ t, ‖(h t).re‖ ≤ C) :
    (integralComplex h hs hb).re = integralReal (fun t => (h t).re) rs rb := by
  have he : realPart (periodBCF h hs hb) = periodBCF (fun t => (h t).re) rs rb := by
    ext x
    induction x using QuotientAddGroup.induction_on with
    | H t => exact Complex.reCLM.map_tsum (period_summable hs t)
  simp only [integralComplex, cmean, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_self, add_zero, he, integralReal]

theorem integralReal_ordinary (f : C(ℝ, ℝ)) {N : ℕ} {B : ℝ}
    (hs : ∀ t : ℝ, (N : ℝ) < |t| → f t = 0) (hb : ∀ t, ‖f t‖ ≤ B) :
    integralReal (fun t : AF => f t) (fun t ht => hs t ht) (fun t => hb t) =
      ∫ t : ℝ, f t := by
  let fc : C(ℝ, ℂ) := ⟨fun t => (f t : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hcs : ∀ t : ℝ, (N : ℝ) < |t| → fc t = 0 := by
    intro t ht
    simp [fc, hs t ht]
  have hcb : ∀ t, ‖fc t‖ ≤ B := by
    intro t
    simpa only [fc, coe_mk, Complex.norm_real] using hb t
  have hi := integralComplex_ordinary fc hcs hcb
  have hre := congrArg Complex.re hi
  rw [integralComplex_re _ _ _ (fun t ht => hs t ht) (fun t => hb t)] at hre
  change integralReal (fun t : AF => f t) _ _ = (∫ t : ℝ, (f t : ℂ)).re at hre
  rw [integral_complex_ofReal] at hre
  exact hre

end OrdinaryIntegral

section Smoothing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma weakIntegral_congr (h j : AF → H) {N M : ℕ} {B C : ℝ}
    (hs : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → h t = 0)
    (hb : ∀ t, ‖h t‖ ≤ B)
    (js : ∀ t : AF, (M : ℝ) < |(t : ℝ)| → j t = 0)
    (jb : ∀ t, ‖j t‖ ≤ C) (he : ∀ t, h t = j t) :
    weakIntegral h hs hb = weakIntegral j js jb := by
  unfold weakIntegral
  congr 1
  ext x
  induction x using QuotientAddGroup.induction_on with
  | H t => exact tsum_congr (fun k => he (t+k))

lemma shifted_support {φ : AF → ℝ} {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (s : AF) (hs : |(s : ℝ)| ≤ 1) :
    ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → φ (t-s) = 0 := by
  intro t ht
  apply hφ
  have hi : |(t : ℝ)| ≤ |(t : ℝ)-(s : ℝ)| + |(s : ℝ)| := by
    simpa using abs_add_le ((t : ℝ)-(s : ℝ)) (s : ℝ)
  change (N : ℝ) < |(t : ℝ)-(s : ℝ)|
  push_cast at ht
  linarith

variable (U : AF → H ≃ₗᵢ[ℝ] H)

omit [CompleteSpace H] in
lemma smoothed_support (φ : AF → ℝ) {N : ℕ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0) (v : H) :
    ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t • U t v = 0 := by
  intro t ht
  rw [hφ t ht, zero_smul]

omit [CompleteSpace H] in
lemma smoothed_bound (φ : AF → ℝ) {B : ℝ} (hb : ∀ t, |φ t| ≤ B) (v : H) :
    ∀ t, ‖φ t • U t v‖ ≤ B * ‖v‖ := by
  intro t
  rw [norm_smul, Real.norm_eq_abs, (U t).norm_map]
  exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg v)

def smoothedVector (φ : AF → ℝ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) : H :=
  weakIntegral (fun t => φ t • U t v) (smoothed_support U φ hφ v)
    (smoothed_bound U φ hb v)

/-- Translation continuity of smoothing rests only on regularity of the scalar
window, not on any measurability of the discrete representation. -/
theorem smoothed_translation_bound
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : AF → ℝ) {N : ℕ} {B C : ℝ}
    (hφ : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) (s : AF) (hs : |(s : ℝ)| ≤ 1)
    (hC : 0 ≤ C) (hd : ∀ t, |φ (t-s)-φ t| ≤ C) :
    ‖U s (smoothedVector U φ hφ hb v) - smoothedVector U φ hφ hb v‖ ≤
      (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * (C * ‖v‖) := by
  let h : AF → H := fun t => φ t • U t v
  let j : AF → H := fun t => φ (t-s) • U t v
  have hh := smoothed_support U φ hφ v
  have bh := smoothed_bound U φ hb v
  have hj := smoothed_support U (fun t => φ (t-s)) (shifted_support hφ s hs) v
  have bj := smoothed_bound U (fun t => φ (t-s)) (fun t => hb (t-s)) v
  have dh : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → j t-h t = 0 := by
    intro t ht
    change φ (t-s) • U t v - φ t • U t v = 0
    rw [hj t ht, hh t (by push_cast at ht; linarith), sub_self]
  have db : ∀ t, ‖j t-h t‖ ≤ C*‖v‖ := by
    intro t
    change ‖φ (t-s) • U t v - φ t • U t v‖ ≤ _
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, (U t).norm_map]
    exact mul_le_mul_of_nonneg_right (hd t) (norm_nonneg v)
  have kh : ∀ t : AF, (N : ℝ) < |(t : ℝ)| → U s (h t) = 0 := by
    intro t ht
    change U s (φ t • U t v) = 0
    rw [hh t ht, map_zero]
  have kb : ∀ t, ‖U s (h t)‖ ≤ B*‖v‖ := by
    intro t
    rw [(U s).norm_map]
    exact bh t
  have je : ∀ t, j t = U s (h (t+(-s))) := by
    intro t
    simp only [j, h, map_smul, hu, sub_eq_add_neg]
    congr 2
    abel_nf
  have kjs : ∀ t : AF, ((N+1 : ℕ) : ℝ) < |(t : ℝ)| → U s (h (t+(-s))) = 0 := by
    intro t ht
    rw [← je]
    exact hj t ht
  have kjb : ∀ t, ‖U s (h (t+(-s)))‖ ≤ B*‖v‖ := by
    intro t
    rw [← je]
    exact bj t
  have ji : weakIntegral j hj bj = U s (weakIntegral h hh bh) := by
    calc
      _ = weakIntegral (fun t => U s (h (t+(-s)))) kjs kjb :=
        weakIntegral_congr _ _ _ _ _ _ je
      _ = weakIntegral (fun t => U s (h t)) kh kb :=
        weakIntegral_shift (fun t => U s (h t)) (-s) kh kb kjs kjb
      _ = U s (weakIntegral h hh bh) :=
        weakIntegral_map (U s).toContinuousLinearEquiv.toContinuousLinearMap h hh bh kh kb
  have di := weakIntegral_sub j h hj bj hh bh dh db
  change ‖U s (weakIntegral h hh bh) - weakIntegral h hh bh‖ ≤ _
  rw [← ji, ← di]
  exact weakIntegral_norm_bound _ dh db (mul_nonneg hC (norm_nonneg v))

/-- Every uniformly continuous compact window produces a strongly continuous
vector even for a completely discontinuous representation of the discrete F. -/
theorem smoothed_tendsto
    (hu : ∀ s t v, U s (U t v) = U (s+t) v)
    (φ : ℝ → ℝ) (hc : UniformContinuous φ) {N : ℕ} {B : ℝ}
    (hφ : ∀ t : ℝ, (N : ℝ) < |t| → φ t = 0)
    (hb : ∀ t, |φ t| ≤ B) (v : H) :
    Tendsto (fun s : AF => U s
      (smoothedVector U (fun t => φ t) (fun t ht => hφ t ht) (fun t => hb t) v))
      (𝓝 0) (𝓝 (smoothedVector U (fun t => φ t)
        (fun t ht => hφ t ht) (fun t => hb t) v)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let Q : ℝ := (Finset.Icc (-((N+1 : ℕ) : ℤ)-2) (((N+1 : ℕ) : ℤ)+2)).card * ‖v‖
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg v)
  have hp : 0 < ε/(Q+1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hc _ hp
  have hnorm : ∀ᶠ s : AF in 𝓝 0, ‖s‖ < min δ 1 :=
    (show Tendsto (fun s : AF => ‖s‖) (𝓝 0) (𝓝 (0 : ℝ)) by
      simpa using continuous_norm.tendsto (0 : AF)).eventually
        (eventually_lt_nhds (lt_min hδ zero_lt_one))
  filter_upwards [hnorm] with s hs
  have hsδ : |(s : ℝ)| < δ := (lt_min_iff.mp hs).1
  have hs1 : |(s : ℝ)| ≤ 1 := le_of_lt (lt_min_iff.mp hs).2
  have hdiff : ∀ t : AF, |φ ((t-s : AF) : ℝ) - φ t| ≤ ε/(Q+1) := by
    intro t
    apply le_of_lt
    apply hd
    change |(t : ℝ)-(s : ℝ)-(t : ℝ)| < δ
    rw [show (t : ℝ)-(s : ℝ)-(t : ℝ) = -(s : ℝ) by ring, abs_neg]
    exact hsδ
  have hbound := smoothed_translation_bound U hu (fun t => φ t)
    (fun t ht => hφ t ht) (fun t => hb t) v s hs1 hp.le hdiff
  rw [dist_zero_right]
  apply hbound.trans_lt
  have hr : Q * (ε/(Q+1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < Q+1)]
    nlinarith
  simpa only [Q, mul_assoc, mul_comm (ε/(Q+1)) ‖v‖] using hr

end Smoothing
end PlaneFiveColor.InvariantMean
end
end
end

end OAI
