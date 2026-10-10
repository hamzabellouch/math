import OAI.InformationTheory.PhotonNumber.Functions

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace DiagonalForms.System
def logMean (X Y : ℝ) : ℝ := if X = Y then X else (Y-X) / (Real.log Y-Real.log X)
end DiagonalForms.System

namespace QuantumCalculus
theorem integral_exp_affine_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ s in (0 : ℝ)..1, Real.exp ((1-s)*Real.log p+s*Real.log q)) =
      DiagonalForms.System.logMean p q := by
  by_cases he : p = q
  · subst q
    have hh (s : ℝ) : (1-s)*Real.log p+s*Real.log p = Real.log p := by ring
    simp_rw [hh, Real.exp_log hp]
    simp [DiagonalForms.System.logMean]
  · have hd : Real.log q - Real.log p ≠ 0 := by
      intro h
      exact he ((Real.log_injOn_pos hp hq) (sub_eq_zero.mp h).symm)
    conv_lhs => arg 1; ext s
                rw [show (1-s)*Real.log p+s*Real.log q =
                  (Real.log q-Real.log p)*s+Real.log p by ring]
    rw [intervalIntegral.integral_comp_mul_add _ hd]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, integral_exp,
      Real.exp_log hp, Real.exp_log hq]
    simp [DiagonalForms.System.logMean, he, div_eq_mul_inv, mul_comm]
end QuantumCalculus

namespace DiagonalForms.System
@[simp] theorem logMean_self (p : ℝ) : logMean p p = p := by simp [logMean]
theorem logMean_symm (p q : ℝ) : logMean p q = logMean q p := by
  by_cases he : p = q
  · subst q; rfl
  · rw [logMean, ite_eq_right he, logMean, ite_eq_right (Ne.symm he)]
    rw [show p-q = -(q-p) by ring, show Real.log p-Real.log q = -(Real.log q-Real.log p) by ring]
    simp only [neg_div_neg_eq]
theorem logMean_pos {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : 0 < logMean p q := by
  rcases lt_trichotomy p q with h | h | h
  · rw [logMean, ite_eq_right h.ne]
    exact div_pos (sub_pos.mpr h) (sub_pos.mpr (Real.strictMonoOn_log hp hq h))
  · simp [h, hq]
  · rw [logMean_symm, logMean, ite_eq_right h.ne]
    exact div_pos (sub_pos.mpr h) (sub_pos.mpr (Real.strictMonoOn_log hq hp h))
theorem logMean_le_arithmetic {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : logMean p q ≤ (p+q)/2 := by
  rw [← QuantumCalculus.integral_exp_affine_log hp hq]
  calc
    _ ≤ ∫ s in (0:ℝ)..1, ((1-s)*p+s*q) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      · exact Continuous.intervalIntegrable (by fun_prop) _ _
      intro s hs
      have hh := convexOn_exp.2 (Set.mem_univ (Real.log p)) (Set.mem_univ (Real.log q))
        (sub_nonneg.mpr hs.2) hs.1 (by ring : (1-s)+s=1)
      simpa only [smul_eq_mul, Real.exp_log hp, Real.exp_log hq] using hh
    _ = (p+q)/2 := by
      rw [intervalIntegral.integral_add (by exact Continuous.intervalIntegrable (by fun_prop) _ _) (by exact Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (by exact Continuous.intervalIntegrable (by fun_prop) _ _) (by exact Continuous.intervalIntegrable (by fun_prop) _ _)]
      simp
      ring
end DiagonalForms.System

namespace DiagonalForms.System
open EntropyPhotonNumber

theorem logMean_exp_mul_f (u v : ℝ) :
    logMean (Real.exp u) (Real.exp v)*f ((u-v)/2)=Real.exp ((u+v)/2) := by
  by_cases he : u=v
  · subst v
    simp
  · have he' : Real.exp u ≠ Real.exp v := fun h => he (Real.exp_injective h)
    have hx : (u-v)/2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr he) (by norm_num)
    have hd : v-u ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
    have hu : Real.exp u=Real.exp ((u+v)/2)*Real.exp ((u-v)/2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hv : Real.exp v=Real.exp ((u+v)/2)*Real.exp (-((u-v)/2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [logMean, ite_eq_right he', Real.log_exp, Real.log_exp, f_of_ne_zero hx,
      hu, hv, Real.sinh_eq]
    have hsh : Real.exp ((u-v)/2)-Real.exp (-((u-v)/2)) ≠ 0 := by
      intro hh
      have hh' := Real.exp_injective (sub_eq_zero.mp hh)
      apply hx
      linarith
    field_simp
    ring

theorem logMean_mul_f {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q*f ((Real.log p-Real.log q)/2)=Real.exp ((Real.log p+Real.log q)/2) := by
  simpa only [Real.exp_log hp, Real.exp_log hq] using logMean_exp_mul_f (Real.log p) (Real.log q)

theorem logMean_arithmetic_plus {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q*f ((Real.log p-Real.log q)/2)*Real.exp ((Real.log p-Real.log q)/2)=p := by
  rw [logMean_mul_f hp hq, ← Real.exp_add]
  convert Real.exp_log hp using 1
  congr 1
  ring

theorem logMean_arithmetic_minus {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    logMean p q*f ((Real.log p-Real.log q)/2)*Real.exp (-((Real.log p-Real.log q)/2))=q := by
  rw [logMean_mul_f hp hq, ← Real.exp_add]
  convert Real.exp_log hq using 1
  congr 1
  ring

theorem logMean_product {a b c d : ℝ} (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) :
    logMean (a*c) (b*d)=logMean a b*fourWeightTarget (logMean c d)
      ((Real.log a-Real.log b)/2) ((Real.log c-Real.log d)/2) := by
  have hh :
      (logMean a b*f ((Real.log a-Real.log b)/2))*(logMean c d*f ((Real.log c-Real.log d)/2))=
      logMean (a*c) (b*d)*f (((Real.log a-Real.log b)/2)+((Real.log c-Real.log d)/2)) := by
    rw [logMean_mul_f ha hb, logMean_mul_f hc hd, ← Real.exp_add]
    rw [show ((Real.log a-Real.log b)/2)+((Real.log c-Real.log d)/2) =
      (Real.log (a*c)-Real.log (b*d))/2 by rw [Real.log_mul ha.ne' hc.ne', Real.log_mul hb.ne' hd.ne']; ring,
      logMean_mul_f (mul_pos ha hc) (mul_pos hb hd)]
    congr 1
    rw [Real.log_mul ha.ne' hc.ne', Real.log_mul hb.ne' hd.ne']
    ring
  unfold fourWeightTarget
  have hf := (f_pos (((Real.log a-Real.log b)/2)+((Real.log c-Real.log d)/2))).ne'
  rw [← mul_div_assoc]
  apply (eq_div_iff hf).mpr
  nlinarith [hh]

theorem logMean_scale {p q : ℝ} (hp : 0<p) (hq : 0<q) {c : ℝ} (hc : 0<c) :
    logMean (c*p) (c*q)=c*logMean p q := by
  by_cases he : p=q
  · subst q; simp
  · have he' : c*p ≠ c*q := fun h => he (mul_left_cancel₀ hc.ne' h)
    rw [logMean, ite_eq_right he', Real.log_mul hc.ne' hq.ne', Real.log_mul hc.ne' hp.ne',
      logMean, ite_eq_right he]
    ring

theorem logMean_mono {p q a b : ℝ} (hp : 0<p) (hq : 0<q) (hpa : p≤a) (hqb : q≤b) :
    logMean p q≤logMean a b := by
  rw [← QuantumCalculus.integral_exp_affine_log hp hq,
    ← QuantumCalculus.integral_exp_affine_log (hp.trans_le hpa) (hq.trans_le hqb)]
  apply intervalIntegral.integral_mono_on (by norm_num)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro s hs
  apply Real.exp_le_exp.mpr
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.log_le_log hp hpa) (sub_nonneg.mpr hs.2))
    (mul_le_mul_of_nonneg_left (Real.log_le_log hq hqb) hs.1)

end DiagonalForms.System

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace DiagonalForms

structure System (P I J : Type*) where
  sourceParam : I → P
  targetParam : J → P
  tests : Submodule ℂ (I → ℂ)
  map : tests →ₗ[ℂ] (J → ℂ)
  mass_summable : ∀ z : tests, Summable (fun i => Complex.normSq (z.val i))
  finite_values : ∀ z : tests, ∃ s : Finset P, ∀ i, z.val i ≠ 0 → sourceParam i ∈ s
  multiplier_mem : ∀ (z : tests) (w : P → ℂ), (fun i => w (sourceParam i) * z.val i) ∈ tests

namespace System

variable {P I J : Type*} (D : System P I J)

def sourceForm (w : P → ℝ) (z : D.tests) : ℝ :=
  ∑' i, w (D.sourceParam i) * Complex.normSq (z.val i)

def Comparison (w : P → ℝ) : Prop :=
  ∀ (z : D.tests) (s : Finset J),
    ∑ j ∈ s, w (D.targetParam j) * Complex.normSq (D.map z j) ≤ D.sourceForm w z

def multiplier (w : P → ℝ) (z : D.tests) : D.tests :=
  ⟨fun i => (w (D.sourceParam i) : ℂ) * z.val i, D.multiplier_mem z (fun p => (w p : ℂ))⟩

@[simp] theorem multiplier_apply (w : P → ℝ) (z : D.tests) (i : I) :
    (D.multiplier w z).val i = (w (D.sourceParam i) : ℂ) * z.val i := rfl

theorem source_summable (w : P → ℝ) (z : D.tests) :
    Summable (fun i => w (D.sourceParam i) * Complex.normSq (z.val i)) := by
  classical
  obtain ⟨s, hs⟩ := D.finite_values z
  let B : ℝ := ∑ p ∈ s, |w p|
  apply Summable.of_norm_bounded ((D.mass_summable z).mul_left B)
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
  by_cases hz : z.val i = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun p _ => abs_nonneg (w p)) (hs i hz)) (Complex.normSq_nonneg _)

theorem comparison_add {v w : P → ℝ} (hv : D.Comparison v) (hw : D.Comparison w) :
    D.Comparison (fun p => v p + w p) := by
  intro z s
  simp only [add_mul, Finset.sum_add_distrib]
  simp only [sourceForm, add_mul]
  rw [(D.source_summable v z).tsum_add (D.source_summable w z)]
  exact add_le_add (hv z s) (hw z s)

theorem comparison_smul {w : P → ℝ} (hw : D.Comparison w) {a : ℝ} (ha : 0 ≤ a) :
    D.Comparison (fun p => a * w p) := by
  intro z s
  simp only [mul_assoc, ← Finset.mul_sum]
  simp only [sourceForm, mul_assoc, tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (hw z s) ha

def parallel (x y : ℝ) : ℝ := x * y / (x + y)

theorem parallel_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < parallel x y := by
  unfold parallel
  positivity

theorem parallel_norm_bound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (u v : ℂ) :
    parallel x y * Complex.normSq (u + v) ≤ x * Complex.normSq u + y * Complex.normSq v := by
  unfold parallel
  rw [div_mul_eq_mul_div, div_le_iff₀ (add_pos hx hy)]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (x * u.re - y * v.re), sq_nonneg (x * u.im - y * v.im)]

theorem parallel_minimum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    x * Complex.normSq (((y / (x + y) : ℝ) : ℂ) * z) +
      y * Complex.normSq (((x / (x + y) : ℝ) : ℂ) * z) = parallel x y * Complex.normSq z := by
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  unfold parallel
  field_simp [ne_of_gt (add_pos hx hy)]
  ring

theorem comparison_parallel {v w : P → ℝ} (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => parallel (v p) (w p)) := by
  intro z s
  let u := D.multiplier (fun p => w p / (v p + w p)) z
  let t := D.multiplier (fun p => v p / (v p + w p)) z
  have hut : u + t = z := by
    apply Subtype.ext
    funext i
    simp only [u, t, Submodule.coe_add, Pi.add_apply, multiplier_apply,
      ← add_mul, ← Complex.ofReal_add]
    rw [← add_div, add_comm (w _), div_self (ne_of_gt (add_pos (hvp _) (hwp _)))]
    simp
  have hmap (j : J) : D.map u j + D.map t j = D.map z j := by
    rw [← Pi.add_apply, ← map_add, hut]
  calc
    _ ≤ ∑ j ∈ s, (v (D.targetParam j) * Complex.normSq (D.map u j) +
        w (D.targetParam j) * Complex.normSq (D.map t j)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← hmap j]
      exact parallel_norm_bound (hvp _) (hwp _) _ _
    _ = (∑ j ∈ s, v (D.targetParam j) * Complex.normSq (D.map u j)) +
        ∑ j ∈ s, w (D.targetParam j) * Complex.normSq (D.map t j) := Finset.sum_add_distrib
    _ ≤ D.sourceForm v u + D.sourceForm w t := add_le_add (hv u s) (hw t s)
    _ = D.sourceForm (fun p => parallel (v p) (w p)) z := by
      simp only [sourceForm]
      rw [← (D.source_summable v u).tsum_add (D.source_summable w t)]
      apply tsum_congr
      intro i
      exact parallel_minimum (hvp _) (hwp _) (z.val i)

theorem sourceForm_finite (z : D.tests) :
    ∃ (s : Finset P) (c : P → ℝ), ∀ w : P → ℝ,
      D.sourceForm w z = ∑ p ∈ s, w p * c p := by
  classical
  obtain ⟨s, hs⟩ := D.finite_values z
  let c (p : P) : ℝ := ∑' i, if p = D.sourceParam i then Complex.normSq (z.val i) else 0
  refine ⟨s, c, ?_⟩
  intro w
  have hsum (p : P) : Summable (fun i => if p = D.sourceParam i then Complex.normSq (z.val i) else 0) := by
    apply Summable.of_nonneg_of_le _ _ (D.mass_summable z)
    · intro i
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl
    · intro i
      split_ifs
      · exact le_rfl
      · exact Complex.normSq_nonneg _
  simp only [c, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun p _ => (hsum p).mul_left (w p))]
  apply tsum_congr
  intro i
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases hz : z.val i = 0
  · simp [hz]
  · simp [hs i hz]

theorem sourceForm_tendsto {α : Type*} {l : Filter α} {w : α → P → ℝ} {v : P → ℝ}
    (h : ∀ p, Tendsto (fun a => w a p) l (𝓝 (v p))) (z : D.tests) :
    Tendsto (fun a => D.sourceForm (w a) z) l (𝓝 (D.sourceForm v z)) := by
  obtain ⟨s, c, hc⟩ := D.sourceForm_finite z
  simp_rw [hc]
  exact tendsto_finsetSum s (fun p _ => (h p).mul_const (c p))

theorem comparison_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {w : α → P → ℝ} {v : P → ℝ} (hw : ∀ a, D.Comparison (w a))
    (hlim : ∀ p, Tendsto (fun a => w a p) l (𝓝 (v p))) : D.Comparison v := by
  intro z s
  exact le_of_tendsto_of_tendsto
    (tendsto_finsetSum s (fun j _ => (hlim _).mul_const _))
    (D.sourceForm_tendsto hlim z) (Eventually.of_forall (fun a => hw a z s))

theorem comparison_zero : D.Comparison (fun _ => 0) := by
  intro z s
  simp [sourceForm]

theorem comparison_finsetSum {K : Type*} (s : Finset K) {w : K → P → ℝ}
    (hw : ∀ k ∈ s, D.Comparison (w k)) : D.Comparison (fun p => ∑ k ∈ s, w k p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using D.comparison_zero
  | @insert k s hk ih =>
    simp only [Finset.forall_mem_insert] at hw
    simpa only [Finset.sum_insert hk] using D.comparison_add hw.1 (ih hw.2)


theorem comparison_tsum {w : P → ℝ} (hw : D.Comparison w) (hp : ∀ p, 0 ≤ w p)
    (z : D.tests) :
    Summable (fun j => w (D.targetParam j) * Complex.normSq (D.map z j)) ∧
      (∑' j, w (D.targetParam j) * Complex.normSq (D.map z j)) ≤ D.sourceForm w z := by
  have hx (j : J) : 0 ≤ w (D.targetParam j) * Complex.normSq (D.map z j) :=
    mul_nonneg (hp _) (Complex.normSq_nonneg _)
  exact ⟨summable_of_sum_le hx (hw z), Real.tsum_le_of_sum_le hx (hw z)⟩

end System

end DiagonalForms

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem parallel_inv {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    parallel x⁻¹ y⁻¹ = (x + y)⁻¹ := by
  unfold parallel
  field_simp
  ring

theorem comparison_harmonic_sum_pos {K : Type*} (s : Finset K) (hs : s.Nonempty)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 < c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hs).elim
  | @insert k s hk ih =>
    have hkpos := hc k (Finset.mem_insert_self k s)
    have hkw := hwp k (Finset.mem_insert_self k s)
    have hkc := hw k (Finset.mem_insert_self k s)
    have hcomp : D.Comparison (fun p => (c k / w k p)⁻¹) := by
      simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using
        D.comparison_smul hkc (le_of_lt (inv_pos.mpr hkpos))
    by_cases he : s.Nonempty
    · have hcs : ∀ j ∈ s, 0 < c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
      have hws : ∀ j ∈ s, ∀ p, 0 < w j p := fun j hj => hwp j (Finset.mem_insert_of_mem hj)
      have hcps : ∀ j ∈ s, D.Comparison (w j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
      have hsum (p : P) : 0 < ∑ j ∈ s, c j / w j p :=
        Finset.sum_pos (fun j hj => div_pos (hcs j hj) (hws j hj p)) he
      have hh := D.comparison_parallel hcomp (ih he hcs hws hcps)
        (fun p => inv_pos.mpr (div_pos hkpos (hkw p)))
        (fun p => inv_pos.mpr (hsum p))
      simpa only [Finset.sum_insert hk, parallel_inv (div_pos hkpos (hkw _)) (hsum _)] using hh
    · have hem : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simpa [hem] using hcomp

theorem comparison_harmonic_sum {K : Type*} (s : Finset K)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hex : ∃ k ∈ s, 0 < c k)
    (hwp : ∀ k ∈ s, ∀ p, 0 < w k p) (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  let t := s.filter (fun k => 0 < c k)
  have ht : t.Nonempty := by
    obtain ⟨k, hk, hck⟩ := hex
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hck⟩⟩
  have he (p : P) : (∑ k ∈ t, c k / w k p) = ∑ k ∈ s, c k / w k p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkt
    have hck : c k = 0 := by
      have : ¬ 0 < c k := fun h => hkt (Finset.mem_filter.mpr ⟨hk, h⟩)
      exact le_antisymm (le_of_not_gt this) (hc k hk)
    simp [hck]
  have hh := D.comparison_harmonic_sum_pos t ht
    (fun k hk => (Finset.mem_filter.mp hk).2)
    (fun k hk => hwp k (Finset.mem_filter.mp hk).1)
    (fun k hk => hw k (Finset.mem_filter.mp hk).1)
  simpa only [he] using hh


theorem integral_comp_simpleFunc {X K : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : MeasureTheory.SimpleFunc X K) (g : K → ℝ) :
    (∫ x, g (f x) ∂μ) = ∑ k ∈ f.range, μ.real (f ⁻¹' {k}) * g k := by
  classical
  have hi (k : K) : Integrable ((f ⁻¹' {k}).indicator (fun _ => g k)) μ :=
    (integrable_const _).indicator (f.measurableSet_fiber k)
  have he (x : X) : g (f x) = ∑ k ∈ f.range, (f ⁻¹' {k}).indicator (fun _ => g k) x := by
    simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
    rw [Finset.sum_ite_eq]
    simp only [SimpleFunc.mem_range, Set.mem_range_self, ↓reduceIte]
  simp_rw [he]
  rw [integral_finsetSum f.range (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_indicator (f.measurableSet_fiber k), setIntegral_const, smul_eq_mul]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem comparison_harmonic_sum_add {K : Type*} (s : Finset K)
    {v : P → ℝ} {w : K → P → ℝ} {c : K → ℝ}
    (hv : D.Comparison v) (hvp : ∀ p, 0 < v p)
    (hc : ∀ k ∈ s, 0 ≤ c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => ((v p)⁻¹ + ∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hv
  | @insert k s hk ih =>
    have hcs : ∀ j ∈ s, 0 ≤ c j := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    have hws : ∀ j ∈ s, ∀ p, 0 < w j p := fun j hj => hwp j (Finset.mem_insert_of_mem hj)
    have hcomp := ih hcs hws (fun j hj => hw j (Finset.mem_insert_of_mem hj))
    have hk0 := hc k (Finset.mem_insert_self k s)
    rcases eq_or_lt_of_le hk0 with he | hp
    · simpa only [Finset.sum_insert hk, ← he, zero_div, zero_add] using hcomp
    · have hsmall := D.comparison_smul (hw k (Finset.mem_insert_self k s))
        (le_of_lt (inv_pos.mpr hp))
      have hsmall' : D.Comparison (fun p => (c k / w k p)⁻¹) := by
        simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_comm] using hsmall
      have hsum (p : P) : 0 < (v p)⁻¹ + ∑ j ∈ s, c j / w j p :=
        add_pos_of_pos_of_nonneg (inv_pos.mpr (hvp p))
          (Finset.sum_nonneg (fun j hj => div_nonneg (hcs j hj) (hws j hj p).le))
      have hkp (p : P) : 0 < c k / w k p :=
        div_pos hp (hwp k (Finset.mem_insert_self k s) p)
      have h := D.comparison_parallel hsmall' hcomp
        (fun p => inv_pos.mpr (hkp p)) (fun p => inv_pos.mpr (hsum p))
      simpa only [parallel_inv (hkp _) (hsum _), Finset.sum_insert hk, add_left_comm] using h

section CompactIntegral
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

def compactApprox (n : ℕ) : SimpleFunc K K :=
  SimpleFunc.approxOn id measurable_id Set.univ k₀ (Set.mem_univ _) n

theorem integral_compactApprox_tendsto {g : K → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ k, g (compactApprox k₀ n k) ∂μ) atTop (𝓝 (∫ k, g k ∂μ)) := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
  · intro n
    exact (hg.measurable.comp (compactApprox k₀ n).measurable).aestronglyMeasurable
  · exact integrable_const M
  · intro n
    exact Filter.Eventually.of_forall (fun k => hM _ (Set.mem_univ _))
  · apply Filter.Eventually.of_forall
    intro k
    apply hg.continuousAt.tendsto.comp
    exact SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ k₀) (by simp)

include k₀ in
theorem comparison_integral {w : K → P → ℝ}
    (hcont : ∀ p, Continuous (fun k => w k p)) (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => ∫ k, w k p ∂μ) := by
  apply D.comparison_tendsto (l := atTop)
    (w := fun n p => ∫ k, w (compactApprox k₀ n k) p ∂μ)
  · intro n
    have he (p : P) := integral_comp_simpleFunc μ (compactApprox k₀ n) (fun k => w k p)
    simp_rw [he]
    apply D.comparison_finsetSum
    intro k _
    exact D.comparison_smul (hw k) ENNReal.toReal_nonneg
  · intro p
    exact integral_compactApprox_tendsto μ k₀ (hcont p)

include k₀ in
theorem comparison_inverse_integral_add {v : P → ℝ} {w : K → P → ℝ}
    (hv : D.Comparison v) (hvp : ∀ p, 0 < v p)
    (hcont : ∀ p, Continuous (fun k => w k p)) (hwp : ∀ k p, 0 < w k p)
    (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => ((v p)⁻¹ + ∫ k, (w k p)⁻¹ ∂μ)⁻¹) := by
  apply D.comparison_tendsto (l := atTop)
    (w := fun n p => ((v p)⁻¹ + ∫ k, (w (compactApprox k₀ n k) p)⁻¹ ∂μ)⁻¹)
  · intro n
    have he (p : P) := integral_comp_simpleFunc μ (compactApprox k₀ n) (fun k => (w k p)⁻¹)
    simp_rw [he]
    simpa only [div_eq_mul_inv, Measure.real] using D.comparison_harmonic_sum_add
      (compactApprox k₀ n).range hv hvp (fun _ _ => ENNReal.toReal_nonneg)
      (fun k _ => hwp k) (fun k _ => hw k)
  · intro p
    apply Tendsto.inv₀
    · exact tendsto_const_nhds.add (integral_compactApprox_tendsto μ k₀
        ((hcont p).inv₀ (fun k => (hwp k p).ne')))
    · exact ne_of_gt (add_pos_of_pos_of_nonneg (inv_pos.mpr (hvp p))
        (integral_nonneg (fun k => inv_nonneg.mpr (hwp k p).le)))

end CompactIntegral
end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem comparison_harmonic_sum_nonneg {K : Type*} (s : Finset K)
    {w : K → P → ℝ} {c : K → ℝ}
    (hc : ∀ k ∈ s, 0 ≤ c k) (hwp : ∀ k ∈ s, ∀ p, 0 < w k p)
    (hw : ∀ k ∈ s, D.Comparison (w k)) :
    D.Comparison (fun p => (∑ k ∈ s, c k / w k p)⁻¹) := by
  classical
  by_cases h : ∃ k ∈ s, 0 < c k
  · exact D.comparison_harmonic_sum s hc h hwp hw
  · have hz : ∀ k ∈ s, c k = 0 := by
      intro k hk
      exact le_antisymm (le_of_not_gt (fun hh => h ⟨k, hk, hh⟩)) (hc k hk)
    have he (p : P) : ∑ k ∈ s, c k / w k p = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [hz k hk]
    simpa only [he, inv_zero] using D.comparison_zero

theorem comparison_inverse_integral {K : Type*} [MetricSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (k₀ : K) (hμ : μ ≠ 0) {w : K → P → ℝ}
    (hcont : ∀ p, Continuous (fun k => w k p)) (hwp : ∀ k p, 0 < w k p)
    (hw : ∀ k, D.Comparison (w k)) :
    D.Comparison (fun p => (∫ k, (w k p)⁻¹ ∂μ)⁻¹) := by
  apply D.comparison_tendsto (l := atTop)
    (w := fun n p => (∫ k, (w (compactApprox k₀ n k) p)⁻¹ ∂μ)⁻¹)
  · intro n
    have he (p : P) := integral_comp_simpleFunc μ (compactApprox k₀ n) (fun k => (w k p)⁻¹)
    simp_rw [he]
    simpa only [div_eq_mul_inv, Measure.real] using D.comparison_harmonic_sum_nonneg
      (compactApprox k₀ n).range (fun _ _ => ENNReal.toReal_nonneg)
      (fun k _ => hwp k) (fun k _ => hw k)
  · intro p
    have hg : Continuous (fun k => (w k p)⁻¹) :=
      (hcont p).inv₀ (fun k => (hwp k p).ne')
    have hs : Function.support (fun k => (w k p)⁻¹) = Set.univ := by
      ext k
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact inv_ne_zero (hwp k p).ne'
    have hi : 0 < ∫ k, (w k p)⁻¹ ∂μ := by
      rw [integral_pos_iff_support_of_nonneg
        (fun k => inv_nonneg.mpr (hwp k p).le)
        (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)), hs]
      exact Measure.measure_univ_pos.mpr hμ
    exact (integral_compactApprox_tendsto μ k₀ hg).inv₀ hi.ne'

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

theorem integral_unitInterval (f : ℝ → ℝ) :
    (∫ t : UnitInterval, f t.val) = ∫ t in (0 : ℝ)..1, f t := by
  rw [integral_subtype measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

theorem unitInterval_volume : (volume : Measure UnitInterval) Set.univ = 1 := by
  simp [UnitInterval]

theorem affine_pos {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (t : UnitInterval) :
    0 < (1 - t.val) * X + t.val * Y := by
  rcases t.property.1.eq_or_lt with ht | ht
  · simp [← ht, hX]
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) hX.le) (mul_pos ht hY)
theorem integral_affine_inv {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    (∫ t : UnitInterval, ((1-t.val)*X+t.val*Y)⁻¹) = (logMean X Y)⁻¹ := by
  rw [integral_unitInterval (fun t => ((1-t)*X+t*Y)⁻¹)]
  by_cases he : X = Y
  · subst Y
    simp only [logMean]
    conv_lhs => arg 1; ext t; rw [show (1-t)*X+t*X = X by ring]
    simp
  · have hd : Y-X ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
    conv_lhs => arg 1; ext t; rw [show (1-t)*X+t*Y = (Y-X)*t+X by ring]
    rw [intervalIntegral.integral_comp_mul_add _ hd]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [integral_inv_of_pos hX hY, Real.log_div hY.ne' hX.ne']
    simp [logMean, he, div_eq_mul_inv, mul_comm]

theorem comparison_logMean {v w : P → ℝ}
    (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => logMean (v p) (w p)) := by
  have ha (t : UnitInterval) : D.Comparison (fun p => (1-t.val)*v p+t.val*w p) :=
    D.comparison_add (D.comparison_smul hv (sub_nonneg.mpr t.property.2))
      (D.comparison_smul hw t.property.1)
  have hc (p : P) : Continuous (fun t : UnitInterval => (1-t.val)*v p+t.val*w p) := by
    fun_prop
  have hμ : (volume : Measure UnitInterval) ≠ 0 := by
    intro h
    have h1 := unitInterval_volume
    rw [h] at h1
    simp at h1
  have hh := D.comparison_inverse_integral volume ⟨0, by norm_num⟩ hμ hc
    (fun t p => affine_pos (hvp p) (hwp p) t) ha
  simp_rw [integral_affine_inv (hvp _) (hwp _), inv_inv] at hh
  exact hh

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)

theorem inverse_logMean_inverse {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    (logMean X⁻¹ Y⁻¹)⁻¹ = X*Y/logMean X Y := by
  by_cases he : X = Y
  · subst Y
    simp [logMean, hX.ne']
  · have he' : X⁻¹ ≠ Y⁻¹ := fun h => he (inv_injective h)
    have hd : Y-X ≠ 0 := sub_ne_zero.mpr (Ne.symm he)
    have hl : Real.log Y - Real.log X ≠ 0 := by
      apply sub_ne_zero.mpr
      intro h
      apply he
      exact (Real.log_injOn_pos hY hX h).symm
    simp only [logMean, ite_eq_right he, ite_eq_right he', Real.log_inv]
    field_simp
    ring

theorem comparison_dualLogMean {v w : P → ℝ}
    (hv : D.Comparison v) (hw : D.Comparison w)
    (hvp : ∀ p, 0 < v p) (hwp : ∀ p, 0 < w p) :
    D.Comparison (fun p => v p*w p/logMean (v p) (w p)) := by
  have ha (t : UnitInterval) :
      D.Comparison (fun p => ((1-t.val)/(v p)+t.val/(w p))⁻¹) := by
    have hh := D.comparison_harmonic_sum_nonneg (Finset.univ : Finset (Fin 2))
      (w := fun i p => if i = 0 then v p else w p)
      (c := fun i => if i = 0 then 1-t.val else t.val)
      (by intro i _; split_ifs; exact sub_nonneg.mpr t.property.2; exact t.property.1)
      (by intro i _ p; split_ifs; exact hvp p; exact hwp p)
      (by intro i _; split_ifs; exact hv; exact hw)
    simpa [Fin.sum_univ_two] using hh
  have hc (p : P) :
      Continuous (fun t : UnitInterval => ((1-t.val)/(v p)+t.val/(w p))⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t
      simpa [div_eq_mul_inv] using (affine_pos (inv_pos.mpr (hvp p))
        (inv_pos.mpr (hwp p)) t).ne'
  have hh := D.comparison_integral volume (⟨0, by norm_num⟩ : UnitInterval) hc ha
  have he (p : P) : (∫ t : UnitInterval, ((1-t.val)/(v p)+t.val/(w p))⁻¹) =
      v p*w p/logMean (v p) (w p) := by
    simp only [div_eq_mul_inv]
    rw [integral_affine_inv (inv_pos.mpr (hvp p)) (inv_pos.mpr (hwp p)),
      inverse_logMean_inverse (hvp p) (hwp p), div_eq_mul_inv]
  simp_rw [he] at hh
  exact hh

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] (k₀ : K)

def resolventWeight (c : ℝ) (r : K → ℝ) (q : ℝ) : ℝ :=
  q⁻¹ + c + ∫ k, (1+(q-1)*r k)⁻¹ ∂μ

theorem resolvent_kernel_pos {q r : ℝ} (hq : 0 < q) (hr : r ∈ Icc 0 1) :
    0 < 1+(q-1)*r := by
  have h := affine_pos (X := 1) (Y := q) (by norm_num) hq ⟨r, hr⟩
  dsimp at h
  nlinarith

include k₀ in
theorem comparison_resolvent {m q : P → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    (hm : ∀ p, 0 < m p) (hq : ∀ p, 0 < q p)
    (hmcomp : D.Comparison m) (hqcomp : D.Comparison (fun p => m p*q p)) :
    D.Comparison (fun p => m p / resolventWeight μ c r (q p)) := by
  let v (p : P) := ((m p*q p)⁻¹+c/(m p))⁻¹
  have hv : D.Comparison v := by
    have h := D.comparison_harmonic_sum_nonneg (Finset.univ : Finset (Fin 2))
      (w := fun i p => if i = 0 then m p*q p else m p)
      (c := fun i => if i = 0 then 1 else c)
      (by intro i _; split_ifs; norm_num; exact hc)
      (by intro i _ p; split_ifs; exact mul_pos (hm p) (hq p); exact hm p)
      (by intro i _; split_ifs; exact hqcomp; exact hmcomp)
    simpa [v, Fin.sum_univ_two] using h
  have hvp (p : P) : 0 < v p := inv_pos.mpr
    (add_pos_of_pos_of_nonneg (inv_pos.mpr (mul_pos (hm p) (hq p)))
      (div_nonneg hc (hm p).le))
  let w (k : K) (p : P) := m p*(1+(q p-1)*r k)
  have hwp (k : K) (p : P) : 0 < w k p :=
    mul_pos (hm p) (resolvent_kernel_pos (hq p) (hr k))
  have hw (k : K) : D.Comparison (w k) := by
    have h := D.comparison_add (D.comparison_smul hmcomp (sub_nonneg.mpr (hr k).2))
      (D.comparison_smul hqcomp (hr k).1)
    convert h using 1
    funext p
    dsimp [w]
    ring
  have hwc (p : P) : Continuous (fun k => w k p) := by
    dsimp [w]
    fun_prop
  have h := D.comparison_inverse_integral_add μ k₀ hv hvp hwc hwp hw
  convert h using 1
  funext p
  dsimp [v, w, resolventWeight]
  simp only [inv_inv, mul_inv_rev]
  rw [integral_mul_const]
  simp only [div_eq_mul_inv]
  rw [show (q p)⁻¹ * (m p)⁻¹ + c*(m p)⁻¹ +
      (∫ k, (1+(q p-1)*r k)⁻¹ ∂μ)*(m p)⁻¹ =
      ((q p)⁻¹+c+∫ k, (1+(q p-1)*r k)⁻¹ ∂μ)*(m p)⁻¹ by ring]
  simp only [mul_inv_rev, inv_inv]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {P I J : Type*} (D : DiagonalForms.System P I J)
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

omit [MetricSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure μ] in
theorem resolventWeight_pos {c : ℝ} (hc : 0 ≤ c) {r : K → ℝ}
    (hr : ∀ k, r k ∈ Icc 0 1) {q : ℝ} (hq : 0 < q) :
    0 < resolventWeight μ c r q := by
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (inv_pos.mpr hq) hc)
    (integral_nonneg (fun k => inv_nonneg.mpr (resolvent_kernel_pos hq (hr k)).le))

theorem continuous_resolvent_affine {c : ℝ} {r : K → ℝ} (hrc : Continuous r)
    (hr : ∀ k, r k ∈ Icc 0 1) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    Continuous (fun θ : UnitInterval =>
      resolventWeight μ c r ((1-θ.val)*s+θ.val*t)) := by
  have hk : Continuous (fun z : UnitInterval × K =>
      (1+(((1-z.1.val)*s+z.1.val*t)-1)*r z.2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro z
      exact (resolvent_kernel_pos (affine_pos hs ht z.1) (hr z.2)).ne'
  have hi : Continuous (fun θ : UnitInterval =>
      ∫ k, (1+(((1-θ.val)*s+θ.val*t)-1)*r k)⁻¹ ∂μ) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := μ) hk isCompact_univ)
  exact ((by fun_prop : Continuous (fun θ : UnitInterval => (1-θ.val)*s+θ.val*t)).inv₀
    (fun θ => (affine_pos hs ht θ).ne') |>.add continuous_const).add hi



theorem comparison_resolvent_average (k₀ : K) {m s t : P → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    (hm : ∀ p, 0 < m p) (hs : ∀ p, 0 < s p) (ht : ∀ p, 0 < t p)
    (hmc : D.Comparison m) (hsc : D.Comparison (fun p => m p*s p))
    (htc : D.Comparison (fun p => m p*t p)) :
    D.Comparison (fun p => m p / ∫ θ : UnitInterval,
      resolventWeight μ c r ((1-θ.val)*s p+θ.val*t p)) := by
  let q (θ : UnitInterval) (p : P) := (1-θ.val)*s p+θ.val*t p
  have hqc (θ : UnitInterval) : D.Comparison (fun p => m p*q θ p) := by
    have h := D.comparison_add (D.comparison_smul hsc (sub_nonneg.mpr θ.property.2))
      (D.comparison_smul htc θ.property.1)
    convert h using 1
    funext p
    dsimp [q]
    ring
  have hqp (θ : UnitInterval) (p : P) : 0 < q θ p := affine_pos (hs p) (ht p) θ
  have hw (θ : UnitInterval) :
      D.Comparison (fun p => m p / resolventWeight μ c r (q θ p)) :=
    D.comparison_resolvent μ k₀ hc hrc hr hm (hqp θ) hmc (hqc θ)
  have hwp (θ : UnitInterval) (p : P) :
      0 < m p / resolventWeight μ c r (q θ p) :=
    div_pos (hm p) (resolventWeight_pos μ hc hr (hqp θ p))
  have hcont (p : P) : Continuous (fun θ : UnitInterval =>
      m p / resolventWeight μ c r (q θ p)) := by
    exact continuous_const.div (continuous_resolvent_affine μ hrc hr (hs p) (ht p))
      (fun θ => (resolventWeight_pos μ hc hr (hqp θ p)).ne')
  have hμ : (volume : Measure UnitInterval) ≠ 0 := by
    intro h
    have h1 := unitInterval_volume
    rw [h] at h1
    simp at h1
  have h := D.comparison_inverse_integral volume ⟨0, by norm_num⟩ hμ hcont hwp hw
  convert h using 1
  funext p
  dsimp [q]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, integral_mul_const]

end DiagonalForms.System

namespace DiagonalForms.System
open MeasureTheory Set
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]

theorem continuous_resolvent_comp {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    {c : ℝ} {r : K → ℝ} (hrc : Continuous r) (hr : ∀ k, r k ∈ Icc 0 1)
    {q : X → ℝ} (hqc : Continuous q) (hqp : ∀ x, 0 < q x) :
    Continuous (fun x => resolventWeight μ c r (q x)) := by
  have hk : Continuous (fun z : X × K => (1+(q z.1-1)*r z.2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro z
      exact (resolvent_kernel_pos (hqp z.1) (hr z.2)).ne'
  have hi : Continuous (fun x => ∫ k, (1+(q x-1)*r k)⁻¹ ∂μ) := by
    simpa only [setIntegral_univ] using
      (continuous_parametric_integral_of_continuous (μ := μ) hk isCompact_univ)
  exact ((hqc.inv₀ (fun x => (hqp x).ne')).add continuous_const).add hi

theorem continuousOn_resolventWeight {c : ℝ} {r : K → ℝ} (hrc : Continuous r)
    (hr : ∀ k, r k ∈ Icc 0 1) : ContinuousOn (resolventWeight μ c r) (Ioi 0) := by
  let : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_resolvent_comp μ hrc hr continuous_subtype_val (fun x => x.property)

end DiagonalForms.System

namespace DiagonalForms.System
open Function
variable {P I J : Type*} (D : DiagonalForms.System P I J)

def fiveQuadratic (v₀ v₁ v₂ v₃ v₄ : ℝ) (ξ φ : ℂ) : ℝ :=
  v₀*Complex.normSq (ξ-φ) + v₁*Complex.normSq (ξ+φ) +
  v₂*Complex.normSq (ξ+φ) + v₃*Complex.normSq (ξ-φ) + v₄*Complex.normSq φ




theorem comparison_fiveQuadratic {v₀ v₁ v₂ v₃ v₄ F δ : P → ℝ}
    (h₀ : D.Comparison v₀) (h₁ : D.Comparison v₁) (h₂ : D.Comparison v₂)
    (h₃ : D.Comparison v₃) (h₄ : D.Comparison v₄)
    (hmin : ∀ p ξ, fiveQuadratic (v₀ p) (v₁ p) (v₂ p) (v₃ p) (v₄ p)
      ξ ((δ p : ℂ)*ξ) = F p*Complex.normSq ξ)
    (hlower : ∀ p ξ φ, F p*Complex.normSq ξ ≤
      fiveQuadratic (v₀ p) (v₁ p) (v₂ p) (v₃ p) (v₄ p) ξ φ) :
    D.Comparison F := by
  intro z s
  let φ := D.multiplier δ z
  have hsum : HasSum (fun i => fiveQuadratic (v₀ (D.sourceParam i)) (v₁ (D.sourceParam i))
      (v₂ (D.sourceParam i)) (v₃ (D.sourceParam i)) (v₄ (D.sourceParam i)) (z.val i) (φ.val i))
      (D.sourceForm v₀ (z-φ)+D.sourceForm v₁ (z+φ)+D.sourceForm v₂ (z+φ)+
        D.sourceForm v₃ (z-φ)+D.sourceForm v₄ φ) := by
    have h := (((((D.source_summable v₀ (z-φ)).hasSum.add
      (D.source_summable v₁ (z+φ)).hasSum).add
      (D.source_summable v₂ (z+φ)).hasSum).add
      (D.source_summable v₃ (z-φ)).hasSum).add
      (D.source_summable v₄ φ).hasSum)
    simpa only [sourceForm, fiveQuadratic, Submodule.coe_sub, Submodule.coe_add,
      Pi.sub_apply, Pi.add_apply] using h
  have heq : D.sourceForm v₀ (z-φ)+D.sourceForm v₁ (z+φ)+D.sourceForm v₂ (z+φ)+
      D.sourceForm v₃ (z-φ)+D.sourceForm v₄ φ = D.sourceForm F z := by
    apply hsum.unique
    convert (D.source_summable F z).hasSum using 1
    · funext i
      exact hmin (D.sourceParam i) (z.val i)
    · rfl
  calc
    ∑ j ∈ s, F (D.targetParam j)*Complex.normSq (D.map z j) ≤
        ∑ j ∈ s, fiveQuadratic (v₀ (D.targetParam j)) (v₁ (D.targetParam j))
          (v₂ (D.targetParam j)) (v₃ (D.targetParam j)) (v₄ (D.targetParam j))
            (D.map z j) (D.map φ j) :=
      Finset.sum_le_sum (fun j _ => hlower _ _ _)
    _ = (∑ j ∈ s, v₀ (D.targetParam j)*Complex.normSq (D.map (z-φ) j))+
        (∑ j ∈ s, v₁ (D.targetParam j)*Complex.normSq (D.map (z+φ) j))+
        (∑ j ∈ s, v₂ (D.targetParam j)*Complex.normSq (D.map (z+φ) j))+
        (∑ j ∈ s, v₃ (D.targetParam j)*Complex.normSq (D.map (z-φ) j))+
        (∑ j ∈ s, v₄ (D.targetParam j)*Complex.normSq (D.map φ j)) := by
      simp only [fiveQuadratic, Finset.sum_add_distrib, map_sub, map_add, Pi.sub_apply, Pi.add_apply]
    _ ≤ D.sourceForm v₀ (z-φ)+D.sourceForm v₁ (z+φ)+D.sourceForm v₂ (z+φ)+
        D.sourceForm v₃ (z-φ)+D.sourceForm v₄ φ :=
      add_le_add (add_le_add (add_le_add (add_le_add (h₀ (z-φ) s) (h₁ (z+φ) s))
        (h₂ (z+φ) s)) (h₃ (z-φ) s)) (h₄ φ s)
    _ = D.sourceForm F z := heq

end DiagonalForms.System

end

end

end OAI
