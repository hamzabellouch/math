import OAI.Analysis.SignedDisk.DiskMaximalTools1

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open scoped Topology RealInnerProductSpace ContDiff
open scoped Topology Interval NNReal
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open scoped ENNReal NNReal

noncomputable section

namespace SignedDisk

namespace ScalarCancellation
open Finset
variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Fintype ι]

lemma scalar_defect_sum (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    (hcol : ∀ k s, ∑ q, w k q s = 1) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (k : ℕ) :
    (∑ q, ∫ x, |errors μ w f (k+1) q x| ∂μ) ≤
      (∑ q, |∫ x, refined w f k q x ∂μ|)-(∑ q, |∫ x, refined w f (k+1) q x ∂μ|) := by
  calc
    _ ≤ ∑ q, ((∑ s, w k q s*|∫ x, refined w f k s x ∂μ|)-|∫ x, refined w f (k+1) q x ∂μ|) :=
      sum_le_sum (fun q _ => errors_cost w hw hf k q)
    _ = _ := by
      rw [sum_sub_distrib,sum_comm]
      congr 1
      apply sum_congr rfl
      intro s _
      rw [← sum_mul,hcol,one_mul]

/-- The total cancellation cost of all levels is bounded by the actual scalar
input mass, independently of the number of refinement levels. -/
theorem errors_total_cost (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    (hcol : ∀ k s, ∑ q, w k q s = 1) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q, ∫ x, |errors μ w f k q x| ∂μ) +
      (∑ q, |∫ x, refined w f n q x ∂μ|) ≤ ∑ q, ∫ x, |f q x| ∂μ := by
  induction n with
  | zero =>
    simp only [Nat.zero_add,range_one,sum_singleton,errors_terminal_cost w hf,refined,sum_sub_distrib]
    exact (sub_add_cancel _ _).le
  | succ n ih =>
    rw [sum_range_succ]
    have hstep := scalar_defect_sum w hw hcol hf n
    linarith

lemma errors_total_cost_le (w : ℕ → ι → ι → ℝ) (hw : ∀ k q s, 0 ≤ w k q s)
    (hcol : ∀ k s, ∑ q, w k q s = 1) {f : ι → α → ℝ}
    (hf : ∀ q, Integrable (f q) μ) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q, ∫ x, |errors μ w f k q x| ∂μ) ≤ ∑ q, ∫ x, |f q x| ∂μ := by
  have h := errors_total_cost w hw hcol hf n
  have hx : 0 ≤ ∑ q, |∫ x, refined w f n q x ∂μ| := sum_nonneg (fun _ _ => abs_nonneg _)
  linarith

/-- Exact expansion in a coherent family of refinement coefficients. The
finite zero-mass pieces are the explicitly constructed `errors`, not merely
scalar mass certificates. -/
theorem telescoped_decomposition [DecidableEq ι] (w : ℕ → ι → ι → ℝ) (f : ι → α → ℝ)
    (Λ : ℕ → ℕ → ι → ι → ℝ)
    (hdiag : ∀ k q s, Λ k k q s = if q = s then 1 else 0)
    (hstep : ∀ k j q s, j ≤ k → Λ (k+1) j q s = ∑ a, w k q a*Λ k j a s)
    (k : ℕ) (q : ι) (x : α) :
    refined w f k q x = roots μ w f k q x +
      ∑ j ∈ range (k+1), ∑ s, Λ k j q s*errors μ w f j s x := by
  classical
  induction k generalizing q with
  | zero =>
    simp only [Nat.zero_add,Finset.range_one,sum_singleton,hdiag,ite_mul,one_mul,zero_mul]
    rw [sum_ite_eq univ q]
    simp only [Finset.mem_univ,ite_true,errors,refined]
    ring
  | succ k ih =>
    rw [sum_range_succ]
    have hlast : (∑ s, Λ (k+1) (k+1) q s*errors μ w f (k+1) s x) = errors μ w f (k+1) q x := by
      simp only [hdiag,ite_mul,one_mul,zero_mul]
      simp
    rw [hlast,errors,refined]
    simp_rw [ih]
    simp only [mul_add,sum_add_distrib]
    have hsum : (∑ a, w k q a*(∑ j ∈ range (k+1), ∑ s, Λ k j a s*errors μ w f j s x)) =
        ∑ j ∈ range (k+1), ∑ s, Λ (k+1) j q s*errors μ w f j s x := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      rw [hstep k j q s (Nat.le_of_lt_succ (mem_range.mp hj)),sum_mul]
      apply sum_congr rfl
      intro a _
      ring
    rw [hsum]
    ring

end ScalarCancellation

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace DyadicHats

def tent (x : ℝ) : ℝ := max (1-|x|) 0

lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_right _ _
lemma tent_le_one (x : ℝ) : tent x ≤ 1 := max_le (by linarith [abs_nonneg x]) (by norm_num)
lemma tent_pos_iff (x : ℝ) : 0 < tent x ↔ |x| < 1 := by
  unfold tent
  rw [lt_max_iff]
  constructor
  · intro h; rcases h with h|h <;> linarith
  · intro h; exact Or.inl (by linarith)
lemma tent_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  exact max_eq_right (by linarith)
lemma tent_of_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : tent x = 1-x := by
  simp only [tent, abs_of_nonneg hx, max_eq_left (sub_nonneg.mpr hx1)]
lemma tent_of_nonpos {x : ℝ} (hx : x ≤ 0) (hx1 : -1 ≤ x) : tent x = 1+x := by
  rw [tent,abs_of_nonpos hx,max_eq_left (by linarith)]
  ring
lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp only [tent,abs_neg]

lemma lipschitz_tent : LipschitzWith 1 tent := by
  have hn : LipschitzWith 1 (fun x : ℝ => |x|) := by
    change LipschitzWith 1 (norm : ℝ → ℝ)
    exact lipschitzWith_one_norm
  have h : LipschitzWith 1 (fun x : ℝ => 1-|x|) := by
    simpa only [zero_add] using (LipschitzWith.const (1:ℝ)).sub hn
  change LipschitzWith 1 (fun x : ℝ => max (1-|x|) 0)
  simpa only [max_eq_left (by norm_num : (0:ℝ≥0) ≤ 1)] using h.max (LipschitzWith.const (0:ℝ))

theorem tent_refine (x : ℝ) :
    tent x = (1/2)*tent (2*x+1)+tent (2*x)+(1/2)*tent (2*x-1) := by
  wlog hx : 0 ≤ x generalizing x
  · have h := this (-x) (by linarith)
    rw [tent_neg] at h
    have heq1 : 2*(-x)+1 = -(2*x-1) := by ring
    have heq2 : 2*(-x) = -(2*x) := by ring
    have heq3 : 2*(-x)-1 = -(2*x+1) := by ring
    rw [heq1,heq3,heq2,tent_neg,tent_neg,tent_neg] at h
    linarith
  have hplus : tent (2*x+1) = 0 := tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [hplus,mul_zero,zero_add]
  by_cases hx1 : x ≤ 1/2
  · rw [tent_of_nonneg hx (by linarith),tent_of_nonneg (by linarith) (by linarith),
      tent_of_nonpos (by linarith) (by linarith)]
    ring
  · by_cases hx2 : x ≤ 1
    · rw [tent_of_nonneg hx hx2,tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith),
        tent_of_nonneg (by linarith) (by linarith)]
      ring
    · rw [tent_eq_zero_of_one_le (by rw [abs_of_nonneg hx]; linarith),
        tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith),
        tent_eq_zero_of_one_le (by rw [abs_of_nonneg (by linarith)]; linarith)]
      ring

lemma tent_floor (x : ℝ) : tent (x-⌊x⌋) = 1-(x-⌊x⌋) :=
  tent_of_nonneg (sub_nonneg.mpr (Int.floor_le x)) (by linarith [Int.lt_floor_add_one x])
lemma tent_floor_succ (x : ℝ) : tent (x-(⌊x⌋+1)) = x-⌊x⌋ := by
  rw [tent_of_nonpos (by linarith [Int.lt_floor_add_one x]) (by linarith [Int.floor_le x])]
  ring
lemma tent_floor_partition (x : ℝ) : tent (x-⌊x⌋)+tent (x-(⌊x⌋+1)) = 1 := by
  rw [tent_floor,tent_floor_succ]; ring

lemma tent_eq_zero_of_ne_floor {x : ℝ} {j : ℤ}
    (hj : j ≠ ⌊x⌋) (hj' : j ≠ ⌊x⌋+1) : tent (x-j) = 0 := by
  apply tent_eq_zero_of_one_le
  have hcases : j < ⌊x⌋ ∨ ⌊x⌋+1 < j := by omega
  rcases hcases with h|h
  · have hjle : (j:ℝ)+1 ≤ ⌊x⌋ := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith [Int.floor_le x])]
    linarith [Int.floor_le x]
  · have hjle : (⌊x⌋:ℝ)+2 ≤ j := by exact_mod_cast (show ⌊x⌋+2 ≤ j by omega)
    rw [abs_of_nonpos (by linarith [Int.lt_floor_add_one x])]
    linarith [Int.lt_floor_add_one x]

lemma summable_tent (x : ℝ) : Summable (fun j : ℤ => tent (x-j)) := by
  apply summable_of_ne_finset_zero (s := {⌊x⌋,⌊x⌋+1})
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  exact tent_eq_zero_of_ne_floor hj.1 hj.2

/-- Partition of unity on the complete integer grid, including grid boundaries. -/
theorem tsum_tent (x : ℝ) : (∑' j : ℤ, tent (x-j)) = 1 := by
  rw [tsum_eq_sum (s := {⌊x⌋,⌊x⌋+1}) (fun j hj => by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    exact tent_eq_zero_of_ne_floor hj.1 hj.2)]
  rw [Finset.sum_insert (by simp),Finset.sum_singleton]
  simpa only [Int.cast_add,Int.cast_one] using tent_floor_partition x

/-- Actual Euclidean-plane product hats at a positive physical scale. -/
def hat (r : ℝ) (p : ℤ × ℤ) (x : ℂ) : ℝ :=
  tent (x.re/r-p.1)*tent (x.im/r-p.2)
lemma hat_nonneg (r : ℝ) (p : ℤ × ℤ) (x : ℂ) : 0 ≤ hat r p x :=
  mul_nonneg (tent_nonneg _) (tent_nonneg _)
lemma hat_le_one (r : ℝ) (p : ℤ × ℤ) (x : ℂ) : hat r p x ≤ 1 := by
  calc
    _ ≤ 1*1 := mul_le_mul (tent_le_one _) (tent_le_one _) (tent_nonneg _) (by norm_num)
    _ = _ := one_mul _
lemma continuous_hat (r : ℝ) (p : ℤ × ℤ) : Continuous (hat r p) := by
  unfold hat
  exact (lipschitz_tent.continuous.comp (by fun_prop)).mul
    (lipschitz_tent.continuous.comp (by fun_prop))

lemma summable_hat (r : ℝ) (x : ℂ) : Summable (fun p : ℤ × ℤ => hat r p x) :=
  (summable_tent (x.re/r)).mul_of_nonneg (summable_tent (x.im/r))
    (fun _ => tent_nonneg _) (fun _ => tent_nonneg _)

theorem tsum_hat (r : ℝ) (x : ℂ) : (∑' p : ℤ × ℤ, hat r p x) = 1 := by
  rw [Summable.tsum_prod (summable_hat r x)]
  simp_rw [hat,tsum_mul_left,tsum_tent,mul_one]
  exact tsum_tent _

/-- One-dimensional refinement written with the actual interpolation weights. -/
lemma tent_half_integer {j : ℤ} (hj : j ∉ Finset.Icc (-1) 1) : tent ((j:ℝ)/2) = 0 := by
  apply tent_eq_zero_of_one_le
  simp only [Finset.mem_Icc,not_and_or,not_le] at hj
  rcases hj with hj|hj
  · have h : (j:ℝ) ≤ -2 := by exact_mod_cast (show j ≤ -2 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h : (2:ℝ) ≤ j := by exact_mod_cast (show 2 ≤ j by omega)
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma tent_half_refine (x : ℝ) :
    tent (x/2) = ∑ j ∈ Finset.Icc (-1:ℤ) 1, tent ((j:ℝ)/2)*tent (x-j) := by
  rw [show Finset.Icc (-1:ℤ) 1 = {-1,0,1} by decide]
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,
    Finset.mem_singleton,Int.reduceEq,or_self,not_false_eq_true,
    Int.cast_neg,Int.cast_one,Int.cast_zero,sub_neg_eq_add,sub_zero]
  norm_num [tent] at ⊢
  have h := tent_refine (x/2)
  unfold tent at h
  convert h using 1
  ring_nf

lemma tent_half_tsum_refine (x : ℝ) (p : ℤ) :
    tent (x/2-p) = ∑' j : ℤ, tent ((j:ℝ)/2-p)*tent (x-j) := by
  have heq : (∑' j : ℤ, tent ((j:ℝ)/2-p)*tent (x-j)) =
      ∑' j : ℤ, tent ((j:ℝ)/2)*tent ((x-2*p)-j) := by
    rw [← (Equiv.addRight (2*p)).tsum_eq]
    apply tsum_congr
    intro j
    simp only [Equiv.coe_addRight,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    congr 2 <;> ring
  rw [heq,tsum_eq_sum (s := Finset.Icc (-1:ℤ) 1)]
  · convert tent_half_refine (x-2*p) using 1
    congr 1
    ring
  · intro j hj
    rw [tent_half_integer hj,zero_mul]

lemma summable_tent_weight (x : ℝ) (a : ℤ → ℝ) :
    Summable (fun j : ℤ => a j*tent (x-j)) := by
  apply summable_of_ne_finset_zero (s := {⌊x⌋,⌊x⌋+1})
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
  rw [tent_eq_zero_of_ne_floor hj.1 hj.2,mul_zero]

/-- Positive interpolation coefficients, indexed by coarse and fine grid indices. -/
def step (p q : ℤ × ℤ) : ℝ :=
  tent ((q.1:ℝ)/2-p.1)*tent ((q.2:ℝ)/2-p.2)
lemma step_nonneg (p q : ℤ × ℤ) : 0 ≤ step p q :=
  mul_nonneg (tent_nonneg _) (tent_nonneg _)
lemma step_column (q : ℤ × ℤ) : (∑' p : ℤ × ℤ, step p q) = 1 := by
  calc
    _ = ∑' p, hat 1 p (((q.1:ℝ)/2 : ℂ)+((q.2:ℝ)/2 : ℂ)*Complex.I) := by
      apply tsum_congr
      intro p
      simp [step,hat]
    _ = 1 := tsum_hat _ _

lemma summable_step_hat (p : ℤ × ℤ) (r : ℝ) (x : ℂ) :
    Summable (fun q : ℤ × ℤ => step p q*hat r q x) := by
  have h1 := summable_tent_weight (x.re/r) (fun j => tent ((j:ℝ)/2-p.1))
  have h2 := summable_tent_weight (x.im/r) (fun j => tent ((j:ℝ)/2-p.2))
  convert h1.mul_of_nonneg h2 (fun j => mul_nonneg (tent_nonneg _) (tent_nonneg _))
    (fun j => mul_nonneg (tent_nonneg _) (tent_nonneg _)) using 1
  funext q
  simp only [step,hat]
  ring

/-- Exact planar hat refinement; no grid truncation is hidden in the identity. -/
theorem hat_refine (r : ℝ) (p : ℤ × ℤ) (x : ℂ) :
    hat (2*r) p x = ∑' q : ℤ × ℤ, step p q*hat r q x := by
  rw [Summable.tsum_prod (summable_step_hat p r x)]
  have heq : (fun j : ℤ => ∑' k : ℤ,
      step p (j,k)*hat r (j,k) x) = fun j : ℤ =>
      (tent ((j:ℝ)/2-p.1)*tent (x.re/r-j))*
        ∑' k : ℤ, tent ((k:ℝ)/2-p.2)*tent (x.im/r-k) := by
    funext j
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    simp only [step,hat]
    ring
  rw [heq,tsum_mul_right,← tent_half_tsum_refine,← tent_half_tsum_refine]
  unfold hat
  congr 2 <;> ring

end DyadicHats

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace PlanePotential

lemma dim_complex : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

lemma volume_real_unit_ball : volume.real (ball (0:ℂ) 1) = Real.pi := by
  rw [measureReal_def,Complex.volume_ball]
  simp

lemma integral_radial (f : ℝ → ℝ) :
    (∫ x : ℂ, f ‖x‖) = 2*Real.pi * ∫ r in Ioi (0:ℝ), r*f r := by
  rw [integral_fun_norm_addHaar volume f]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul,volume_real_unit_ball,
    nsmul_eq_mul,Nat.cast_ofNat]
  ring

lemma integrable_radial_iff (f : ℝ → ℝ) :
    Integrable (fun x : ℂ => f ‖x‖) ↔ IntegrableOn (fun r => r*f r) (Ioi (0:ℝ)) := by
  simpa only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul] using
    integrable_fun_norm_addHaar (E := ℂ) volume (f := f)

lemma radial_near_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t * (Iio r).indicator (fun u : ℝ => u^a) t = (Ioo 0 r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : t < r
  · simp only [indicator_of_mem (show t ∈ Iio r from htr),indicator_of_mem (show t ∈ Ioo 0 r from ⟨ht,htr⟩)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Iio r from htr),indicator_of_notMem (show t ∉ Ioo 0 r by simp [htr]),mul_zero]

lemma integrable_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun t : ℝ => t^a)]
  simp only [dim_complex,show (2:ℕ)-1=1 by rfl,pow_one,smul_eq_mul]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioo 0 r) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mpr (by linarith)
  apply hi.congr_fun _ measurableSet_Ioo
  intro t ht
  change t^(a+1) = t*t^a
  rw [Real.rpow_add ht.1,Real.rpow_one,mul_comm]

/-- Exact planar singular-kernel integral; the center point is not excluded by
an unproved integrability convention. -/
theorem integral_norm_rpow_near {a r : ℝ} (ha : -2 < a) (hr : 0 < r) :
    (∫ x in ball (0:ℂ) r, ‖x‖^a) = 2*Real.pi * (r^(a+2)/(a+2)) := by
  have heq : (ball (0:ℂ) r).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Iio r).indicator (fun t : ℝ => t^a) ‖x‖ := by
    funext x
    by_cases hx : ‖x‖ < r <;> simp [indicator,hx]
  rw [← integral_indicator measurableSet_ball,heq,integral_radial]
  have hinner : (∫ t in Ioi (0:ℝ), t*(Iio r).indicator (fun u : ℝ => u^a) t) =
      ∫ t in Ioo 0 r, t^(a+1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_near_identity a r ht)]
    rw [integral_indicator measurableSet_Ioo,Measure.restrict_restrict measurableSet_Ioo,
      inter_eq_left.mpr (Ioo_subset_Ioi_self)]
  rw [hinner,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr.le,
    integral_rpow (Or.inl (by linarith : -1 < a+1))]
  rw [show a+1+1=a+2 by ring,Real.zero_rpow (by linarith : a+2 ≠ 0),sub_zero]

lemma radial_far_identity (a r : ℝ) {t : ℝ} (ht : 0 < t) :
    t*(Ioi r).indicator (fun u : ℝ => u^a) t = (Ioi r).indicator (fun u : ℝ => u^(a+1)) t := by
  by_cases htr : r < t
  · simp only [indicator_of_mem (show t ∈ Ioi r from htr)]
    rw [Real.rpow_add ht,Real.rpow_one,mul_comm]
  · simp only [indicator_of_notMem (show t ∉ Ioi r from htr),mul_zero]

lemma integrable_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    IntegrableOn (fun x : ℂ => ‖x‖^a) {x | r < ‖x‖} := by
  rw [← integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
  have heq : ({x : ℂ | r < ‖x‖}).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Ioi r).indicator (fun t : ℝ => t^a) ‖x‖ := by rfl
  rw [heq,integrable_radial_iff]
  have hi : IntegrableOn (fun t : ℝ => t^(a+1)) (Ioi r) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hr
  have hi' : Integrable ((Ioi r).indicator (fun t : ℝ => t^(a+1))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hi
  apply hi'.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  exact (radial_far_identity a r ht).symm

theorem integral_norm_rpow_far {a r : ℝ} (ha : a < -2) (hr : 0 < r) :
    (∫ x : ℂ in {x | r < ‖x‖}, ‖x‖^a) = 2*Real.pi * (-r^(a+2)/(a+2)) := by
  have heq : ({x : ℂ | r < ‖x‖}).indicator (fun x => ‖x‖^a) =
      fun x : ℂ => (Ioi r).indicator (fun t : ℝ => t^a) ‖x‖ := by rfl
  rw [← integral_indicator (measurableSet_lt measurable_const measurable_norm),heq,integral_radial]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => radial_far_identity a r ht)]
  rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hr.le),integral_Ioi_rpow_of_lt (by linarith : a+1 < -1) hr]
  congr 2
  rw [show a+1+1 = a+2 by ring]
  ring

end PlanePotential

end SignedDisk

end

end OAI
