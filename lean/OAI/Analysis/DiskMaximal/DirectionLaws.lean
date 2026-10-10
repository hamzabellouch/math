import OAI.Analysis.DiskMaximal.Refinement

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology

noncomputable section

namespace DyadicHats
open scoped BigOperators

lemma step_support {r : ℝ} (_hr : 0 < r) {p q : ℤ × ℤ} (hw : step p q ≠ 0) :
    Function.support (hat r q) ⊆ Function.support (hat (2*r) p) := by
  have hq : q ∈ children p := by
    by_contra hn
    exact hw (step_zero_of_not_child hn)
  intro x hx
  have hpos : 0 < step p q*hat r q x := mul_pos
    (lt_of_le_of_ne (step_nonneg p q) (Ne.symm hw))
    (lt_of_le_of_ne (hat_nonneg r q x) (Ne.symm hx))
  have hle : step p q*hat r q x ≤ hat (2*r) p x := by
    rw [hat_refine_finite]
    exact Finset.single_le_sum (fun s _ => mul_nonneg (step_nonneg p s) (hat_nonneg r s x)) hq
  exact ne_of_gt (hpos.trans_le hle)

variable {N : ℕ}
def weights (N : ℕ) : ℕ → Grid N → Grid N → ℝ := fun _ p q => step p q
def pieces (N : ℕ) (r : ℝ) (h : ℂ → ℝ) : Grid N → ℂ → ℝ := fun q x => hat r q x*h x

def densityRoot (N : ℕ) (r : ℝ) (h : ℂ → ℝ) :=
  ScalarCancellation.roots volume (weights N) (pieces N r h)
def densityError (N : ℕ) (r : ℝ) (h : ℂ → ℝ) :=
  ScalarCancellation.errors volume (weights N) (pieces N r h)

lemma pieces_integrable {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (q : Grid N) :
    Integrable (pieces N r h q) := integrable_hat_mul hh r q

lemma refined_eq_density {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) (x : ℂ) :
    ScalarCancellation.refined (weights N) (pieces N r h) k q x = hat (scale r k) q x*h x := by
  induction k generalizing q with
  | zero => simp only [ScalarCancellation.refined,pieces,scale,pow_zero,one_mul]
  | succ k ih =>
    simp only [ScalarCancellation.refined,weights,ih,scale_succ]
    exact (density_refine_grid (scale_pos hr k) (scale_index_bound hr hR hN k) hs q x).symm

lemma densityRoot_integrable {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (k : ℕ) (q : Grid N) :
    Integrable (densityRoot N r h k q) :=
  ScalarCancellation.roots_integrable _ (pieces_integrable hh r) k q
lemma densityError_integrable {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (k : ℕ) (q : Grid N) :
    Integrable (densityError N r h k q) :=
  ScalarCancellation.errors_integrable _ (pieces_integrable hh r) k q
lemma densityError_zero_mass {h : ℂ → ℝ} (hh : Integrable h) (r : ℝ) (k : ℕ) (q : Grid N) :
    (∫ x, densityError N r h k q x) = 0 :=
  ScalarCancellation.errors_zero_mass _ (pieces_integrable hh r) k q

lemma densityRoot_mass {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, densityRoot N r h k q x) = ∫ x, hat (scale r k) q x*h x := by
  have he := ScalarCancellation.roots_mass (weights N) (pieces_integrable hh r) k q
  simpa only [densityRoot,refined_eq_density hr hR hN hs] using he

lemma densityRoot_abs_mass {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityRoot N r h k q x|) = |∫ x, hat (scale r k) q x*h x| := by
  have he := ScalarCancellation.roots_abs_mass (weights N) (pieces_integrable hh r) k q
  simpa only [densityRoot,refined_eq_density hr hR hN hs] using he

lemma density_support {r : ℝ} (hr : 0 < r) {h : ℂ → ℝ} (hh : Integrable h)
    (k : ℕ) (q : Grid N) (x : ℂ) (hx : hat (scale r k) q x = 0) :
    densityRoot N r h k q x = 0 ∧ densityError N r h k q x = 0 := by
  apply ScalarCancellation.roots_errors_support (weights N) (pieces_integrable hh r)
    (fun k q => Function.support (hat (scale r k) q)) ?_ ?_ k q x (by simpa using hx)
  · intro q y hy
    have hz : hat r q y = 0 := by simpa [scale] using hy
    simp only [pieces,hz,zero_mul]
  · intro k p q hw
    rw [scale_succ]
    exact step_support (scale_pos hr k) hw

def densityDefect (N : ℕ) (r : ℝ) (h : ℂ → ℝ) : ℕ → Grid N → ℝ
  | 0,q => ((∫ x, hat r q x*|h x|)-|∫ x, hat r q x*h x|)/2
  | k+1,q => ((∑ s : Grid N, step q s*|∫ x, hat (scale r k) s x*h x|)-
      |∫ x, hat (scale r (k+1)) q x*h x|)/2

lemma densityError_cost {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    (∫ x, |densityError N r h k q x|) ≤ 2*densityDefect N r h k q := by
  cases k with
  | zero =>
    have he := ScalarCancellation.errors_terminal_cost (weights N) (pieces_integrable hh r) q
    simp only [pieces,abs_mul,abs_of_nonneg (hat_nonneg r q _)] at he
    rw [densityDefect]
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) 0 q x|) ≤ _
    rw [he]
    linarith
  | succ k =>
    have he := ScalarCancellation.errors_cost (weights N) (fun _ p s => step_nonneg p s)
      (pieces_integrable hh r) k q
    simp only [refined_eq_density hr hR hN hs,weights] at he
    change (∫ x, |ScalarCancellation.errors volume (weights N) (pieces N r h) (k+1) q x|) ≤ _
    rw [densityDefect]
    linarith

lemma densityError_total_cost {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ∑ q : Grid N, ∫ x, |densityError N r h k q x|) ≤ ∫ x, |h x| := by
  have he := ScalarCancellation.errors_total_cost_le (weights N) (fun _ p s => step_nonneg p s)
    (fun _ q => grid_step_column N q) (pieces_integrable hh r) n
  have hi : (∑ q : Grid N, ∫ x, |pieces N r h q x|) = ∫ x, |h x| := by
    rw [← integral_finsetSum _ (fun q _ => (pieces_integrable hh r q).abs)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [pieces,abs_mul,abs_of_nonneg (hat_nonneg r _ x)]
    apply density_partition_grid hr hN
    intro y hy
    exact hs y (fun hz => hy (by rw [hz,abs_zero]))
  exact he.trans_eq hi

end DyadicHats

namespace DyadicHats
open Finset

/-- Coherent refinement coefficients, evaluated by exact positive matrix
composition on the finite box. These are not row-stochastic transitions. -/
def coeff (N : ℕ) : ℕ → Grid N → Grid N → ℝ
  | 0,p,q => if p=q then 1 else 0
  | d+1,p,q => ∑ a : Grid N, step p a*coeff N d a q

lemma coeff_nonneg (N d : ℕ) (p q : Grid N) : 0 ≤ coeff N d p q := by
  induction d generalizing p with
  | zero => simp only [coeff]; split_ifs <;> norm_num
  | succ d ih => exact sum_nonneg fun a _ => mul_nonneg (step_nonneg p a) (ih a)

lemma coeff_column (N d : ℕ) (q : Grid N) : (∑ p : Grid N, coeff N d p q) = 1 := by
  induction d with
  | zero => simp [coeff]
  | succ d ih =>
    simp only [coeff]
    rw [Finset.sum_comm]
    simp_rw [← sum_mul,grid_step_column,one_mul]
    exact ih

/-- All lower-level error densities, with their actual coherent coefficients,
reconstruct the genuine coarse hat density exactly. -/
theorem density_decomposition {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (q : Grid N) (x : ℂ) :
    hat (scale r k) q x*h x = densityRoot N r h k q x+
      ∑ j ∈ range (k+1), ∑ s : Grid N, coeff N (k-j) q s*densityError N r h j s x := by
  rw [← refined_eq_density hr hR hN hs]
  apply ScalarCancellation.telescoped_decomposition (weights N) (pieces N r h)
    (fun k j p s => coeff N (k-j) p s)
  · intro j p s
    simp only [Nat.sub_self,coeff]
  · intro k j p s hj
    rw [show k+1-j = k-j+1 by omega,coeff]
    rfl

lemma terminal_abs_sum {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) :
    (∑ q : Grid N, ∫ x, hat r q x*|h x|) = ∫ x, |h x| := by
  rw [← integral_finsetSum (Finset.univ : Finset (Grid N)) (fun q _ => integrable_hat_mul hh.abs r q)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  apply density_partition_grid hr hN
  intro y hy
  exact hs y (fun hz => hy (by rw [hz,abs_zero]))

lemma densityDefect_sum_succ (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (k : ℕ) :
    (∑ q : Grid N, densityDefect N r h (k+1) q) =
      ((∑ q : Grid N, |∫ x, hat (scale r k) q x*h x|)-
       (∑ q : Grid N, |∫ x, hat (scale r (k+1)) q x*h x|))/2 := by
  simp only [densityDefect]
  rw [← sum_div,sum_sub_distrib]
  congr 2
  rw [Finset.sum_comm]
  simp_rw [← sum_mul,grid_step_column,one_mul]

/-- Exact telescoping of the literal scalar defects, including the finest
terminal split. No depth-dependent or terminal remainder is discarded. -/
theorem densityDefect_budget_eq {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, densityDefect N r h k q) =
      ((∫ x, |h x|)-(∑ q : Grid N, |∫ x, hat (scale r n) q x*h x|))/2 := by
  induction n with
  | zero =>
    simp only [Nat.zero_add,range_one,sum_singleton,densityDefect,
      scale,pow_zero,one_mul]
    rw [← sum_div,sum_sub_distrib]
    rw [terminal_abs_sum hr hN hh hs]
  | succ n ih =>
    rw [sum_range_succ,ih,densityDefect_sum_succ]
    ring

lemma densityDefect_nonneg {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N) :
    0 ≤ densityDefect N r h k q := by
  have he := densityError_cost hr hR hN hh hs k q
  have hn : 0 ≤ ∫ x, |densityError N r h k q x| := integral_nonneg (fun x => abs_nonneg _)
  linarith

lemma densityDefect_budget {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, densityDefect N r h k q) ≤ (∫ x, |h x|)/2 := by
  rw [densityDefect_budget_eq hr hN hh hs]
  have he : 0 ≤ ∑ q : Grid N, |∫ x, hat (scale r n) q x*h x| := sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-- The common scalar price assigned to a root. The geometric discount is
applied at the actual birth scale of each zero-mass error. -/
def scalarPrice (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (ρ : ℝ) (k : ℕ) (q : Grid N) : ℝ :=
  ∑ j ∈ range (k+1), ρ^(k-j)*∑ s : Grid N, coeff N (k-j) q s*densityDefect N r h j s

lemma scalarPrice_sum (N : ℕ) (r : ℝ) (h : ℂ → ℝ) (ρ : ℝ) (k : ℕ) :
    (∑ q : Grid N, scalarPrice N r h ρ k q) =
      ∑ j ∈ range (k+1), ρ^(k-j)*∑ s : Grid N, densityDefect N r h j s := by
  simp only [scalarPrice]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← mul_sum,Finset.sum_comm]
  congr 1
  simp_rw [← sum_mul,coeff_column,one_mul]

end DyadicHats

namespace DyadicHats
open Finset

lemma discount_recurrence (ρ : ℝ) (a : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ range (k+2), ρ^(k+1-j)*a j) =
      a (k+1)+ρ*(∑ j ∈ range (k+1), ρ^(k-j)*a j) := by
  rw [sum_range_succ]
  simp only [Nat.sub_self,pow_zero,one_mul,mul_sum]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [show k+1-j = (k-j)+1 by have := mem_range.mp hj; omega,pow_succ]
  ring

lemma triangle_discount_bound {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ j ∈ range (k+1), ρ^(k-j)*a j) ≤
      (1-ρ)⁻¹*∑ j ∈ range (n+1), a j := by
  let b : ℕ → ℝ := fun k => ∑ j ∈ range (k+1), ρ^(k-j)*a j
  have hb : ∀ k, 0 ≤ b k := fun k => sum_nonneg fun j _ => mul_nonneg (pow_nonneg hρ _) (ha j)
  have hi : ∀ n, (1-ρ)*(∑ k ∈ range (n+1), b k) =
      (∑ j ∈ range (n+1), a j)-ρ*b n := by
    intro n
    induction n with
    | zero => simp [b]; ring
    | succ n ih =>
      rw [sum_range_succ (f := b) (n := n+1),sum_range_succ (f := a) (n := n+1),mul_add,ih]
      have he : b (n+1) = a (n+1)+ρ*b n := discount_recurrence ρ a n
      rw [he]
      ring
  have hle : (1-ρ)*(∑ k ∈ range (n+1), b k) ≤ ∑ j ∈ range (n+1), a j := by
    rw [hi]
    exact sub_le_self _ (mul_nonneg hρ (hb n))
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sub_pos.mpr hρ1)).mpr (by rwa [mul_comm])

theorem scalarPrice_budget {N : ℕ} {r R ρ : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℝ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    (∑ k ∈ range (n+1), ∑ q : Grid N, scalarPrice N r h ρ k q) ≤
      (1-ρ)⁻¹*((∫ x, |h x|)/2) := by
  simp_rw [scalarPrice_sum]
  apply (triangle_discount_bound hρ hρ1
    (fun j => sum_nonneg fun q _ => densityDefect_nonneg hr hR hN hh hs j q) n).trans
  exact mul_le_mul_of_nonneg_left (densityDefect_budget hr hN hh hs n)
    (inv_nonneg.mpr (sub_nonneg.mpr hρ1.le))

end DyadicHats

namespace DyadicHats
open Finset

def activeIndices (r : ℝ) (x : ℂ) : Finset (ℤ × ℤ) :=
  ({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ).product {⌊x.im/r⌋,⌊x.im/r⌋+1}

lemma hat_zero_of_not_active (r : ℝ) (x : ℂ) {p : ℤ × ℤ} (hp : p ∉ activeIndices r x) :
    hat r p x = 0 := by
  have hp' : ¬(p.1 ∈ ({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ) ∧
      p.2 ∈ ({⌊x.im/r⌋,⌊x.im/r⌋+1} : Finset ℤ)) := fun hn => hp (mem_product.mpr hn)
  rw [not_and_or] at hp'
  rcases hp' with h|h
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [hat,tent_eq_zero_of_ne_floor h.1 h.2,zero_mul]
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    rw [hat,tent_eq_zero_of_ne_floor h.1 h.2,mul_zero]

lemma activeIndices_card (r : ℝ) (x : ℂ) : (activeIndices r x).card ≤ 4 := by
  change (({⌊x.re/r⌋,⌊x.re/r⌋+1} : Finset ℤ) ×ˢ
    ({⌊x.im/r⌋,⌊x.im/r⌋+1} : Finset ℤ)).card ≤ 4
  rw [Finset.card_product]
  exact (Nat.mul_le_mul (card_insert_le ..) (card_insert_le ..)).trans (by simp)

lemma summable_weighted_hat (r : ℝ) (x : ℂ) (f : ℤ × ℤ → ℝ) :
    Summable (fun p => hat r p x*f p) := by
  apply summable_of_ne_finset_zero (s := activeIndices r x)
  intro p hp
  rw [hat_zero_of_not_active r x hp,zero_mul]

/-- The literal locally finite tent interpolation, indexed by the whole grid. -/
def interpolate (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ) : ℝ := ∑' p, hat r p x*f p

lemma interpolate_eq_sum (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ)
    (S : Finset (ℤ × ℤ)) (hS : activeIndices r x ⊆ S) :
    interpolate r f x = ∑ p ∈ S, hat r p x*f p := by
  apply tsum_eq_sum
  intro p hp
  rw [hat_zero_of_not_active r x (fun hn => hp (hS hn)),zero_mul]

lemma interpolate_add (r : ℝ) (f g : ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => f p+g p) x = interpolate r f x+interpolate r g x := by
  simp only [interpolate,mul_add]
  exact (summable_weighted_hat r x f).tsum_add (summable_weighted_hat r x g)
lemma interpolate_sub (r : ℝ) (f g : ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => f p-g p) x = interpolate r f x-interpolate r g x := by
  simp only [interpolate,mul_sub]
  exact (summable_weighted_hat r x f).tsum_sub (summable_weighted_hat r x g)
lemma interpolate_mul_const (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ) (c : ℝ) :
    interpolate r (fun p => f p*c) x = interpolate r f x*c := by
  simp only [interpolate,← mul_assoc,tsum_mul_right]
lemma interpolate_const (r : ℝ) (x : ℂ) (c : ℝ) : interpolate r (fun _ => c) x = c := by
  rw [interpolate,tsum_mul_right,tsum_hat,one_mul]
lemma interpolate_nonneg (r : ℝ) (x : ℂ) {f : ℤ × ℤ → ℝ} (hf : ∀ p, 0 ≤ f p) :
    0 ≤ interpolate r f x := tsum_nonneg fun p => mul_nonneg (hat_nonneg r p x) (hf p)
lemma interpolate_mono (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ} (h : ∀ p, f p ≤ g p) :
    interpolate r f x ≤ interpolate r g x := by
  exact Summable.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_left (h p) (hat_nonneg r p x))
    (summable_weighted_hat r x f) (summable_weighted_hat r x g)
lemma interpolate_le_const (r : ℝ) (x : ℂ) {f : ℤ × ℤ → ℝ} {c : ℝ} (hf : ∀ p, f p ≤ c) :
    interpolate r f x ≤ c := (interpolate_mono r x hf).trans_eq (interpolate_const r x c)

lemma interpolate_finset_sum {ι : Type*} (s : Finset ι) (r : ℝ)
    (f : ι → ℤ × ℤ → ℝ) (x : ℂ) :
    interpolate r (fun p => ∑ i ∈ s, f i p) x = ∑ i ∈ s, interpolate r (f i) x := by
  simp only [interpolate,mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => summable_weighted_hat r x (f i))

/-- Only eight tents can contribute to a difference of two interpolated values.
This is the quantitative global Lipschitz bound with no grid cardinality loss. -/
theorem interpolate_lipschitz {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {f : ℤ × ℤ → ℝ} (hf : ∀ p, |f p| ≤ B) :
    LipschitzWith (Real.toNNReal (16*B/r)) (interpolate r f) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  let S := activeIndices r x ∪ activeIndices r y
  have hcard : S.card ≤ 8 := (Finset.card_union_le (activeIndices r x) (activeIndices r y)).trans
    (by have := activeIndices_card r x; have := activeIndices_card r y; omega)
  have hsum : |interpolate r f x-interpolate r f y| ≤
      (S.card:ℝ)*((2/r)*‖x-y‖*B) := by
    rw [interpolate_eq_sum r f x S subset_union_left,interpolate_eq_sum r f y S subset_union_right,
      ← sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ S, |hat r p x*f p-hat r p y*f p| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ S, (2/r)*‖x-y‖*B := by
        apply sum_le_sum
        intro p _
        rw [← sub_mul,abs_mul]
        have hb := (lipschitz_hat hr p).dist_le_mul x y
        rw [Real.dist_eq,Real.coe_toNNReal (2/r) (by positivity),dist_eq_norm] at hb
        exact mul_le_mul hb (hf p) (abs_nonneg _) (by positivity)
      _ = _ := by rw [sum_const,nsmul_eq_mul]
  rw [Real.dist_eq,Real.coe_toNNReal (16*B/r) (by positivity),dist_eq_norm]
  have hcard' : (S.card:ℝ) ≤ 8 := by exact_mod_cast hcard
  calc
    _ ≤ (8:ℝ)*((2/r)*‖x-y‖*B) := hsum.trans (mul_le_mul_of_nonneg_right hcard' (by positivity))
    _ = _ := by ring

end DyadicHats

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma delta_diff_le_one (i j k : ι) : |delta i k-delta j k| ≤ 1 := by
  exact abs_sub_le_iff.mpr ⟨by linarith [(delta i).nonneg k,law_le_one (delta i) k,(delta j).nonneg k],
    by linarith [(delta j).nonneg k,law_le_one (delta j) k,(delta i).nonneg k]⟩

/-- The actual locally finite transition row on the entire spatial grid. -/
def spatialRow (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) : Law ι where
  mass j := delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x
  nonneg j := by
    simp only [mul_sub,interpolate_sub,interpolate_mul_const]
    have h0 := interpolate_nonneg r x hp0
    have h1 := interpolate_le_const r x hp1
    have h2 := interpolate_nonneg r x (fun z => mul_nonneg (hp0 z) ((delta (target z)).nonneg j))
    have hd := (delta old).nonneg j
    nlinarith
  total := by
    rw [sum_add_distrib,(delta old).total,← interpolate_finset_sum]
    have he : (fun z => ∑ j : ι, p z*(delta (target z) j-delta old j)) = fun _ => 0 := by
      funext z
      rw [← mul_sum,sum_sub_distrib,(delta _).total,(delta _).total,sub_self,mul_zero]
    rw [he,interpolate_const,add_zero]

lemma spatialRow_formula (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι) :
    spatialRow old target p hp0 hp1 r x j =
      delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x := rfl

lemma spatialRow_component_lipschitz (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hpB : ∀ z, p z ≤ B) (j : ι) :
    LipschitzWith (Real.toNNReal (16*B/r)) (fun x => spatialRow old target p hp0 hp1 r x j) := by
  have hl := interpolate_lipschitz hr hB (f := fun z => p z*(delta (target z) j-delta old j))
    (fun z => by rw [abs_mul,abs_of_nonneg (hp0 z)]; exact
      (mul_le_mul_of_nonneg_left (delta_diff_le_one _ _ _) (hp0 z)).trans (by simpa using hpB z))
  change LipschitzWith (Real.toNNReal (16*B/r))
    (fun x => delta old j+interpolate r (fun z => p z*(delta (target z) j-delta old j)) x)
  simpa only [zero_add] using (LipschitzWith.const (delta old j)).add hl

lemma spatialRow_distance (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    (hpB : ∀ z, p z ≤ B) (x y : ℂ) :
    l1dist (spatialRow old target p hp0 hp1 r x) (spatialRow old target p hp0 hp1 r y) ≤
      (Fintype.card ι:ℝ)*(16*B/r)*‖x-y‖ := by
  unfold l1dist
  calc
    _ ≤ ∑ _j : ι, (16*B/r)*‖x-y‖ := by
      apply sum_le_sum
      intro j _
      have hl := (spatialRow_component_lipschitz old target p hp0 hp1 hr hB hpB j).dist_le_mul x y
      rw [Real.dist_eq,Real.coe_toNNReal (16*B/r) (by positivity),dist_eq_norm] at hl
      exact hl
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]

end FiniteLabels

namespace DyadicHats
open Finset Filter

lemma interpolate_congr_on (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ p, hat r p x ≠ 0 → f p = g p) : interpolate r f x = interpolate r g x := by
  apply tsum_congr
  intro p
  by_cases hp : hat r p x = 0
  · simp only [hp,zero_mul]
  · rw [h p hp]

lemma interpolate_mono_on (r : ℝ) (x : ℂ) {f g : ℤ × ℤ → ℝ}
    (h : ∀ p, hat r p x ≠ 0 → f p ≤ g p) : interpolate r f x ≤ interpolate r g x := by
  apply Summable.tsum_le_tsum _ (summable_weighted_hat r x f) (summable_weighted_hat r x g)
  intro p
  by_cases hp : hat r p x = 0
  · simp only [hp,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h p hp) (hat_nonneg r p x)

lemma hat_vertex_local {r : ℝ} (hr : 0 < r) {x q : ℂ}
    (hx : boxNorm (x-q) < 199*r) {p : ℤ × ℤ} (hp : hat r p x ≠ 0) :
    boxNorm (point r p-q) ≤ 200*r := by
  have hd := (hat_ne_zero_iff hr p x).mp hp
  have ht := boxNorm_add_le (point r p-x) (x-q)
  rw [sub_add_sub_cancel,boxNorm_sub_comm (point r p) x] at ht
  linarith

lemma continuous_boxNorm : Continuous boxNorm :=
  (Complex.continuous_re.abs).max (Complex.continuous_im.abs)

lemma local_neighborhood {r : ℝ} {q x : ℂ} (hx : boxNorm (x-q) < 199*r) :
    ∀ᶠ y in 𝓝 x, boxNorm (y-q) < 199*r := by
  exact ((continuous_boxNorm.comp (continuous_id.sub continuous_const)).continuousAt.eventually
    (eventually_lt_nhds hx))

def truncate (r : ℝ) (q : ℂ) (p : ℤ × ℤ → ℝ) (z : ℤ × ℤ) : ℝ :=
  if boxNorm (point r z-q) ≤ 200*r then p z else 0

lemma truncate_nonneg (r : ℝ) (q : ℂ) {p : ℤ × ℤ → ℝ} (hp : ∀ z, 0 ≤ p z) (z : ℤ × ℤ) :
    0 ≤ truncate r q p z := by unfold truncate; split_ifs <;> simp [hp]
lemma truncate_le {r B : ℝ} {q : ℂ} {p : ℤ × ℤ → ℝ} (hB : 0 ≤ B)
    (hp : ∀ z, boxNorm (point r z-q) ≤ 200*r → p z ≤ B) (z : ℤ × ℤ) :
    truncate r q p z ≤ B := by unfold truncate; split_ifs with h; exact hp z h; exact hB
lemma interpolate_truncate {r : ℝ} (hr : 0 < r) {q x : ℂ}
    (hx : boxNorm (x-q) < 199*r) (p : ℤ × ℤ → ℝ) :
    interpolate r (truncate r q p) x = interpolate r p x := by
  apply interpolate_congr_on
  intro z hz
  exact ite_eq_left (hat_vertex_local hr hx hz)

end DyadicHats

namespace FiniteLabels
open DyadicHats Finset Filter
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spatialRow_truncate (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r : ℝ} (hr : 0 < r) {q x : ℂ}
    (hx : boxNorm (x-q) < 199*r) (j : ι) :
    spatialRow old target (truncate r q p) (truncate_nonneg r q hp0)
      (truncate_le (by norm_num) (fun z _ => hp1 z)) r x j =
    spatialRow old target p hp0 hp1 r x j := by
  rw [spatialRow_formula,spatialRow_formula]
  congr 1
  apply interpolate_congr_on
  intro z hz
  rw [truncate,ite_eq_left (hat_vertex_local hr hx hz)]

lemma spatialRow_local_distance (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {q x y : ℂ} (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hpB : ∀ z, boxNorm (point r z-q) ≤ 200*r → p z ≤ B) :
    l1dist (spatialRow old target p hp0 hp1 r x) (spatialRow old target p hp0 hp1 r y) ≤
      (Fintype.card ι:ℝ)*(16*B/r)*‖x-y‖ := by
  have h := spatialRow_distance old target (truncate r q p) (truncate_nonneg r q hp0)
    (truncate_le (by norm_num) (fun z _ => hp1 z)) hr hB (truncate_le hB hpB) x y
  simpa only [l1dist,spatialRow_truncate old target p hp0 hp1 hr hx,
    spatialRow_truncate old target p hp0 hp1 hr hy] using h

/-- The derivative cost is bounded by the local switched mass, with a constant
fixed by the finite palette, rather than by the number of scales or vertices. -/
lemma spatialRow_local_derivative (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {q x : ℂ} (hx : boxNorm (x-q) < 199*r)
    (hpB : ∀ z, boxNorm (point r z-q) ≤ 200*r → p z ≤ B) :
    r*∑ j : ι, ‖gradient (fun y => spatialRow old target p hp0 hp1 r y j) x‖ ≤
      16*(Fintype.card ι:ℝ)*B := by
  have hb (j : ι) : ‖gradient (fun y => spatialRow old target p hp0 hp1 r y j) x‖ ≤ 16*B/r := by
    have he : (fun y => spatialRow old target (truncate r q p) (truncate_nonneg r q hp0)
        (truncate_le (by norm_num) (fun z _ => hp1 z)) r y j) =ᶠ[𝓝 x]
        (fun y => spatialRow old target p hp0 hp1 r y j) := by
      filter_upwards [local_neighborhood hx] with y hy
      exact spatialRow_truncate old target p hp0 hp1 hr hy j
    have hl := spatialRow_component_lipschitz old target (truncate r q p) (truncate_nonneg r q hp0)
      (truncate_le (by norm_num) (fun z _ => hp1 z)) hr hB (truncate_le hB hpB) j
    have hd := he.fderiv_eq (𝕜 := ℝ)
    have hn := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hl
    rw [hd,Real.coe_toNNReal (16*B/r) (by positivity)] at hn
    simpa only [gradient,(InnerProductSpace.toDual ℝ ℂ).symm.norm_map] using hn
  calc
    _ ≤ r*∑ _j : ι, 16*B/r := mul_le_mul_of_nonneg_left (sum_le_sum (fun j _ => hb j)) hr.le
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul]; field_simp

end FiniteLabels

namespace FiniteLabels

def probability (τ d : ℝ) : ℝ := min 1 ((τ⁻¹*max (d-τ) 0)^2)
def amplitude (τ d : ℝ) : ℝ := min 1 (τ⁻¹*max (d-τ) 0)

lemma probability_formula (τ d : ℝ) :
    probability τ d = min 1 (τ^(-2:ℤ)*max (d-τ) 0^2) := by
  simp only [probability,mul_pow,zpow_neg,zpow_ofNat,inv_pow]

lemma amplitude_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (d : ℝ) : 0 ≤ amplitude τ d :=
  le_min (by norm_num) (mul_nonneg (inv_nonneg.mpr hτ) (le_max_right _ _))
lemma amplitude_le_one (τ d : ℝ) : amplitude τ d ≤ 1 := min_le_left _ _
lemma probability_nonneg (τ d : ℝ) : 0 ≤ probability τ d := le_min (by norm_num) (sq_nonneg _)
lemma probability_le_one (τ d : ℝ) : probability τ d ≤ 1 := min_le_left _ _

lemma probability_eq_square {τ : ℝ} (hτ : 0 ≤ τ) (d : ℝ) :
    probability τ d = amplitude τ d^2 := by
  have hx : 0 ≤ τ⁻¹*max (d-τ) 0 := mul_nonneg (inv_nonneg.mpr hτ) (le_max_right _ _)
  unfold probability amplitude
  by_cases h : τ⁻¹*max (d-τ) 0 ≤ 1
  · rw [min_eq_right h,min_eq_right (by nlinarith)]
  · rw [min_eq_left (le_of_not_ge h),min_eq_left (by nlinarith)]
    norm_num

lemma amplitude_lipschitz {τ : ℝ} (hτ : 0 < τ) :
    LipschitzWith (Real.toNNReal τ⁻¹) (amplitude τ) := by
  have hid : LipschitzWith 1 (fun d : ℝ => d-τ) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_right,le_refl]
  have hmax : LipschitzWith 1 (fun d : ℝ => max (d-τ) 0) := by
    simpa only [max_eq_left (by norm_num : (0:ℝ≥0) ≤ 1)] using hid.max (LipschitzWith.const 0)
  have hm : LipschitzWith (Real.toNNReal τ⁻¹) (fun d : ℝ => τ⁻¹*max (d-τ) 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro d d'
    rw [Real.dist_eq,Real.dist_eq,← mul_sub,abs_mul,
      abs_of_nonneg (inv_nonneg.mpr hτ.le),Real.coe_toNNReal _ (inv_nonneg.mpr hτ.le)]
    have hl := hmax.dist_le_mul d d'
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
    exact mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hτ.le)
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  change dist (min 1 (τ⁻¹*max (x-τ) 0)) (min 1 (τ⁻¹*max (y-τ) 0)) ≤ _
  simpa only [max_eq_right (by positivity : (0:ℝ≥0) ≤ Real.toNNReal τ⁻¹)] using
    ((LipschitzWith.const (1:ℝ)).min hm).dist_le_mul x y

lemma probability_compare {τ : ℝ} (hτ : 0 < τ) (d d' : ℝ) :
    probability τ d ≤ 2*probability τ d'+2*τ⁻¹^2*|d-d'|^2 := by
  rw [probability_eq_square hτ.le,probability_eq_square hτ.le]
  have hl := (amplitude_lipschitz hτ).dist_le_mul d d'
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (inv_nonneg.mpr hτ.le)] at hl
  have hdiff : (amplitude τ d-amplitude τ d')^2 ≤ (τ⁻¹*|d-d'|)^2 := by
    nlinarith [sq_abs (amplitude τ d-amplitude τ d'),abs_nonneg (amplitude τ d-amplitude τ d'),
      mul_nonneg (inv_nonneg.mpr hτ.le) (abs_nonneg (d-d'))]
  nlinarith [sq_nonneg (amplitude τ d-2*amplitude τ d')]

lemma probability_norm_compare {E : Type*} [NormedAddCommGroup E] {τ : ℝ}
    (hτ : 0 < τ) (n θ θ' : E) :
    probability τ ‖n-θ‖ ≤ 2*probability τ ‖n-θ'‖+2*τ⁻¹^2*‖θ-θ'‖^2 := by
  apply (probability_compare hτ ‖n-θ‖ ‖n-θ'‖).trans
  have hd : |‖n-θ‖-‖n-θ'‖| ≤ ‖θ-θ'‖ := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev θ' θ] using abs_norm_sub_norm_le (n-θ) (n-θ')
  have hs : |‖n-θ‖-‖n-θ'‖|^2 ≤ ‖θ-θ'‖^2 := by
    nlinarith [abs_nonneg (‖n-θ‖-‖n-θ'‖),norm_nonneg (θ-θ')]
  have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*τ⁻¹^2 by positivity)
  linarith

lemma probability_eq_zero {τ d : ℝ} (hd : d ≤ τ) : probability τ d = 0 := by
  rw [probability,max_eq_right (sub_nonpos.mpr hd)]
  norm_num

lemma probability_lt_one_iff {τ d : ℝ} (hτ : 0 < τ) : probability τ d < 1 ↔ d < 2*τ := by
  rw [probability,min_lt_iff]
  constructor
  · intro h
    rcases h with h|h
    · exact (lt_irrefl _ h).elim
    have hm := le_max_left (d-τ) 0
    have hn : 0 ≤ τ⁻¹*max (d-τ) 0 := by positivity
    have ht : τ⁻¹*max (d-τ) 0 < 1 := by nlinarith
    rw [inv_mul_eq_div,div_lt_one hτ] at ht
    linarith
  · intro h
    right
    have hm : max (d-τ) 0 < τ := max_lt (by linarith) hτ
    have hn : 0 ≤ τ⁻¹*max (d-τ) 0 := by positivity
    have ht : τ⁻¹*max (d-τ) 0 < 1 := by rw [inv_mul_eq_div,div_lt_one hτ]; exact hm
    nlinarith

end FiniteLabels

namespace FiniteLabels
open DyadicHats

lemma interpolate_const_mul (r : ℝ) (f : ℤ × ℤ → ℝ) (x : ℂ) (c : ℝ) :
    interpolate r (fun p => c*f p) x = c*interpolate r f x := by
  simp only [mul_comm c,interpolate_mul_const]

lemma norm_sub_sq_le_four {E : Type*} [NormedAddCommGroup E] (u v w : E) {A : ℝ}
    (hu : ‖u-w‖^2 ≤ A) (hv : ‖v-w‖^2 ≤ A) : ‖u-v‖^2 ≤ 4*A := by
  have ht : ‖u-v‖ ≤ ‖u-w‖+‖v-w‖ := by
    simpa only [sub_add_sub_cancel,norm_sub_rev w v] using norm_add_le (u-w) (w-v)
  nlinarith [norm_nonneg (u-v),norm_nonneg (u-w),norm_nonneg (v-w),
    sq_nonneg (‖u-w‖-‖v-w‖)]

def switchRate (τ r : ℝ) (Θ : ℤ × ℤ → ℂ) (n x : ℂ) : ℝ :=
  interpolate r (fun z => probability τ ‖n-Θ z‖) x

lemma switchRate_nonneg (τ r : ℝ) (Θ : ℤ × ℤ → ℂ) (n x : ℂ) :
    0 ≤ switchRate τ r Θ n x := interpolate_nonneg r x (fun _ => probability_nonneg _ _)
lemma switchRate_le_one (τ r : ℝ) (Θ : ℤ × ℤ → ℂ) (n x : ℂ) :
    switchRate τ r Θ n x ≤ 1 := interpolate_le_const r x (fun _ => probability_le_one _ _)

/-- The row-rate comparison is produced from the literal quadratic probability
and the actual partition of unity, uniformly over all nearby grid vertices. -/
lemma probability_le_rate_energy {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (Θ : ℤ × ℤ → ℂ) (n θ q y : ℂ) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E)
    (z : ℤ × ℤ) (hz : boxNorm (point r z-q) ≤ 200*r) :
    probability τ ‖n-Θ z‖ ≤ 2*switchRate τ r Θ n y+8*τ⁻¹^2*E := by
  have hp (z' : ℤ × ℤ) (hz' : hat r z' y ≠ 0) :
      probability τ ‖n-Θ z‖ ≤ 2*probability τ ‖n-Θ z'‖+8*τ⁻¹^2*E := by
    have he := norm_sub_sq_le_four (Θ z) (Θ z') θ (hE z hz) (hE z' (hat_vertex_local hr hy hz'))
    have hh := probability_norm_compare hτ n (Θ z) (Θ z')
    have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2*τ⁻¹^2 by positivity)
    nlinarith
  calc
    _ = interpolate r (fun _ => probability τ ‖n-Θ z‖) y := (interpolate_const _ _ _).symm
    _ ≤ interpolate r (fun z' => 2*probability τ ‖n-Θ z'‖+8*τ⁻¹^2*E) y :=
      interpolate_mono_on r y hp
    _ = _ := by rw [interpolate_add,interpolate_const_mul,interpolate_const]; rfl

lemma switchRate_local_compare {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (Θ : ℤ × ℤ → ℂ) (n θ q x y : ℂ)
    (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E) :
    switchRate τ r Θ n x ≤ 2*switchRate τ r Θ n y+8*τ⁻¹^2*E := by
  change interpolate r _ x ≤ _
  calc
    _ ≤ interpolate r (fun _ => 2*switchRate τ r Θ n y+8*τ⁻¹^2*E) x := by
      apply interpolate_mono_on
      intro z hz
      exact probability_le_rate_energy hτ hr Θ n θ q y hy hE z (hat_vertex_local hr hx hz)
    _ = _ := interpolate_const _ _ _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def spatialSwitchRow (τ r : ℝ) (label : ι → ℂ) (Θ : ℤ × ℤ → ℂ)
    (target : ℤ × ℤ → ι) (old : ι) (x : ℂ) : Law ι :=
  spatialRow old target (fun z => probability τ ‖label old-Θ z‖)
    (fun _ => probability_nonneg _ _) (fun _ => probability_le_one _ _) r x

lemma spatialSwitchRow_local_distance {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hE0 : 0 ≤ E)
    (label : ι → ℂ) (Θ : ℤ × ℤ → ℂ) (target : ℤ × ℤ → ι) (old : ι)
    (θ q x y : ℂ) (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E) :
    l1dist (spatialSwitchRow τ r label Θ target old x) (spatialSwitchRow τ r label Θ target old y) ≤
      (Fintype.card ι:ℝ)*
        (16*(2*switchRate τ r Θ (label old) y+8*τ⁻¹^2*E)/r)*‖x-y‖ := by
  apply spatialRow_local_distance old target _ _ _ hr
    (by have h := switchRate_nonneg τ r Θ (label old) y; positivity) hx hy
  intro z hz
  exact probability_le_rate_energy hτ hr Θ (label old) θ q y hy hE z hz

lemma spatialSwitchRow_local_derivative {τ r E : ℝ} (hτ : 0 < τ) (hr : 0 < r) (hE0 : 0 ≤ E)
    (label : ι → ℂ) (Θ : ℤ × ℤ → ℂ) (target : ℤ × ℤ → ι) (old : ι)
    (θ q x y : ℂ) (hx : boxNorm (x-q) < 199*r) (hy : boxNorm (y-q) < 199*r)
    (hE : ∀ z, boxNorm (point r z-q) ≤ 200*r → ‖Θ z-θ‖^2 ≤ E) :
    r*∑ j : ι, ‖gradient (fun x => spatialSwitchRow τ r label Θ target old x j) x‖ ≤
      16*(Fintype.card ι:ℝ)*(2*switchRate τ r Θ (label old) y+8*τ⁻¹^2*E) := by
  apply spatialRow_local_derivative old target _ _ _ hr
    (by have h := switchRate_nonneg τ r Θ (label old) y; positivity) hx
  intro z hz
  exact probability_le_rate_energy hτ hr Θ (label old) θ q y hy hE z hz

end FiniteLabels

namespace DyadicHats
open Finset

lemma hat_at_point {r : ℝ} (hr : r ≠ 0) (p q : ℤ × ℤ) :
    hat r p (point r q) = if p=q then 1 else 0 := by
  have ht (a b : ℤ) : tent ((b:ℝ)-(a:ℝ)) = if a=b then 1 else 0 := by
    by_cases h : a=b
    · simp [h,tent]
    · rw [ite_eq_right h]
      apply tent_eq_zero_of_one_le
      have hi : (1:ℤ) ≤ |b-a| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
      exact_mod_cast hi
  simp only [hat,point,mul_div_cancel_left₀ _ hr,ht]
  split_ifs <;> simp_all [Prod.ext_iff]

lemma hat_vertex_bound {r : ℝ} (hr : 0 < r) {N : ℕ} {x : ℂ}
    (hx1 : |x.re| ≤ r*N) (hx2 : |x.im| ≤ r*N)
    {p : ℤ × ℤ} (hp : hat r p x ≠ 0) : p ∈ indexBox N := by
  have h := (hat_ne_zero_iff hr p x).mp hp
  have h1 := lt_of_le_of_lt (le_max_left |(x-point r p).re| |(x-point r p).im|) h
  have h2 := lt_of_le_of_lt (le_max_right |(x-point r p).re| |(x-point r p).im|) h
  simp only [Complex.sub_re,Complex.sub_im,point] at h1 h2
  have hb (t : ℝ) (j : ℤ) (ht : |t| ≤ r*N) (hj : |t-r*j| < r) :
      j ∈ Finset.Icc (-(N:ℤ)) N := by
    have ht' := abs_le.mp ht
    have hj' := abs_lt.mp hj
    have hlo : -(N:ℝ)-1 < (j:ℝ) := by nlinarith
    have hhi : (j:ℝ) < (N:ℝ)+1 := by nlinarith
    have hlo' : -(N:ℤ)-1 < j := by exact_mod_cast hlo
    have hhi' : j < (N:ℤ)+1 := by exact_mod_cast hhi
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  exact Finset.mem_product.mpr ⟨hb _ _ hx1 h1,hb _ _ hx2 h2⟩

lemma velocity_bound_on_grid {N : ℕ} {r : ℝ} (hr : 0 < r) (k : ℕ) (q : Grid N) :
    |(point r q).re| ≤ scale r k*N ∧ |(point r q).im| ≤ scale r k*N := by
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp q.property).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp q.property).2
  have hh (j : ℤ) (hj : -(N:ℤ) ≤ j ∧ j ≤ N) : |r*j| ≤ scale r k*N := by
    have hj' : |(j:ℝ)| ≤ N := abs_le.mpr ⟨by exact_mod_cast hj.1,by exact_mod_cast hj.2⟩
    rw [abs_mul,abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hj' hr.le).trans
      (mul_le_mul_of_nonneg_right (le_scale hr.le k) (Nat.cast_nonneg N))
  exact ⟨hh q.val.1 h1,hh q.val.2 h2⟩

end DyadicHats

namespace DyadicHats

lemma coeff_eq_hat {N : ℕ} {r : ℝ} (hr : 0 < r) (k : ℕ) (p q : Grid N) :
    coeff N k p q = hat (scale r k) p (point r q) := by
  induction k generalizing p with
  | zero =>
    simp only [coeff,scale,pow_zero,one_mul,hat_at_point hr.ne']
    by_cases hpq : p=q
    · rw [ite_eq_left hpq,ite_eq_left (congrArg Subtype.val hpq)]
    · rw [ite_eq_right hpq,ite_eq_right (fun h => hpq (Subtype.ext h))]
  | succ k ih =>
    rw [coeff,scale_succ,hat_refine,tsum_eq_sum (s := indexBox N)]
    · rw [← sum_coe_sort (indexBox N) (fun j => step p j*hat (scale r k) j (point r q))]
      apply sum_congr rfl
      intro j hj
      rw [ih]
    · intro j hj
      have hz : hat (scale r k) j (point r q) = 0 := by
        by_contra hn
        have hb := velocity_bound_on_grid hr k q
        exact hj (hat_vertex_bound (scale_pos hr k) hb.1 hb.2 hn)
      rw [hz,mul_zero]

lemma hat_refine_grid_at {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {x : ℂ} (hx : ‖x‖ ≤ R) (p : Grid N) :
    hat (2*r) p x = ∑ q : Grid N, step p q*hat r q x := by
  rw [hat_refine,tsum_eq_sum (s := indexBox N)]
  · exact (sum_coe_sort (indexBox N) (fun q => step p q*hat r q x)).symm
  · intro q hq
    have hz : hat r q x = 0 := by
      by_contra hn
      exact hq (mem_indexBox_of_le hr hN hx hn)
    rw [hz,mul_zero]

lemma vectorMass_grid_refine {N : ℕ} {r R : ℝ} (hr : 0 < r)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (p : Grid N) :
    vectorMass h (2*r) p = ∑ q : Grid N, step p q • vectorMass h r q := by
  let f := fun y => ∑ q : Grid N, step p q • (hat r q y • h y)
  have hf : (fun y => hat (2*r) p y • h y) = f := by
    funext y
    by_cases hy : h y=0
    · simp only [f,hy,smul_zero,sum_const_zero]
    · rw [hat_refine_grid_at hr hN (hs y hy) p,sum_smul]
      simp only [f,smul_smul]
  rw [vectorMass,hf]
  dsimp only [f]
  have hi (q : Grid N) : Integrable (fun y => step p q • (hat r q y • h y)) :=
    Integrable.smul (step p q) (integrable_hat_smul hh r q)
  rw [integral_finsetSum Finset.univ (fun q _ => hi q)]
  apply sum_congr rfl
  intro q hq
  rw [integral_smul]
  rfl

lemma vectorMass_coeff {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hs : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : Grid N) :
    vectorMass h (scale r k) p = ∑ q : Grid N, coeff N k p q • vectorMass h r q := by
  induction k generalizing p with
  | zero => simp [coeff,scale]
  | succ k ih =>
    rw [scale_succ,vectorMass_grid_refine (scale_pos hr k) (scale_index_bound hr hR hN k) hh hs]
    simp only [ih,smul_sum,smul_smul,coeff,sum_smul]
    exact Finset.sum_comm

lemma sum_scalarMass_grid_le {N : ℕ} {h : ℂ → ℂ} (hh : Integrable h) (r : ℝ) :
    (∑ q : Grid N, scalarMass h r q) ≤ ∫ y, ‖h y‖ := by
  rw [sum_coe_sort (indexBox N) (fun q => scalarMass h r q)]
  exact sum_scalarMass_le hh r (indexBox N)

end DyadicHats

namespace DyadicHats
open Finset

lemma hat_lower {r a : ℝ} (hr : 0 < r) (ha : a ≤ 1) (p : ℤ × ℤ) (x : ℂ)
    (hx : boxNorm (x-point r p) ≤ a*r) : (1-a)^2 ≤ hat r p x := by
  have h1 := (le_max_left |(x-point r p).re| |(x-point r p).im|).trans hx
  have h2 := (le_max_right |(x-point r p).re| |(x-point r p).im|).trans hx
  simp only [Complex.sub_re,Complex.sub_im,point] at h1 h2
  have hh (t : ℝ) (j : ℤ) (h : |t-r*j| ≤ a*r) : 1-a ≤ tent (t/r-j) := by
    have he : t/r-j = (t-r*j)/r := by field_simp
    rw [he,tent,abs_div,abs_of_pos hr]
    have hd : |t-r*j|/r ≤ a := (div_le_iff₀ hr).mpr h
    exact (sub_le_sub_left hd 1).trans (le_max_left _ _)
  calc
    (1-a)^2 = (1-a)*(1-a) := by ring
    _ ≤ tent (x.re/r-p.1)*tent (x.im/r-p.2) :=
      mul_le_mul (hh _ _ h1) (hh _ _ h2) (sub_nonneg.mpr ha) (tent_nonneg _)
    _ = _ := rfl

def nearParent (q : ℤ × ℤ) : ℤ × ℤ := ((q.1+2048)/4096,(q.2+2048)/4096)

lemma nearParent_int_bound (j : ℤ) : |j-4096*((j+2048)/4096)| ≤ 2048 := by
  rw [abs_le]
  omega

lemma nearParent_box {r : ℝ} (hr : 0 < r) (q : ℤ × ℤ) :
    boxNorm (point r q-point (4096*r) (nearParent q)) ≤ (1/2 : ℝ)*(4096*r) := by
  have hh (j : ℤ) : |r*j-(4096*r)*((j+2048)/4096:ℤ)| ≤ (1/2:ℝ)*(4096*r) := by
    have hi : |(j:ℝ)-4096*((j+2048)/4096:ℤ)| ≤ 2048 := by exact_mod_cast nearParent_int_bound j
    have he : r*j-(4096*r)*((j+2048)/4096:ℤ) = r*((j:ℝ)-4096*((j+2048)/4096:ℤ)) := by ring
    rw [he,abs_mul,abs_of_pos hr]
    nlinarith
  exact max_le (hh q.1) (hh q.2)

lemma nearParent_mem {N : ℕ} {q : ℤ × ℤ} (hq : q ∈ indexBox N) : nearParent q ∈ indexBox N := by
  have h1 := Finset.mem_Icc.mp (Finset.mem_product.mp hq).1
  have h2 := Finset.mem_Icc.mp (Finset.mem_product.mp hq).2
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr <;> dsimp only [nearParent] <;> constructor <;> omega

lemma nearParent_hat_lower {r : ℝ} (hr : 0 < r) (q w : ℤ × ℤ)
    (hw : boxNorm (point r w-point r q) ≤ 500*r) :
    1/4 ≤ hat (scale r 12) (nearParent q) (point r q) ∧
    9/64 ≤ hat (scale r 12) (nearParent q) (point r w) := by
  have hs : scale r 12 = 4096*r := by norm_num [scale]
  have hq := nearParent_box hr q
  have ht := boxNorm_add_le (point r w-point r q) (point r q-point (4096*r) (nearParent q))
  rw [sub_add_sub_cancel] at ht
  have hw' : boxNorm (point r w-point (4096*r) (nearParent q)) ≤ (5/8:ℝ)*(4096*r) := by
    linarith
  have h1 := hat_lower (by positivity : 0 < 4096*r) (by norm_num : (1/2:ℝ) ≤ 1) (nearParent q) (point r q) hq
  have h2 := hat_lower (by positivity : 0 < 4096*r) (by norm_num : (5/8:ℝ) ≤ 1) (nearParent q) (point r w) hw'
  rw [hs]
  norm_num at h1 h2 ⊢
  exact ⟨h1,h2⟩

lemma nearParent_fiber_card (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    (S.filter (fun q => nearParent q=p)).card ≤ 4097^2 := by
  let T := (Finset.Icc (4096*p.1-2048) (4096*p.1+2048)).product
    (Finset.Icc (4096*p.2-2048) (4096*p.2+2048))
  have hsub : S.filter (fun q => nearParent q=p) ⊆ T := by
    intro q hq
    have he := (Finset.mem_filter.mp hq).2
    have h1 := nearParent_int_bound q.1
    have h2 := nearParent_int_bound q.2
    have he1 : (q.1+2048)/4096=p.1 := congrArg Prod.fst he
    have he2 : (q.2+2048)/4096=p.2 := congrArg Prod.snd he
    rw [he1,abs_le] at h1
    rw [he2,abs_le] at h2
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,
      Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  apply (Finset.card_le_card hsub).trans
  dsimp only [T]
  change ((Finset.Icc (4096*p.1-2048) (4096*p.1+2048)) ×ˢ
    (Finset.Icc (4096*p.2-2048) (4096*p.2+2048))).card ≤ 4097^2
  rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
  have he (j : ℤ) : 4096*j+2048+1-(4096*j-2048)=4097 := by ring
  rw [he,he]
  change (4097:ℕ)*4097 ≤ 4097^2
  norm_num

end DyadicHats

end

end OAI
