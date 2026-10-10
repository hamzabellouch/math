import OAI.Analysis.SignedDisk.DyadicHats1

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
open Finset
open scoped ENNReal NNReal RealInnerProductSpace
open scoped ContDiff
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset

noncomputable section

namespace SignedDisk

namespace DyadicHats

section
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

end

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

end SignedDisk

end

end OAI
