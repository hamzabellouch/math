import OAI.Analysis.SignedDisk.CommonPrices1

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

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset

def energyRate (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (y : ℂ) (i : ℕ) : ℝ :=
  switchCost h r y i+energy h (r i) (q i)
lemma energyRate_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (y : ℂ) (i : ℕ) :
    0 ≤ energyRate h r q y i := add_nonneg (switchCost_nonneg h r y i) (energy_nonneg h (r i) (q i))
lemma energyRate_le_five (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (y : ℂ) (i : ℕ) :
    energyRate h r q y i ≤ 5 := by
  have h1 := switchCost_le_one h r y i
  have h2 := energy_le_four h (r i) (q i)
  dsimp [energyRate]
  linarith

/-- Spatial comparison of the actual marginal laws. No independent coupling or
pointwise uniform distribution of labels is assumed. -/
theorem marginal_spatial_distance (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ)
    (x y : ℂ) (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hx : ∀ i ≤ j, boxNorm (x-point (r i) (q i)) < 199*r i)
    (hy : ∀ i ≤ j, boxNorm (y-point (r i) (q i)) < 199*r i) :
    l1dist (marginal h r j x) (marginal h r j y) ≤
      comparisonConstant*‖x-y‖*∑ i ∈ range (j+1), energyRate h r q y i/r i := by
  induction j with
  | zero =>
    have he := initial_distance h (hr 0 le_rfl) x y
    have hc : 1 ≤ energyRate h r q y 0 := by
      dsimp [energyRate,switchCost]
      linarith [energy_nonneg h (r 0) (q 0)]
    have ht := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hc (hr 0 le_rfl).le)
      (mul_nonneg comparisonConstant_pos.le (norm_nonneg (x-y)))
    simp only [Nat.zero_add,sum_range_one,marginal]
    apply he.trans
    convert ht using 1
    ring
  | succ j ih =>
    have hd := ih (fun i hi => hr i (by omega)) (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    have hm := move_compare (marginal h r j x) (marginal h r j y)
      (row h (r (j+1)) x) (row h (r (j+1)) y)
    have hrow : (∑ n, marginal h r j y n*l1dist (row h (r (j+1)) x n) (row h (r (j+1)) y n)) ≤
        comparisonConstant*‖x-y‖/r (j+1)*energyRate h r q y (j+1) := by
      calc
        _ ≤ expect (marginal h r j y) (fun n => comparisonConstant*‖x-y‖/r (j+1)*
            (rate h (r (j+1)) y n+energy h (r (j+1)) (q (j+1)))) := by
          exact expect_mono _ (row_local_distance h (hr (j+1) le_rfl) (q (j+1)) x y
            (hx (j+1) le_rfl) (hy (j+1) le_rfl))
        _ = _ := by rw [FiniteLabels.expect_mul,FiniteLabels.expect_add,FiniteLabels.expect_const]; rfl
    change l1dist (marginal h r (j+1) x) (marginal h r (j+1) y) ≤ _ at hm
    rw [sum_range_succ,mul_add]
    have hterm : comparisonConstant*‖x-y‖/r (j+1)*energyRate h r q y (j+1) =
        comparisonConstant*‖x-y‖*(energyRate h r q y (j+1)/r (j+1)) := by ring
    rw [hterm] at hrow
    linarith

lemma switchCost_spatial (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℤ × ℤ) (x y : ℂ) (i : ℕ)
    (hr : 0 < r (i+1)) (hx : boxNorm (x-point (r (i+1)) q) < 199*r (i+1))
    (hy : boxNorm (y-point (r (i+1)) q) < 199*r (i+1)) :
    switchCost h r x (i+1) ≤ comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q)+
      l1dist (marginal h r i x) (marginal h r i y) := by
  have he := expect_compare (marginal h r i x) (marginal h r i y)
    (fun n => by rw [abs_of_nonneg (rate_nonneg h (r (i+1)) x n)]; exact rate_le_one h (r (i+1)) x n)
  have hrw := expect_mono (marginal h r i y) (rate_local h hr q x y hx hy)
  rw [FiniteLabels.expect_mul,FiniteLabels.expect_add,FiniteLabels.expect_const] at hrw
  change expect (marginal h r i y) (rate h (r (i+1)) x) ≤
    comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q) at hrw
  change expect (marginal h r i x) (rate h (r (i+1)) x) ≤ _
  linarith

lemma derivativeCost_spatial (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℤ × ℤ) (x y : ℂ) (i : ℕ)
    (hr : 0 < r (i+1)) (hx : boxNorm (x-point (r (i+1)) q) < 199*r (i+1))
    (hy : boxNorm (y-point (r (i+1)) q) < 199*r (i+1)) :
    derivativeCost h r x (i+1) ≤ comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q)+
      comparisonConstant*l1dist (marginal h r i x) (marginal h r i y) := by
  have he := expect_compare (marginal h r i x) (marginal h r i y)
    (fun n => by rw [abs_of_nonneg (rowDerivative_nonneg h hr.le x n)]; exact rowDerivative_uniform h hr x n)
  have hrw := expect_mono (marginal h r i y) (row_local_derivative h hr q x y hx hy)
  rw [FiniteLabels.expect_mul,FiniteLabels.expect_add,FiniteLabels.expect_const] at hrw
  have hcoef : 16*(Fintype.card Label:ℝ) ≤ comparisonConstant := by
    dsimp [comparisonConstant]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
  have hm := mul_le_mul_of_nonneg_right hcoef (l1dist_nonneg (marginal h r i x) (marginal h r i y))
  change derivativeCost h r x (i+1) ≤ _ at he
  change expect (marginal h r i y) (rowDerivative h (r (i+1)) x) ≤
    comparisonConstant*(switchCost h r y (i+1)+energy h (r (i+1)) q) at hrw
  linarith

end ActualLabels

namespace GeometricFilter
open Finset
/-- Causal dyadic averaging, with both the present and the complete past. -/
def filt (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => c 0
  | i+1 => c (i+1)+filt c i/2
lemma filt_nonneg {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i) (i : ℕ) : 0 ≤ filt c i := by
  induction i with
  | zero => exact hc 0
  | succ i ih => exact add_nonneg (hc _) (div_nonneg ih (by norm_num))
lemma le_filt {c : ℕ → ℝ} (hc : ∀ i, 0 ≤ c i) (i : ℕ) : c i ≤ filt c i := by
  cases i with
  | zero => exact le_rfl
  | succ i => dsimp only [filt]; linarith [filt_nonneg hc i]
lemma filt_le {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ∀ i, c i ≤ A) (i : ℕ) : filt c i ≤ 2*A := by
  induction i with
  | zero => exact (hc 0).trans (by linarith)
  | succ i ih => dsimp only [filt]; linarith [hc (i+1)]
lemma filt_mono {c d : ℕ → ℝ} (h : ∀ i, c i ≤ d i) (i : ℕ) : filt c i ≤ filt d i := by
  induction i with
  | zero => exact h 0
  | succ i ih => dsimp only [filt]; linarith [h (i+1)]
lemma filt_mul (c : ℕ → ℝ) (a : ℝ) (i : ℕ) : filt (fun j => a*c j) i = a*filt c i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [filt,ih]; ring
lemma filt_sum (c : ℕ → ℝ) (i : ℕ) :
    filt c i = ∑ j ∈ range (i+1), (1/2:ℝ)^(i-j)*c j := by
  induction i with
  | zero => simp [filt]
  | succ i ih =>
    rw [filt,ih]
    conv_rhs => rw [sum_range_succ]
    simp only [Nat.sub_self,pow_zero,one_mul]
    rw [add_comm]
    congr 1
    rw [div_eq_mul_inv,sum_mul]
    apply sum_congr rfl
    intro j hj
    have hj' : j ≤ i := by have := mem_range.mp hj; omega
    rw [show i+1-j = (i-j)+1 by omega,pow_succ]
    ring

lemma filt_tail_strong {c : ℕ → ℝ} (hc0 : ∀ i, 0 ≤ c i) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c i) ≤ 2*∑ i ∈ Ico b (m+1), c i+2*filt c b := by
  have hid : (∑ i ∈ Ico (b+1) (m+1), filt c i) =
      (∑ i ∈ Ico (b+1) (m+1), c i)+(∑ i ∈ Ico b m, filt c i)/2 := by
    rw [← sum_Ico_add' (fun i => filt c i) b m 1,
      ← sum_Ico_add' (fun i => c i) b m 1]
    simp only [filt,sum_add_distrib,sum_div]
  have hsplit := sum_eq_sum_Ico_succ_bot (f := filt c) (by omega : b < m+1)
  have hcsplit := sum_eq_sum_Ico_succ_bot (f := c) (by omega : b < m+1)
  have he : (∑ i ∈ Ico b m, filt c i) ≤ ∑ i ∈ Ico b (m+1), filt c i := by
    apply sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_right (by omega))
    intro i _ _
    exact filt_nonneg hc0 i
  rw [hsplit,hid] at he
  rw [hsplit,hid,hcsplit]
  linarith [hc0 b]

/-- The complete pre-birth history costs a fixed amount, not the birth index. -/
theorem filt_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c i) ≤ 2*∑ i ∈ Ico b (m+1), c i+4*A := by
  have h1 := filt_tail_strong hc0 hbm
  have h2 := filt_le hA hcA b
  linarith

/-- Two geometric convolutions are summable on every occupied lifetime. -/
theorem double_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt (filt c) i) ≤ 4*∑ i ∈ Ico b (m+1), c i+16*A := by
  have h1 := filt_tail hA hc0 hcA hbm
  have h2 := filt_tail (by positivity : 0 ≤ 2*A) (filt_nonneg hc0) (filt_le hA hcA) hbm
  linarith

open Finset
lemma radius_sum {r c : ℕ → ℝ} (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hstep : ∀ i < j, r i = 2*r (i+1)) :
    r j*(∑ i ∈ range (j+1), c i/r i) = filt c j := by
  induction j with
  | zero => simp only [Nat.zero_add,sum_range_one,filt]; field_simp [(hr 0 le_rfl).ne']
  | succ j ih =>
    have hs := ih (fun i hi => hr i (by omega)) (fun i hi => hstep i (by omega))
    rw [sum_range_succ,mul_add,filt]
    have he : r (j+1)*(c (j+1)/r (j+1)) = c (j+1) := by field_simp [(hr (j+1) le_rfl).ne']
    rw [he,add_comm]
    congr 1
    rw [← hs,hstep j (by omega)]
    ring
end GeometricFilter

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats Finset GeometricFilter

def spatialConstant : ℝ := 208*comparisonConstant^2
lemma spatialConstant_pos : 0 < spatialConstant := by
  dsimp [spatialConstant]
  have := comparisonConstant_pos
  positivity
lemma spatialConstant_ge : 2*comparisonConstant ≤ spatialConstant := by
  dsimp [spatialConstant]
  nlinarith [comparisonConstant_one]

lemma scaled_marginal_distance (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ)
    (x y : ℂ) (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hstep : ∀ i < j, r i = 2*r (i+1))
    (hx : ∀ i ≤ j, boxNorm (x-point (r i) (q i)) < 199*r i)
    (hy : ∀ i ≤ j, boxNorm (y-point (r i) (q i)) < 199*r i) :
    r j*l1dist (marginal h r j x) (marginal h r j y) ≤
      comparisonConstant*‖x-y‖*filt (energyRate h r q y) j := by
  have hd := mul_le_mul_of_nonneg_left (marginal_spatial_distance h r q x y j hr hx hy) (hr j le_rfl).le
  have he := radius_sum (c := energyRate h r q y) j hr hstep
  calc
    _ ≤ r j*(comparisonConstant*‖x-y‖*∑ i ∈ range (j+1), energyRate h r q y i/r i) := hd
    _ = _ := by rw [← mul_assoc,mul_comm (r j),mul_assoc,he]

/-- Actual spatial comparison at every point of the neighborhood. The gradient
versions are pointwise bounded; differentiability is only needed later for IBP. -/
theorem filtered_spatial_cost (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ)
    (x y : ℂ) (j : ℕ) (hr : ∀ i ≤ j, 0 < r i)
    (hstep : ∀ i < j, r i = 2*r (i+1))
    (hx : ∀ i ≤ j, boxNorm (x-point (r i) (q i)) < 199*r i)
    (hy : ∀ i ≤ j, boxNorm (y-point (r i) (q i)) < 199*r i)
    (hdist : ‖x-y‖ ≤ 104*r j) :
    switchCost h r x j+derivativeCost h r x j ≤
      spatialConstant*filt (energyRate h r q y) j := by
  let c := energyRate h r q y
  have hc0 : ∀ i, 0 ≤ c i := energyRate_nonneg h r q y
  have hC := comparisonConstant_one
  have hC0 := comparisonConstant_pos.le
  cases j with
  | zero =>
    have he : 1 ≤ c 0 := by dsimp [c,energyRate,switchCost]; linarith [energy_nonneg h (r 0) (q 0)]
    have ht := derivativeCost_uniform h r x 0 (hr 0 le_rfl)
    have hbound : 1+16*(Fintype.card Label:ℝ) ≤ 2*comparisonConstant := by
      dsimp [comparisonConstant]
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Label)]
    have hh := mul_le_mul_of_nonneg_left he spatialConstant_pos.le
    dsimp only [switchCost,filt]
    change _ ≤ spatialConstant*c 0
    nlinarith [spatialConstant_ge]
  | succ j =>
    have hm := scaled_marginal_distance h r q x y j
      (fun i hi => hr i (by omega)) (fun i hi => hstep i (by omega))
      (fun i hi => hx i (by omega)) (fun i hi => hy i (by omega))
    have hd : ‖x-y‖ ≤ 52*r j := by rw [hstep j (by omega)]; linarith
    have hmag := mul_le_mul_of_nonneg_right hd (mul_nonneg hC0 (filt_nonneg hc0 j))
    have hd' : l1dist (marginal h r j x) (marginal h r j y) ≤
        52*comparisonConstant*filt c j := by
      have hrj := hr j (by omega)
      change r j*l1dist (marginal h r j x) (marginal h r j y) ≤
        comparisonConstant*‖x-y‖*filt c j at hm
      nlinarith
    have hs := switchCost_spatial h r (q (j+1)) x y j (hr (j+1) le_rfl)
      (hx (j+1) le_rfl) (hy (j+1) le_rfl)
    have ht := derivativeCost_spatial h r (q (j+1)) x y j (hr (j+1) le_rfl)
      (hx (j+1) le_rfl) (hy (j+1) le_rfl)
    change switchCost h r x (j+1) ≤ comparisonConstant*c (j+1)+_ at hs
    change derivativeCost h r x (j+1) ≤ comparisonConstant*c (j+1)+_ at ht
    have hdC := mul_le_mul_of_nonneg_left hd' hC0
    have hcoef : (52*comparisonConstant+52*comparisonConstant^2)*filt c j ≤
        (104*comparisonConstant^2)*filt c j := by
      apply mul_le_mul_of_nonneg_right _ (filt_nonneg hc0 j)
      nlinarith
    have hcC := mul_le_mul_of_nonneg_right spatialConstant_ge (hc0 (j+1))
    change _ ≤ spatialConstant*filt c (j+1)
    rw [filt]
    dsimp [spatialConstant] at hcC ⊢
    nlinarith
end ActualLabels

namespace DyadicHats
lemma scale_mono {r : ℝ} (hr : 0 ≤ r) {i j : ℕ} (hij : i ≤ j) : scale r i ≤ scale r j := by
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) hr
lemma descending_step (r : ℝ) {m i : ℕ} (hi : i < m) :
    scale r (m-i) = 2*scale r (m-(i+1)) := by
  rw [show m-i = (m-(i+1))+1 by omega,scale_succ]
lemma descending_compare {r : ℝ} (hr : 0 ≤ r) {m l i : ℕ} (hi : i ≤ l+1) :
    scale r (m-l) ≤ 2*scale r (m-i) := by
  rw [← scale_succ]
  exact scale_mono hr (by omega)

def neighborhood (r : ℝ) (q : ℤ × ℤ) : Set ℂ := {x | boxNorm (x-point r q) ≤ 25*r}
lemma point_mem_neighborhood {r : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ) : point r q ∈ neighborhood r q := by
  change boxNorm (point r q-point r q) ≤ _
  simp only [sub_self,boxNorm]
  simpa using (mul_nonneg (by norm_num : (0:ℝ) ≤ 25) hr)
end DyadicHats

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

def pathVertex {N : ℕ} (q : Grid N) (p : List (Grid N)) (i : ℕ) : ℤ × ℤ := lastVertex q (p.take i)

lemma terminal_path_locality {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {i : ℕ} (hi : i ≤ m) :
    boxNorm (point r (lastVertex q p)-point (scale r (m-i)) (pathVertex q p i)) < scale r (m-i) := by
  have hlen := active_length v hp
  have hp' : activePath (tree v m 1 q) (p.take i++p.drop i) := by simpa only [List.take_append_drop] using hp
  have hl := active_prefix_locality v hr hp' (x := point r (lastVertex q p)) (by
    rw [List.take_append_drop,hat_at_point hr.ne']
    norm_num)
  simpa only [List.length_take,show min i p.length = i by omega,pathVertex] using hl

/-- The neighborhoods used by assembly remain within the actual 200-neighbor
energy window at every earlier row, including the complete pre-birth history. -/
lemma path_neighborhood_geometry {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) {x : ℂ}
    (hx : x ∈ neighborhood (scale r (m-l)) (pathVertex q p l))
    {i : ℕ} (hi : i ≤ m) (hil : i ≤ l+1) :
    ‖x-point r (lastVertex q p)‖ ≤ 104*scale r (m-i) ∧
    boxNorm (x-point (scale r (m-i)) (pathVertex q p i)) < 199*scale r (m-i) ∧
    boxNorm (point r (lastVertex q p)-point (scale r (m-i)) (pathVertex q p i)) < 199*scale r (m-i) := by
  let y := point r (lastVertex q p)
  have hy := terminal_path_locality v hr hp hl
  have hyi := terminal_path_locality v hr hp hi
  have hxy := boxNorm_add_le (x-point (scale r (m-l)) (pathVertex q p l))
    (point (scale r (m-l)) (pathVertex q p l)-y)
  rw [sub_add_sub_cancel,boxNorm_sub_comm (point _ _)] at hxy
  change boxNorm (x-point (scale r (m-l)) (pathVertex q p l)) ≤ 25*scale r (m-l) at hx
  have hd : boxNorm (x-y) ≤ 26*scale r (m-l) := by change boxNorm (y-_) < _ at hy; linarith
  have hrel := descending_compare hr.le (m := m) hil
  have hrp := scale_pos hr (m-i)
  have hnorm := norm_le_two_boxNorm (x-y)
  have hxi := boxNorm_add_le (x-y) (y-point (scale r (m-i)) (pathVertex q p i))
  rw [sub_add_sub_cancel] at hxi
  change boxNorm (y-point (scale r (m-i)) (pathVertex q p i)) < scale r (m-i) at hyi
  exact ⟨by dsimp only [y] at hnorm hd; linarith,by linarith,by linarith⟩
end ActualMarkTrees

namespace GeometricFilter
open Finset
lemma filt_mono_on {c d : ℕ → ℝ} (j : ℕ) (h : ∀ i ≤ j, c i ≤ d i) : filt c j ≤ filt d j := by
  rw [filt_sum,filt_sum]
  exact sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (h i (by have := mem_range.mp hi; omega)) (by positivity))

lemma shifted_tail {c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc0 : ∀ i, 0 ≤ c i)
    (hcA : ∀ i, c i ≤ A) {b m : ℕ} (hbm : b ≤ m) :
    (∑ i ∈ Ico b (m+1), filt c (i+1)) ≤ 2*∑ i ∈ Ico b (m+1), c i+6*A := by
  have he := sum_Ico_sub (filt c) (by omega : b ≤ m+1)
  rw [sum_sub_distrib] at he
  have h1 := filt_tail hA hc0 hcA hbm
  linarith [filt_le hA hcA (m+1),filt_nonneg hc0 b]
end GeometricFilter

namespace DyadicHats
noncomputable def localSup (f : ℂ → ℝ) (r : ℝ) (q : ℤ × ℤ) : ℝ :=
  sSup (f '' neighborhood r q)
lemma localSup_le {f : ℂ → ℝ} {r A : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ)
    (h : ∀ x ∈ neighborhood r q, f x ≤ A) : localSup f r q ≤ A := by
  apply csSup_le (Set.Nonempty.image f ⟨point r q,point_mem_neighborhood hr q⟩)
  rintro z ⟨x,hx,rfl⟩
  exact h x hx
lemma le_localSup {f : ℂ → ℝ} {r A : ℝ} (q : ℤ × ℤ)
    (h : ∀ x ∈ neighborhood r q, f x ≤ A) {x : ℂ} (hx : x ∈ neighborhood r q) :
    f x ≤ localSup f r q := le_csSup ⟨A,by rintro z ⟨y,hy,rfl⟩; exact h y hy⟩ ⟨x,hx,rfl⟩
lemma localSup_nonneg {f : ℂ → ℝ} {r A : ℝ} (hr : 0 ≤ r) (q : ℤ × ℤ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∀ x ∈ neighborhood r q, f x ≤ A) : 0 ≤ localSup f r q :=
  (h0 (point r q)).trans (le_localSup q h (point_mem_neighborhood hr q))
end DyadicHats

namespace ActualLabels
open DyadicHats GeometricFilter FiniteLabels Finset
lemma derivativeCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (i : ℕ) (hr : 0 ≤ r i) :
    0 ≤ derivativeCost h r x i := by
  cases i with
  | zero => exact mul_nonneg hr (sum_nonneg (fun _ _ => norm_nonneg _))
  | succ i => exact FiniteLabels.expect_nonneg _ (rowDerivative_nonneg h hr x)

def cellCost (h : ℂ → ℂ) (r : ℕ → ℝ) (m l : ℕ) (q : ℤ × ℤ) : ℝ :=
  localSup (fun x => switchCost h r x l) (r l) q+
  (if l=m then 1 else localSup (fun x => switchCost h r x (l+1)) (r l) q)+
  filt (fun i => localSup (fun x => derivativeCost h r x i) (r l) q) l

lemma cellCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (m l : ℕ) (q : ℤ × ℤ) :
    0 ≤ cellCost h r m l q := by
  have hs (i : ℕ) : 0 ≤ localSup (fun x => switchCost h r x i) (r l) q :=
    localSup_nonneg (hr l).le q (fun x => switchCost_nonneg h r x i) (fun x _ => switchCost_le_one h r x i)
  have ht (i : ℕ) : 0 ≤ localSup (fun x => derivativeCost h r x i) (r l) q :=
    localSup_nonneg (hr l).le q (fun x => derivativeCost_nonneg h r x i (hr i).le)
      (fun x _ => derivativeCost_uniform h r x i (hr i))
  dsimp only [cellCost]
  exact add_nonneg (add_nonneg (hs _) (by split_ifs; exact zero_le_one; exact hs _)) (filt_nonneg ht l)
end ActualLabels

end SignedDisk

end

end OAI
