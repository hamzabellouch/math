import OAI.Analysis.DiskMaximal.Packing

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
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

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
end GeometricFilter

namespace GeometricFilter
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

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks ActualLabels GeometricFilter Finset

lemma path_filtered_cost {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) {x : ℂ} (hx : x ∈ neighborhood (scale r (m-l)) (pathVertex q p l))
    {i : ℕ} (hi : i ≤ m) (hil : i ≤ l+1) :
    switchCost h (fun j => scale r (m-j)) x i+derivativeCost h (fun j => scale r (m-j)) x i ≤
      spatialConstant*filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) i := by
  apply filtered_spatial_cost h _ _ x _ i (fun j _ => scale_pos hr (m-j))
    (fun j hj => descending_step r (by omega))
  · intro j hj
    exact (path_neighborhood_geometry v hr hp hl hx (by omega : j ≤ m) (by omega)).2.1
  · intro j hj
    exact (path_neighborhood_geometry v hr hp hl hx (by omega : j ≤ m) (by omega)).2.2
  · exact (path_neighborhood_geometry v hr hp hl hx hi hil).1

lemma path_cellCost {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {l : ℕ} (hl : l ≤ m) :
    cellCost h (fun j => scale r (m-j)) m l (pathVertex q p l) ≤
      spatialConstant*(filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) l+
        filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))) (l+1)+
        filt (filt (energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p)))) l)+
      (if l=m then 1 else 0) := by
  let rs := fun j => scale r (m-j)
  let c := energyRate h rs (pathVertex q p) (point r (lastVertex q p))
  have hs (i : ℕ) (hi : i ≤ m) (hil : i ≤ l+1) :
      localSup (fun x => switchCost h rs x i) (rs l) (pathVertex q p l) ≤ spatialConstant*filt c i := by
    apply localSup_le (scale_pos hr _).le
    intro x hx
    have hh := path_filtered_cost h v hr hp hl hx hi hil
    change switchCost h rs x i+derivativeCost h rs x i ≤ spatialConstant*filt c i at hh
    linarith [derivativeCost_nonneg h rs x i (scale_pos hr _).le]
  have ht (i : ℕ) (hi : i ≤ l) :
      localSup (fun x => derivativeCost h rs x i) (rs l) (pathVertex q p l) ≤ spatialConstant*filt c i := by
    apply localSup_le (scale_pos hr _).le
    intro x hx
    have hh := path_filtered_cost h v hr hp hl hx (show i ≤ m by omega) (show i ≤ l+1 by omega)
    change switchCost h rs x i+derivativeCost h rs x i ≤ spatialConstant*filt c i at hh
    linarith [switchCost_nonneg h rs x i]
  have hT := filt_mono_on l ht
  rw [filt_mul] at hT
  have hnext : (if l=m then 1 else localSup (fun x => switchCost h rs x (l+1)) (rs l) (pathVertex q p l)) ≤
      spatialConstant*filt c (l+1)+(if l=m then 1 else 0) := by
    split_ifs with he
    · have hh := mul_nonneg spatialConstant_pos.le (filt_nonneg (energyRate_nonneg h rs (pathVertex q p) (point r (lastVertex q p))) (l+1))
      linarith
    · simpa only [add_zero] using hs (l+1) (by omega) le_rfl
  have hcur := hs l hl (by omega)
  change cellCost h rs m l (pathVertex q p l) ≤ _
  dsimp only [cellCost]
  change _ ≤ spatialConstant*(filt c l+filt c (l+1)+filt (filt c) l)+(if l=m then 1 else 0)
  linarith

lemma path_cellCost_sum {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {b : ℕ} (hb : b ≤ m) :
    (∑ l ∈ Ico b (m+1), cellCost h (fun j => scale r (m-j)) m l (pathVertex q p l)) ≤
      spatialConstant*(8*∑ i ∈ Ico b (m+1),
        energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p)) i+130)+1 := by
  let c := energyRate h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have hc0 := energyRate_nonneg h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have hcA := energyRate_le_five h (fun j => scale r (m-j)) (pathVertex q p) (point r (lastVertex q p))
  have h1 := filt_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have h2 := shifted_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have h3 := double_tail (by norm_num : (0:ℝ) ≤ 5) hc0 hcA hb
  have hs := sum_le_sum (fun l (hl : l ∈ Finset.Ico b (m+1)) => path_cellCost h v hr hp (show l ≤ m by have := Finset.mem_Ico.mp hl; omega))
  change _ ≤ ∑ l ∈ Ico b (m+1), (spatialConstant*(filt c l+filt c (l+1)+filt (filt c) l)+(if l=m then 1 else 0)) at hs
  simp only [sum_add_distrib,← mul_sum] at hs
  have he : (∑ l ∈ Ico b (m+1), if l=m then (1:ℝ) else 0) = 1 := by simp [hb]
  rw [he] at hs
  change _ ≤ spatialConstant*(8*∑ i ∈ Ico b (m+1), c i+130)+1
  have hh : (∑ i ∈ Ico b (m+1), filt c i)+(∑ i ∈ Ico b (m+1), filt c (i+1))+
      (∑ i ∈ Ico b (m+1), filt (filt c) i) ≤ 8*∑ i ∈ Ico b (m+1), c i+130 := by linarith
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left hh spatialConstant_pos.le])
end ActualMarkTrees

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks ActualLabels GeometricFilter DirectionNeighbors Finset

def packingCharge {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (m : ℕ) (q : Grid N) : List (Grid N) → ℝ :=
  spatialCharge (fun j z => cellCost h (fun i => scale r (m-i)) m (m-j) z) m q

lemma packingCharge_path {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {m : ℕ} {q : Grid N} {p : List (Grid N)} (hp : activePath (tree v m 1 q) p)
    {b : ℕ} (hb : b ≤ p.length) :
    pathCharge (packingCharge h r m q) p b ≤
      8*spatialConstant*particleSwitches h r m q p b+
      8*spatialConstant*pathCharge (pathEnergy h r m q) p b+(130*spatialConstant+1) := by
  have hlen := active_length v hp
  have hs := path_cellCost_sum h v hr hp (show b ≤ m by omega)
  have hC : pathCharge (packingCharge h r m q) p b =
      ∑ i ∈ Ico b (m+1), cellCost h (fun j => scale r (m-j)) m i (pathVertex q p i) := by
    rw [pathCharge_sum,hlen]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_Ico.mp hi; omega
    simp only [packingCharge,spatialCharge,List.length_take,hlen,min_eq_left hi',
      Nat.sub_sub_self hi',pathVertex]
  have hE : (∑ i ∈ Ico b (m+1), energyRate h (fun j => scale r (m-j)) (pathVertex q p)
      (point r (lastVertex q p)) i) =
      particleSwitches h r m q p b+pathCharge (pathEnergy h r m q) p b := by
    rw [pathCharge_sum]
    simp only [particleSwitches,pathSwitches,hlen,energyRate,sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_Ico.mp hi; omega
    simp only [pathEnergy,List.length_take,hlen,min_eq_left hi',pathVertex]
  rw [hC]
  rw [hE] at hs
  linarith

lemma tree_packing_bound {N : ℕ} (h : ℂ → ℂ) (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (q : Grid N) :
    nodeCharge (tree v m 1 q) (packingCharge h r m q) ≤
      8*spatialConstant*particleEval (tree v m 1 q) (particleSwitches h r m q)+
      8*spatialConstant*nodeCharge (tree v m 1 q) (pathEnergy h r m q)+
      (130*spatialConstant+1)*terminalMass (tree v m 1 q) := by
  have hs := particleEval_mono_active (tree v m 1 q)
    (F := pathCharge (packingCharge h r m q))
    (fun p b hp hb => packingCharge_path h v hr hp hb)
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy] at hs
  nlinarith only [hs]

def packingConstant : ℝ :=
  8*spatialConstant*(2560004+2000000*(576*(4097:ℝ)^2))+
  8*spatialConstant*(576*(4097:ℝ)^2)+(130*spatialConstant+1)
lemma packingConstant_pos : 0 < packingConstant := by
  dsimp [packingConstant]
  have := spatialConstant_pos
  positivity

theorem spatial_packing {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (m : ℕ) :
    (∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale r j) q*
      cellCost h (fun i => scale r (m-i)) m (m-j) q) ≤
      packingConstant*(∫ y, ‖h y‖) := by
  have hs := sum_le_sum (fun q (_ : q ∈ (univ : Finset (Grid N))) =>
    tree_packing_bound h (fun q => vectorMass h r q) hr m q)
  simp only [sum_add_distrib,← mul_sum] at hs
  have hleft : (∑ q : Grid N, nodeCharge (tree (fun q => vectorMass h r q) m 1 q)
      (packingCharge h r m q)) =
      ∑ j ∈ range (m+1), ∑ q : Grid N, scalarMass h (scale r j) q*
        cellCost h (fun i => scale r (m-i)) m (m-j) q := by
    unfold packingCharge
    rw [sum_nodeCharge]
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro q hq
    rw [← vectorMass_coeff hr hR hN hh hsupp]
    rfl
  rw [hleft,sum_energyCharge hr hR hN hh hsupp,sum_terminalMass] at hs
  have hS := forest_switch_budget hr hR hN hh hsupp m
  have hE := neighbor_energy_budget hr hR hN hh hsupp (m+1)
  have hM := sum_scalarMass_grid_le (N := N) hh r
  change (∑ q : Grid N, ‖vectorMass h r q‖) ≤ ∫ y, ‖h y‖ at hM
  have hcoef : 0 ≤ 8*spatialConstant := by have := spatialConstant_pos; positivity
  have hcoef' : 0 ≤ 130*spatialConstant+1 := by have := spatialConstant_pos; positivity
  dsimp only [packingConstant]
  nlinarith only [hs,mul_le_mul_of_nonneg_left hS hcoef,
    mul_le_mul_of_nonneg_left hE hcoef,mul_le_mul_of_nonneg_left hM hcoef']
end ActualMarkTrees

namespace CommonPrices
open DyadicHats ConeCoordinates ConeScalar LocalCancellation AffineDensities DirectionNeighbors Finset DiskMoments PricePieces

def rootMass {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) : ℝ :=
  ∑ q ∈ S, scalarMass h (scale r k) q
lemma rootMass_nonneg {N : ℕ} (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (S : Finset (Grid N)) :
    0 ≤ rootMass h r k S := sum_nonneg (fun _ _ => norm_nonneg _)

def sizeErrors {N : ℕ} {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ} (hh : Integrable h)
    (k : ℕ) (p : ℂ) (S : Finset (Grid N)) (n : ℂ) : Option (ErrorIndex N k) → ErrorPiece 2
  | none => unitPiece (rescale p (scale r k) (rootSum h r k S n))
      (integrable_rescale (rootSum_integrable hh r k S n) p (scale_pos hr k).ne') 2
  | some i => smallPiece hh hr k p S n i

lemma sizeErrors_price {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (p : ℂ) (S : Finset (Grid N))
    {n : ℂ} (hn : n ∈ fixedPalette.labels) :
    errorPrice (sizeErrors hr hh k p S n) (1/100) ≤
      (scale r k)⁻¹*(4*rootMass h r k S+2*cellPrice N r h k S) := by
  have hb : (sizeErrors hr hh k p S n none).mass ≤ (scale r k)⁻¹*4*rootMass h r k S := by
    change (∫ X, ‖rescale p (scale r k) (rootSum h r k S n) X‖) ≤ _
    rw [mass_rescale _ _ (scale_pos hr k)]
    simpa only [mul_assoc,rootMass] using mul_le_mul_of_nonneg_left
      (rootSum_mass hr hR hN hh hsupp k S (fixedPalette.unit n hn)) (inv_nonneg.mpr (scale_pos hr k).le)
  have hs := smallPiece_common_price hr hR hN hh hsupp k p S hn
  change (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*
    (smallPiece hh hr k p S n i).mass) ≤ _ at hs
  simp only [errorPrice,Fintype.sum_option,show (sizeErrors hr hh k p S n none).size = 1 from rfl,
    Real.one_rpow,one_mul]
  change (sizeErrors hr hh k p S n none).mass + (∑ i, (smallPiece hh hr k p S n i).size^(1/100:ℝ)*(smallPiece hh hr k p S n i).mass) ≤ _
  linarith

lemma sizeErrors_gradient {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {g : ℂ → ℝ} (hg : Differentiable ℝ g)
    (hh : Integrable (gradient g)) (hsupp : ∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R)
    (k : ℕ) (p : ℤ × ℤ) {n : ℂ} (hn : ‖n‖ = 1) (X : ℂ) (hX : ‖X‖ ≤ 12) :
    (∑ i, (sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n i).density X) =
      gradient (fun Y => g (point (scale r k) p+scale r k • Y)) X := by
  rw [Fintype.sum_option]
  change rescale _ _ (rootSum _ _ _ _ _) X+
    (∑ i : ErrorIndex N k, (smallPiece hh hr k _ _ n i).density X) = _
  rw [smallPiece_sum,gradient_affine hg]
  simp only [rescale,← smul_add,rootSum,← sum_add_distrib]
  have he := sum_congr rfl (fun q (_ : q ∈ cellRoots N p) =>
    (vector_decomposition hr hR hN hsupp k q hn (point (scale r k) p+scale r k • X)).symm)
  rw [he,← sum_smul,cell_partition (scale_pos hr k) (scale_index_bound hr hR hN k) hsupp p X hX]

/-- The endpoint-bin gradient price, with all root terms retained rather than
silently using the cone estimate at one-sided maximizing radii. -/
theorem size_cell_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) → ∀ (k : ℕ) (p : ℤ × ℤ)
    {n : ℂ}, n ∈ fixedPalette.labels → ∀ Q : Set ℂ, volume Q ≤ ENNReal.ofReal 1 →
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ X in Q, F X) ≤ ENNReal.ofReal (C*(scale r k)⁻¹*
        (rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      ∀ X, ‖X‖ ≤ 2 → ∀ t,
        EndpointRadius (fun Y => g (point (scale r k) p+scale r k • Y)) X t →
        ENNReal.ofReal ‖∫ Y in Metric.ball X t,
          gradient (fun Z => g (point (scale r k) p+scale r k • Z)) Y‖ ≤ F X := by
  obtain ⟨C,hC,hmajor⟩ := size_majorant (by norm_num : (0:ℝ) ≤ 2)
  refine ⟨4*C,by positivity,?_⟩
  intro N r R hr hR hN g hg hh hsupp k p n hn Q hQ
  let b := sizeErrors hr hh k (point (scale r k) p) (cellRoots N p) n
  have hg' : ContDiff ℝ 1 (fun Y => g (point (scale r k) p+scale r k • Y)) := hg.comp (by fun_prop)
  obtain ⟨F,hFm,hFi,hFb⟩ := hmajor b _ hg' Q hQ
  refine ⟨F,hFm,?_,?_⟩
  · apply hFi.trans
    apply ENNReal.ofReal_le_ofReal
    have hb := sizeErrors_price hr hR hN hh hsupp k (point (scale r k) p) (cellRoots N p) hn
    have hD : 0 ≤ cellPrice N r (gradient g) k (cellRoots N p) :=
      sum_nonneg (fun q _ => rootPrice_nonneg hr hR hN hh hsupp k q)
    change errorPrice b (1/100) ≤ _ at hb
    have hrk := scale_pos hr k
    nlinarith [mul_le_mul_of_nonneg_left hb hC.le,inv_nonneg.mpr hrk.le,
      mul_nonneg (inv_nonneg.mpr hrk.le) hD]
  · intro X hX t ht
    apply hFb X _ t ht
    filter_upwards with Y hY
    apply sizeErrors_gradient hr hR hN (hg.differentiable one_ne_zero) hh hsupp k p (fixedPalette.unit n hn)
    have hy : ‖Y-X‖ < 3 := by simpa only [Metric.mem_ball,dist_eq_norm] using hY
    have htri := norm_add_le (Y-X) X
    rw [sub_add_cancel] at htri
    linarith
end CommonPrices

end

end OAI
