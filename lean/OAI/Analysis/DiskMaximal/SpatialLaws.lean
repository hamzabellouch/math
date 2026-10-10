import OAI.Analysis.DiskMaximal.Prices

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

namespace FiniteLabels
open DyadicHats
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spatialRow_mixture (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι) :
    spatialRow old target p hp0 hp1 r x j =
      interpolate r (fun z => (1-p z)*delta old j+p z*delta (target z) j) x := by
  have he (z : ℤ × ℤ) : (1-p z)*delta old j+p z*delta (target z) j =
      delta old j+p z*(delta (target z) j-delta old j) := by ring
  simp_rw [he]
  rw [interpolate_add,interpolate_const]
  rfl

lemma spatialRow_vanish (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (j : ι)
    (hj : ∀ z, hat r z x ≠ 0 → (1-p z)*delta old j+p z*delta (target z) j = 0) :
    spatialRow old target p hp0 hp1 r x j = 0 := by
  rw [spatialRow_mixture]
  have he : interpolate r (fun z => (1-p z)*delta old j+p z*delta (target z) j) x =
      interpolate r (fun _ => 0) x := interpolate_congr_on r x hj
  rw [he,interpolate_const]

end FiniteLabels

namespace ActualLabels
open FiniteLabels ConeCoordinates DirectionNeighbors DyadicHats

abbrev Label := {n : ℂ // n ∈ fixedPalette.labels}
instance : Fintype Label := Finset.fintypeCoeSort fixedPalette.labels
instance : DecidableEq Label := Classical.decEq _

lemma label_unit (n : Label) : ‖(n:ℂ)‖ = 1 := fixedPalette.unit n n.property

def target (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) : Label :=
  quantize (Theta h r z) (norm_theta h r (chosen h r z))
lemma target_close (h : ℂ → ℂ) (r : ℝ) (z : ℤ × ℤ) :
    ‖Theta h r z-(target h r z:ℂ)‖ < 1/2000 := quantize_close _ _

def switchChance (h : ℂ → ℂ) (r : ℝ) (n : Label) (z : ℤ × ℤ) : ℝ :=
  probability (1/100) ‖(n:ℂ)-Theta h r z‖
lemma switchChance_nonneg (h : ℂ → ℂ) (r : ℝ) (n : Label) (z : ℤ × ℤ) :
    0 ≤ switchChance h r n z := probability_nonneg _ _
lemma switchChance_le_one (h : ℂ → ℂ) (r : ℝ) (n : Label) (z : ℤ × ℤ) :
    switchChance h r n z ≤ 1 := probability_le_one _ _

def row (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : Law Label :=
  spatialRow n (target h r) (switchChance h r n) (switchChance_nonneg h r n)
    (switchChance_le_one h r n) r x

def initial (h : ℂ → ℂ) (r : ℝ) (x : ℂ) : Law Label :=
  spatialRow (quantize 1 (by norm_num)) (target h r) (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) r x

lemma nearby_sample_close {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0) :
    ‖Theta h r z-theta h r q‖ ≤ 1/1000 := by
  have hloc : boxNorm (point r z-point r q) ≤ 200*r :=
    hat_vertex_local hr (by linarith) hz
  have he := energy_controls hr h q z hloc
  nlinarith [norm_nonneg (Theta h r z-theta h r q)]

lemma sampled_good {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0) :
    Good (target h r z) (theta h r q) := by
  apply good_of_close (label_unit _)
  have he := nearby_sample_close hr h q hx hE z hz
  have ht := target_close h r z
  have hn : ‖theta h r q-(target h r z:ℂ)‖ ≤ ‖theta h r q-Theta h r z‖+‖Theta h r z-(target h r z:ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (theta h r q) (Theta h r z) (target h r z:ℂ)
  have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
  linarith

lemma retained_good {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (z : ℤ × ℤ) (hz : hat r z x ≠ 0)
    (n : Label) (hp : switchChance h r n z < 1) : Good (n:ℂ) (theta h r q) := by
  have hd := (probability_lt_one_iff (by norm_num : (0:ℝ)<1/100)).mp hp
  have he := nearby_sample_close hr h q hx hE z hz
  apply good_of_close (label_unit n)
  have hn : ‖theta h r q-(n:ℂ)‖ ≤ ‖theta h r q-Theta h r z‖+‖Theta h r z-(n:ℂ)‖ := by
    simpa only [dist_eq_norm] using dist_triangle (theta h r q) (Theta h r z) (n:ℂ)
  have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
  have hd' : ‖Theta h r z-(n:ℂ)‖ < 2*(1/100:ℝ) := by simpa only [norm_sub_rev] using hd
  linarith

lemma initial_bad_zero {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h r q)) : initial h r x n = 0 := by
  apply spatialRow_vanish
  intro z hz
  have ht : n ≠ target h r z := fun ht => hn (ht ▸ sampled_good hr h q hx hE z hz)
  simp [delta,ht]

lemma row_bad_zero {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) (old n : Label)
    (hn : ¬Good (n:ℂ) (theta h r q)) : row h r x old n = 0 := by
  apply spatialRow_vanish
  intro z hz
  have ht : n ≠ target h r z := fun ht => hn (ht ▸ sampled_good hr h q hx hE z hz)
  by_cases ho : n = old
  · subst n
    have hp : switchChance h r old z = 1 := le_antisymm (switchChance_le_one h r old z)
      (le_of_not_gt (fun hp => hn (retained_good hr h q hx hE z hz old hp)))
    simp [hp,delta,ht]
  · simp [delta,ho,ht]

/-- The actual finite-state label marginal, with its scale-dependent spatial
rows. This definition introduces no geometric or probabilistic hypothesis. -/
def marginal (h : ℂ → ℂ) (r : ℕ → ℝ) : ℕ → ℂ → Law Label
  | 0,x => initial h (r 0) x
  | k+1,x => move (marginal h r k x) (row h (r (k+1)) x)

theorem marginal_bad_zero (h : ℂ → ℂ) (r : ℕ → ℝ) (k : ℕ) (hr : 0 < r k)
    (q : ℤ × ℤ) {x : ℂ} (hx : boxNorm (x-point (r k) q) ≤ 50*r k)
    (hE : energy h (r k) q ≤ (1/1000:ℝ)^2) (n : Label)
    (hn : ¬Good (n:ℂ) (theta h (r k) q)) : marginal h r k x n = 0 := by
  cases k with
  | zero => exact initial_bad_zero hr h q hx hE n hn
  | succ k =>
    simp only [marginal,move_apply,row_bad_zero hr h q hx hE _ n hn,mul_zero,Finset.sum_const_zero]

end ActualLabels

namespace FiniteLabels
open DyadicHats Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def expect (μ : Law ι) (f : ι → ℝ) : ℝ := ∑ i, μ i*f i

lemma expect_nonneg (μ : Law ι) {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ expect μ f :=
  sum_nonneg (fun i _ => mul_nonneg (μ.nonneg i) (hf i))
lemma expect_le_one (μ : Law ι) {f : ι → ℝ} (hf : ∀ i, f i ≤ 1) : expect μ f ≤ 1 := by
  calc
    _ ≤ ∑ i, μ i*1 := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (μ.nonneg i))
    _ = _ := by simp only [mul_one,μ.total]
lemma expect_add (μ : Law ι) (f g : ι → ℝ) :
    expect μ (fun i => f i+g i) = expect μ f+expect μ g := by
  simp only [expect,mul_add,sum_add_distrib]
lemma expect_sub (μ : Law ι) (f g : ι → ℝ) :
    expect μ (fun i => f i-g i) = expect μ f-expect μ g := by
  simp only [expect,mul_sub,sum_sub_distrib]
lemma expect_move (μ : Law ι) (P : ι → Law κ) (f : κ → ℝ) :
    expect (move μ P) f = expect μ (fun i => expect (P i) f) := by
  simp only [expect,move_apply,sum_mul,mul_sum,mul_assoc]
  rw [Finset.sum_comm]

variable [DecidableEq ι]
lemma expect_delta (i : ι) (f : ι → ℝ) : expect (delta i) f = f i := by
  simp [expect,delta]

lemma spatialRow_expect (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ) (f : ι → ℝ) :
    expect (spatialRow old target p hp0 hp1 r x) f =
      f old+interpolate r (fun z => p z*(f (target z)-f old)) x := by
  simp only [expect,spatialRow_formula,add_mul,sum_add_distrib]
  rw [show (∑ i : ι, delta old i*f i) = f old from expect_delta old f]
  congr 1
  simp_rw [← interpolate_mul_const]
  rw [← interpolate_finset_sum]
  congr 1
  funext z
  simp only [mul_sub,sub_mul,sum_sub_distrib,mul_assoc,← mul_sum]
  rw [show (∑ i : ι, delta (target z) i*f i) = f (target z) from expect_delta _ _,
    show (∑ i : ι, delta old i*f i) = f old from expect_delta _ _]

/-- An absorbing finite set gives exact drift equal to the off-diagonal
switch rate. Conditions concern only tents that actually meet the point. -/
lemma spatialRow_absorbing (old : ι) (target : ℤ × ℤ → ι) (p : ℤ × ℤ → ℝ)
    (hp0 : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1) (r : ℝ) (x : ℂ)
    (b : ι → ℝ) (hb : b old = 0 ∨ b old = 1)
    (ht : ∀ z, hat r z x ≠ 0 → b (target z) = 0)
    (hz : b old = 0 → ∀ z, hat r z x ≠ 0 → p z = 0) :
    expect (spatialRow old target p hp0 hp1 r x) b+interpolate r p x = b old := by
  rw [spatialRow_expect]
  rcases hb with hb|hb
  · have he : interpolate r p x = 0 := by
      rw [interpolate_congr_on r x (hz hb),interpolate_const]
    have he' : interpolate r (fun z => p z*(b (target z)-b old)) x = 0 := by
      have hc : ∀ z, hat r z x ≠ 0 → p z*(b (target z)-b old) = 0 := by
        intro z h; rw [ht z h,hb]; ring
      rw [interpolate_congr_on r x hc,interpolate_const]
    rw [he,he']; ring
  · have hi : interpolate r (fun z => p z*(b (target z)-b old)) x =
        interpolate r (fun z => p z*(-1)) x := by
      apply interpolate_congr_on
      intro z h; rw [ht z h,hb]; ring
    rw [hi,interpolate_mul_const]; ring

end FiniteLabels

namespace ActualLabels
open FiniteLabels DyadicHats DirectionNeighbors ConeCoordinates

def badWeight (anchor : ℂ) (n : Label) : ℝ :=
  if ‖(n:ℂ)-anchor‖ ≤ (1/200:ℝ) then 0 else 1
lemma badWeight_cases (a : ℂ) (n : Label) : badWeight a n = 0 ∨ badWeight a n = 1 := by
  unfold badWeight; split_ifs <;> simp
lemma badWeight_nonneg (a : ℂ) (n : Label) : 0 ≤ badWeight a n := by
  rcases badWeight_cases a n with h|h <;> linarith
lemma badWeight_le_one (a : ℂ) (n : Label) : badWeight a n ≤ 1 := by
  rcases badWeight_cases a n with h|h <;> linarith

def rate (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : ℝ :=
  interpolate r (switchChance h r n) x
lemma rate_nonneg (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : 0 ≤ rate h r x n :=
  interpolate_nonneg r x (switchChance_nonneg h r n)
lemma rate_le_one (h : ℂ → ℂ) (r : ℝ) (x : ℂ) (n : Label) : rate h r x n ≤ 1 :=
  interpolate_le_const r x (switchChance_le_one h r n)

theorem row_drift {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) {anchor : ℂ}
    (ha : ‖theta h r q-anchor‖ ≤ 1/800) (old : Label) :
    expect (row h r x old) (badWeight anchor)+rate h r x old = badWeight anchor old := by
  apply spatialRow_absorbing _ _ _ _ _ _ _ _ (badWeight_cases _ _)
  · intro z hz
    have he := nearby_sample_close hr h q hx hE z hz
    have ht := target_close h r z
    have hn : ‖(target h r z:ℂ)-anchor‖ ≤
        ‖(target h r z:ℂ)-Theta h r z‖+‖Theta h r z-theta h r q‖+‖theta h r q-anchor‖ := by
      simpa only [dist_eq_norm] using dist_triangle4 (target h r z:ℂ) (Theta h r z) (theta h r q) anchor
    have ht' : ‖(target h r z:ℂ)-Theta h r z‖ < 1/2000 := by simpa only [norm_sub_rev] using ht
    exact ite_eq_left (by linarith)
  · intro hb z hz
    have hba : ‖(old:ℂ)-anchor‖ ≤ 1/200 := by
      by_contra hn
      unfold badWeight at hb
      rw [ite_eq_right hn] at hb
      norm_num at hb
    have he := nearby_sample_close hr h q hx hE z hz
    apply probability_eq_zero
    have hn : ‖(old:ℂ)-Theta h r z‖ ≤
        ‖(old:ℂ)-anchor‖+‖anchor-theta h r q‖+‖theta h r q-Theta h r z‖ := by
      simpa only [dist_eq_norm] using dist_triangle4 (old:ℂ) anchor (theta h r q) (Theta h r z)
    have he' : ‖theta h r q-Theta h r z‖ ≤ 1/1000 := by simpa only [norm_sub_rev] using he
    have ha' : ‖anchor-theta h r q‖ ≤ 1/800 := by simpa only [norm_sub_rev] using ha
    linarith

lemma law_drift {r : ℝ} (hr : 0 < r) (h : ℂ → ℂ) (q : ℤ × ℤ)
    {x : ℂ} (hx : boxNorm (x-point r q) ≤ 50*r)
    (hE : energy h r q ≤ (1/1000:ℝ)^2) {anchor : ℂ}
    (ha : ‖theta h r q-anchor‖ ≤ 1/800) (μ : Law Label) :
    expect (move μ (row h r x)) (badWeight anchor)+expect μ (rate h r x) =
      expect μ (badWeight anchor) := by
  rw [expect_move,← expect_add]
  congr 1
  funext old
  exact row_drift hr h q hx hE ha old

end ActualLabels

namespace ActualLabels
open FiniteLabels DyadicHats DirectionNeighbors Finset

def switchCost (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) : ℕ → ℝ
  | 0 => 1
  | k+1 => expect (marginal h r k x) (rate h (r (k+1)) x)

lemma switchCost_nonneg (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (k : ℕ) :
    0 ≤ switchCost h r x k := by
  cases k with
  | zero => exact zero_le_one
  | succ k => exact FiniteLabels.expect_nonneg _ (rate_nonneg h (r (k+1)) x)
lemma switchCost_le_one (h : ℂ → ℂ) (r : ℕ → ℝ) (x : ℂ) (k : ℕ) :
    switchCost h r x k ≤ 1 := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact expect_le_one _ (rate_le_one h (r (k+1)) x)

/-- A telescoping estimate between arbitrary birth and death times. These are
geometric low-energy assumptions on a path, not a switch-budget premise. -/
theorem switchCost_sum (h : ℂ → ℂ) (r : ℕ → ℝ) (q : ℕ → ℤ × ℤ) (x : ℂ)
    (anchor : ℕ → ℂ) (exceptional : ℕ → Bool) {b m : ℕ} (hbm : b ≤ m)
    (hr : ∀ k ∈ Finset.Ico b m, 0 < r (k+1))
    (hx : ∀ k ∈ Finset.Ico b m, boxNorm (x-point (r (k+1)) (q (k+1))) ≤ 50*r (k+1))
    (hE : ∀ k ∈ Finset.Ico b m, exceptional (k+1) = false →
      energy h (r (k+1)) (q (k+1)) ≤ (1/1000:ℝ)^2)
    (ha : ∀ k ∈ Finset.Ico b m, exceptional (k+1) = false →
      anchor (k+1) = anchor k ∧ ‖theta h (r (k+1)) (q (k+1))-anchor k‖ ≤ 1/800) :
    (∑ k ∈ Finset.Ico b m, switchCost h r x (k+1)) ≤
      1+2*∑ k ∈ Finset.Ico b m, if exceptional (k+1) then (1:ℝ) else 0 := by
  let v : ℕ → ℝ := fun k => expect (marginal h r k x) (badWeight (anchor k))
  have hv0 (k : ℕ) : 0 ≤ v k := FiniteLabels.expect_nonneg _ (badWeight_nonneg _)
  have hv1 (k : ℕ) : v k ≤ 1 := expect_le_one _ (badWeight_le_one _)
  have hs (k : ℕ) (hk : k ∈ Finset.Ico b m) : switchCost h r x (k+1) ≤
      v k-v (k+1)+2*(if exceptional (k+1) then (1:ℝ) else 0) := by
    cases he : exceptional (k+1) with
    | false =>
      obtain ⟨heq,hclose⟩ := ha k hk he
      have hd := law_drift (hr k hk) h (q (k+1)) (hx k hk) (hE k hk he) hclose (marginal h r k x)
      have hd' : v (k+1)+switchCost h r x (k+1) = v k := by
        simpa only [v,marginal,switchCost,heq] using hd
      simp only [Bool.false_eq_true,ite_false,mul_zero,add_zero]
      linarith
    | true =>
      simp only [ite_true,mul_one]
      linarith [switchCost_le_one h r x (k+1),hv0 k,hv1 (k+1)]
  have hall := sum_le_sum hs
  rw [sum_add_distrib,← mul_sum] at hall
  have ht : (∑ k ∈ Finset.Ico b m, (v k-v (k+1))) = v b-v m := by
    have hh := Finset.sum_Ico_sub (fun k => -v k) hbm
    simpa only [neg_sub_neg] using hh
  rw [ht] at hall
  linarith [hv1 b,hv0 m]

end ActualLabels

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- Only paths ending in a nonzero terminal vector can carry particles. -/
def activePath : Tree ι E → List ι → Prop
  | .leaf v, [] => v ≠ 0
  | .leaf _, _::_ => False
  | .branch _, [] => False
  | .branch t, i::p => activePath (t i) p

omit [Fintype ι] in
lemma activePath_valid {t : Tree ι E} {p : List ι} (h : activePath t p) : validPath t p := by
  induction p generalizing t with
  | nil => cases t <;> simp_all [activePath,validPath]
  | cons i p ih => cases t with
    | leaf v => exact h.elim
    | branch t => exact ih h

lemma rootEval_mono_active (t : Tree ι E) {F G : List ι → ℝ}
    (h : ∀ p, activePath t p → F p ≤ G p) : rootEval t F ≤ rootEval t G := by
  induction t generalizing F G with
  | leaf v =>
    by_cases hv : v = 0
    · simp [rootEval,hv]
    · exact mul_le_mul_of_nonneg_left (h [] hv) (norm_nonneg v)
  | branch t ih =>
    apply mul_le_mul_of_nonneg_left _ (survival_nonneg t)
    exact Finset.sum_le_sum fun i _ => ih i (fun p hp => h (i::p) hp)

lemma lateEval_mono_active (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, activePath t p → b ≤ p.length → F p b ≤ G p b) : lateEval t F ≤ lateEval t G := by
  induction t generalizing F G with
  | leaf v => rfl
  | branch t ih =>
    unfold lateEval
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (survival_le_one t))
      exact Finset.sum_le_sum fun i _ => rootEval_mono_active (t i) (fun p hp => h (i::p) 1 hp (by simp))
    · exact Finset.sum_le_sum fun i _ => ih i (fun p b hp hb => h (i::p) (b+1) hp (by simpa using Nat.succ_le_succ hb))

lemma particleEval_mono_active (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, activePath t p → b ≤ p.length → F p b ≤ G p b) : particleEval t F ≤ particleEval t G :=
  add_le_add (rootEval_mono_active t (fun p hp => h p 0 hp (Nat.zero_le _)))
    (lateEval_mono_active t h)

/-- The subtree at a prefix (values beyond terminal nodes are immaterial). -/
def atPath : Tree ι E → List ι → Tree ι E
  | t, [] => t
  | .leaf v, _::_ => .leaf v
  | .branch t, i::p => atPath (t i) p

omit [Fintype ι] in
lemma active_append {t : Tree ι E} {p q : List ι} (h : activePath t (p++q)) :
    activePath (atPath t p) q := by
  induction p generalizing t with
  | nil => simpa only [atPath,List.nil_append] using h
  | cons i p ih =>
    cases t with
    | leaf v => exact h.elim
    | branch t => exact ih h

end IntrinsicMarks

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

def lastVertex {N : ℕ} (q : Grid N) : List (Grid N) → Grid N
  | [] => q
  | s::p => lastVertex s p

def pathWeight {N : ℕ} (q : Grid N) : List (Grid N) → ℝ
  | [] => 1
  | s::p => step q s*pathWeight s p

lemma pathWeight_nonneg {N : ℕ} (q : Grid N) (p : List (Grid N)) : 0 ≤ pathWeight q p := by
  induction p generalizing q with
  | nil => exact zero_le_one
  | cons s p ih => exact mul_nonneg (step_nonneg q s) (ih s)

lemma active_length {N : ℕ} (v : Grid N → ℂ) {k : ℕ} {b : ℝ} {q : Grid N}
    {p : List (Grid N)} (h : activePath (tree v k b q) p) : p.length = k := by
  induction k generalizing b q p with
  | zero => cases p with
    | nil => rfl
    | cons i p => exact h.elim
  | succ k ih => cases p with
    | nil => exact h.elim
    | cons i p => exact congrArg Nat.succ (ih h)

lemma active_ne_zero {N : ℕ} (v : Grid N → ℂ) {k : ℕ} {b : ℝ} {q : Grid N}
    {p : List (Grid N)} (h : activePath (tree v k b q) p) : b ≠ 0 := by
  induction k generalizing b q p with
  | zero => cases p with
    | nil =>
      intro hb
      simp [tree,activePath,hb] at h
    | cons i p => exact h.elim
  | succ k ih => cases p with
    | nil => exact h.elim
    | cons i p => exact (mul_ne_zero_iff.mp (ih h)).1

lemma atPath_tree {N : ℕ} (v : Grid N → ℂ) {k : ℕ} (b : ℝ) (q : Grid N)
    (p : List (Grid N)) (hp : p.length ≤ k) :
    atPath (tree v k b q) p = tree v (k-p.length) (b*pathWeight q p) (lastVertex q p) := by
  induction p generalizing k b q with
  | nil => simp [atPath,pathWeight,lastVertex]
  | cons i p ih =>
    cases k with
    | zero => simp at hp
    | succ k =>
      simp only [tree,atPath]
      rw [ih (b*step q i) i (by simpa using hp)]
      simp only [List.length_cons,Nat.succ_sub_succ_eq_sub,pathWeight,lastVertex,mul_assoc]

lemma active_hat_support {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {k : ℕ} {b : ℝ} {q : Grid N} {p : List (Grid N)}
    (h : activePath (tree v k b q) p) {x : ℂ} (hx : hat r (lastVertex q p) x ≠ 0) :
    hat (scale r k) q x ≠ 0 := by
  induction k generalizing b q p with
  | zero => cases p with
    | nil => simpa [lastVertex,scale] using hx
    | cons i p => exact h.elim
  | succ k ih => cases p with
    | nil => exact h.elim
    | cons i p =>
      have hi := ih h hx
      have hs := (mul_ne_zero_iff.mp (active_ne_zero v h)).2
      rw [scale_succ]
      exact step_support (scale_pos hr k) hs hi

lemma lastVertex_append {N : ℕ} (q : Grid N) (p s : List (Grid N)) :
    lastVertex q (p++s) = lastVertex (lastVertex q p) s := by
  induction p generalizing q with
  | nil => rfl
  | cons i p ih => exact ih i

/-- Actual spatial locality, at every prefix of every positive-mass particle
path, for every terminal position in the genuine finest hat support. -/
theorem active_prefix_locality {N : ℕ} (v : Grid N → ℂ) {r : ℝ} (hr : 0 < r)
    {k : ℕ} {b : ℝ} {q : Grid N} {p s : List (Grid N)}
    (h : activePath (tree v k b q) (p++s)) {x : ℂ}
    (hx : hat r (lastVertex q (p++s)) x ≠ 0) :
    boxNorm (x-point (scale r (k-p.length)) (lastVertex q p)) < scale r (k-p.length) := by
  have hp : p.length ≤ k := by have := active_length v h; simp only [List.length_append] at this; omega
  have hh := active_append h
  rw [atPath_tree v b q p hp] at hh
  rw [lastVertex_append] at hx
  exact (hat_ne_zero_iff (scale_pos hr _) _ _).mp (active_hat_support v hr hh hx)

end ActualMarkTrees

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def reset (δ : ℝ) (v n : E) : E := if δ < ‖v-n‖ then v else n

def anchor (e : E) (δ : ℝ) : Tree ι E → E → List ι → E
  | .leaf v,n,_ => reset δ (direction e v) n
  | .branch t,n,[] => reset δ (direction e (∑ i,vector (t i))) n
  | .branch t,n,i::p => anchor e δ (t i) (reset δ (direction e (∑ j,vector (t j))) n) p

def rootAnchor (e : E) (δ : ℝ) (t : Tree ι E) : List ι → E :=
  anchor e δ t (direction e (vector t))

lemma anchor_zero (e : E) (δ : ℝ) (t : Tree ι E) (n : E)
    (hm : markIndicator e δ t n [] = 0) :
    anchor e δ t n [] = n ∧ ‖direction e (vector t)-n‖ ≤ δ := by
  cases t with
  | leaf v =>
    have hc : ¬δ < ‖direction e v-n‖ := by
      intro hc
      simp [markIndicator,hc] at hm
    exact ⟨by simp [anchor,reset,hc],le_of_not_gt hc⟩
  | branch t =>
    have hc : ¬δ < ‖direction e (∑ i,vector (t i))-n‖ := by
      intro hc
      simp [markIndicator,hc] at hm
    exact ⟨by simp [anchor,reset,hc],le_of_not_gt hc⟩

lemma anchor_step (e : E) (δ : ℝ) (t : Tree ι E) (n : E) (p : List ι)
    (hp : validPath t p) {s : ℕ} (hs : s < p.length)
    (hm : markIndicator e δ t n (p.take (s+1)) = 0) :
    anchor e δ t n (p.take (s+1)) = anchor e δ t n (p.take s) ∧
      ‖direction e (vector (atPath t (p.take (s+1))))-anchor e δ t n (p.take s)‖ ≤ δ := by
  induction p generalizing t n s with
  | nil => simp at hs
  | cons i p ih =>
    cases t with
    | leaf v => simp [validPath] at hp
    | branch t =>
      cases s with
      | zero =>
        have hm' : markIndicator e δ (t i) (reset δ (direction e (∑ j,vector (t j))) n) [] = 0 := by
          simpa only [List.take_succ_cons,List.take_zero,markIndicator,reset] using hm
        simpa only [List.take_succ_cons,List.take_zero,anchor,atPath] using
          anchor_zero e δ (t i) (reset δ (direction e (∑ j,vector (t j))) n) hm'
      | succ s =>
        simp only [List.length_cons,Nat.succ_lt_succ_iff] at hs
        simpa only [List.take_succ_cons,anchor,atPath] using
          ih (t i) (reset δ (direction e (∑ j,vector (t j))) n) hp hs hm

lemma rootMark_cons (e : E) {δ : ℝ} (hδ : 0 ≤ δ) (t : Tree ι E) (i : ι) (p : List ι) :
    rootMarkIndicator e δ t (i::p) = markIndicator e δ t (direction e (vector t)) (i::p) := by
  cases t <;> simp [rootMarkIndicator,markIndicator,vector,not_lt_of_ge hδ]

lemma rootAnchor_step (e : E) {δ : ℝ} (hδ : 0 ≤ δ) (t : Tree ι E) (p : List ι)
    (hp : validPath t p) {s : ℕ} (hs : s < p.length)
    (hm : rootMarkIndicator e δ t (p.take (s+1)) = 0) :
    rootAnchor e δ t (p.take (s+1)) = rootAnchor e δ t (p.take s) ∧
      ‖direction e (vector (atPath t (p.take (s+1))))-rootAnchor e δ t (p.take s)‖ ≤ δ := by
  apply anchor_step e δ t (direction e (vector t)) p hp hs
  cases p with
  | nil => simp at hs
  | cons i p => simpa only [List.take_succ_cons,rootMark_cons e hδ] using hm

lemma markIndicator_cases (e : E) (δ : ℝ) (t : Tree ι E) (n : E) (p : List ι) :
    markIndicator e δ t n p = 0 ∨ markIndicator e δ t n p = 1 := by
  induction p generalizing t n with
  | nil => cases t <;> simp only [markIndicator] <;> split_ifs <;> simp
  | cons i p ih =>
    cases t with
    | leaf v => exact Or.inl rfl
    | branch t => exact ih _ _

lemma rootMarkIndicator_cases (e : E) (δ : ℝ) (t : Tree ι E) (p : List ι) :
    rootMarkIndicator e δ t p = 0 ∨ rootMarkIndicator e δ t p = 1 := by
  cases p with
  | nil => cases t <;> exact Or.inr rfl
  | cons i p => cases t with
    | leaf v => exact Or.inl rfl
    | branch t => exact markIndicator_cases e δ (t i) _ p

lemma direction_smul_pos (e v : E) {b : ℝ} (hb : 0 < b) : direction e (b • v) = direction e v := by
  by_cases hv : v = 0
  · simp [hv,direction]
  · have hb0 := hb.ne'
    simp only [direction,smul_eq_zero,hb0,hv,or_self,ite_false,norm_smul,
      Real.norm_eq_abs,abs_of_pos hb,mul_inv_rev,smul_smul]
    congr 1
    field_simp

omit [Fintype ι] [InnerProductSpace ℝ E] in
lemma pathCharge_sum (C : List ι → ℝ) (p : List ι) (b : ℕ) :
    pathCharge C p b = ∑ s ∈ Finset.Ico b (p.length+1), C (p.take s) := by
  induction p generalizing C b with
  | nil => cases b <;> simp [pathCharge]
  | cons i p ih =>
    cases b with
    | zero =>
      simp only [pathCharge,ih,List.length_cons,Nat.Ico_zero_eq_range]
      rw [Finset.sum_range_succ' (fun s => C ((i::p).take s)) (p.length+1)]
      simp only [List.take_succ_cons,List.take_zero]
      exact add_comm _ _
    | succ b =>
      simp only [pathCharge,ih,List.length_cons]
      rw [← Finset.sum_Ico_add' (fun s => C ((i::p).take s)) b (p.length+1) 1]
      simp only [List.take_succ_cons]

end IntrinsicMarks

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks

theorem direction_at_prefix {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) {k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    {q : Grid N} {p s : List (Grid N)}
    (hp : activePath (tree (fun q => vectorMass h r q) k b q) (p++s)) :
    direction (1:ℂ) (vector (atPath (tree (fun q => vectorMass h r q) k b q) p)) =
      DirectionNeighbors.theta h (scale r (k-p.length)) (lastVertex q p) := by
  have hlen : p.length ≤ k := by have := active_length _ hp; simp only [List.length_append] at this; omega
  rw [atPath_tree _ b q p hlen,vector_actual hr hR hN hh hsupp]
  have hpa := active_append hp
  rw [atPath_tree _ b q p hlen] at hpa
  have hpos : 0 < b*pathWeight q p := lt_of_le_of_ne
    (mul_nonneg hb (pathWeight_nonneg q p)) (Ne.symm (active_ne_zero _ hpa))
  exact direction_smul_pos _ _ hpos

end ActualMarkTrees

namespace ActualMarkTrees
open DyadicHats IntrinsicMarks Finset DirectionNeighbors ActualLabels

def pathEnergy (h : ℂ → ℂ) (r : ℝ) (k : ℕ) {N : ℕ} (q : Grid N)
    (p : List (Grid N)) : ℝ := energy h (scale r (k-p.length)) (lastVertex q p)

def pathSwitches (h : ℂ → ℂ) (r : ℝ) (k : ℕ) (x : ℂ)
    {N : ℕ} (p : List (Grid N)) (b : ℕ) : ℝ :=
  ∑ i ∈ Ico b (p.length+1), switchCost h (fun j => scale r (k-j)) x i

lemma mark_nonneg {ι : Type*} [Fintype ι] (t : Tree ι ℂ) (p : List ι) :
    0 ≤ rootMarkIndicator (1:ℂ) (1/800) t p := by
  rcases rootMarkIndicator_cases (1:ℂ) (1/800) t p with h | h
  · exact h.symm.le
  · exact h.symm ▸ zero_le_one

/-- The switch bound on every genuinely occupied path, using its complete
intrinsic history, even before the particle's birth. -/
theorem path_switch_bound {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hN : R/r+1 ≤ (N:ℝ)) {h : ℂ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, h y ≠ 0 → ‖y‖ ≤ R) (k : ℕ) (q : Grid N)
    {p : List (Grid N)} (hp : activePath (tree (fun q => vectorMass h r q) k 1 q) p)
    {b : ℕ} (hb : b ≤ p.length) {x : ℂ} (hx : hat r (lastVertex q p) x ≠ 0) :
    pathSwitches h r k x p b ≤ 2+
      2*pathCharge (rootMarkIndicator (1:ℂ) (1/800) (tree (fun q => vectorMass h r q) k 1 q)) p b+
      2000000*pathCharge (pathEnergy h r k q) p b := by
  classical
  let t := tree (fun q => vectorMass h r q) k 1 q
  let M := rootMarkIndicator (1:ℂ) (1/800) t
  let rs : ℕ → ℝ := fun i => scale r (k-i)
  let qs : ℕ → ℤ × ℤ := fun i => lastVertex q (p.take i)
  let E : ℕ → ℝ := fun i => energy h (rs i) (qs i)
  let A : ℕ → ℂ := fun i => rootAnchor (1:ℂ) (1/800) t (p.take i)
  let bad : ℕ → Bool := fun i => decide (M (p.take i) ≠ 0 ∨ (1/1000:ℝ)^2 < E i)
  have hlen : p.length = k := active_length _ hp
  have hpos (i : ℕ) : 0 < rs i := scale_pos hr _
  have he0 (i : ℕ) : 0 ≤ E i := energy_nonneg h _ _
  have hpref (i : ℕ) : activePath t (p.take i++p.drop i) := by
    simpa only [List.take_append_drop] using hp
  have hloc (i : ℕ) (hi : i ≤ p.length) : boxNorm (x-point (rs i) (qs i)) ≤ 50*rs i := by
    have hl := active_prefix_locality (fun q => vectorMass h r q) hr (hpref i)
      (by simpa only [List.take_append_drop] using hx)
    have hli : (p.take i).length = i := by simp only [List.length_take,min_eq_left hi]
    simp only [hli] at hl
    exact hl.le.trans (by dsimp only [rs,qs]; nlinarith [scale_pos hr (k-i)])
  have hdir (i : ℕ) (hi : i ≤ p.length) :
      direction (1:ℂ) (vector (atPath t (p.take i))) = theta h (rs i) (qs i) := by
    have hd := direction_at_prefix hr hR hN hh hsupp (by norm_num : (0:ℝ) ≤ 1) (hpref i)
    simpa only [List.length_take,min_eq_left hi] using hd
  have hbad (i : ℕ) : bad i = false → M (p.take i) = 0 ∧ E i ≤ (1/1000:ℝ)^2 := by
    simp only [bad,decide_eq_false_iff_not,not_or,not_not,not_lt]
    exact id
  have hs := switchCost_sum h rs qs x A bad (by omega : b ≤ k)
    (fun i _ => hpos (i+1))
    (fun i hi => hloc (i+1) (by simp only [Finset.mem_Ico] at hi; omega))
    (fun i _ hi => (hbad (i+1) hi).2)
    (fun i hi he => by
      have hil : i < p.length := by simp only [Finset.mem_Ico] at hi; omega
      have ha := rootAnchor_step (1:ℂ) (by norm_num : (0:ℝ) ≤ 1/800) t p
        (activePath_valid hp) hil (hbad (i+1) he).1
      rw [hdir (i+1) (by omega)] at ha
      exact ha)
  have hind (i : ℕ) : (if bad i then (1:ℝ) else 0) ≤ M (p.take i)+1000000*E i := by
    rcases rootMarkIndicator_cases (1:ℂ) (1/800) t (p.take i) with hm | hm
    · change M (p.take i) = 0 at hm
      by_cases he : (1/1000:ℝ)^2 < E i
      · simp only [bad,hm,ne_eq,not_true_eq_false,false_or,he,decide_true,ite_true]
        nlinarith
      · simp only [bad,hm,ne_eq,not_true_eq_false,false_or,he,decide_false,Bool.false_eq_true,ite_false]
        nlinarith [he0 i]
    · change M (p.take i) = 1 at hm
      have hh0 := he0 i
      by_cases he : bad i = true <;> simp [he,show M (p.take i) = 1 from hm] <;> nlinarith
  have hterm : (∑ i ∈ Ico b k, if bad (i+1) then (1:ℝ) else 0) ≤
      pathCharge M p b+1000000*pathCharge (pathEnergy h r k q) p b := by
    calc
      _ ≤ ∑ i ∈ Ico b k, (M (p.take (i+1))+1000000*E (i+1)) :=
        sum_le_sum (fun i _ => hind (i+1))
      _ = ∑ i ∈ Ico (b+1) (k+1), (M (p.take i)+1000000*E i) := by
        exact sum_Ico_add' (fun i => M (p.take i)+1000000*E i) b k 1
      _ ≤ ∑ i ∈ Ico b (p.length+1), (M (p.take i)+1000000*E i) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_Ico] at hi ⊢
          omega
        · intro i _ _
          exact add_nonneg (mark_nonneg t _) (mul_nonneg (by norm_num) (he0 i))
      _ = _ := by
        rw [pathCharge_sum,pathCharge_sum,sum_add_distrib,mul_sum]
        congr 1
        apply sum_congr rfl
        intro i hi
        congr 1
        have hil : i ≤ p.length := by have := (Finset.mem_Ico.mp hi).2; omega
        simp only [E,rs,qs,pathEnergy,List.length_take,min_eq_left hil]
  have hsum : pathSwitches h r k x p b = switchCost h rs x b+
      ∑ i ∈ Ico b k, switchCost h rs x (i+1) := by
    change (∑ i ∈ Ico b (p.length+1), switchCost h rs x i) = _
    rw [hlen,Finset.sum_eq_sum_Ico_succ_bot (by omega : b < k+1),Finset.sum_Ico_add']
  rw [hsum]
  have h1 := switchCost_le_one h rs x b
  change _ ≤ 2+2*pathCharge M p b+2000000*pathCharge (pathEnergy h r k q) p b
  linarith

end ActualMarkTrees

end

end OAI
