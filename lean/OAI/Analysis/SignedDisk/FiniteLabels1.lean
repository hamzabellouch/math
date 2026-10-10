import OAI.Analysis.SignedDisk.DyadicHats2

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

section
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

end

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

end SignedDisk

end

end OAI
