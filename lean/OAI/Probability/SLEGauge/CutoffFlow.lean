import Mathlib
import OAI.Probability.SLE.MomentGauge

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.LiteralTrace

open scoped ContinuousMapZero
abbrev Driver := C(ℝ≥0, ℝ)₀
instance : MeasurableSpace Driver := borel Driver
instance : BorelSpace Driver := ⟨rfl⟩
abbrev WienerLaw := Measure Driver

def IsWiener (W : WienerLaw) : Prop :=
  ProbabilityTheory.IsBrownianReal (fun t b => b t) W

def a (κ : ℝ) := 2 / κ
def d (κ : ℝ) := 1 + 1 / (4 * a κ)
def α (κ : ℝ) := 2 - d κ
def p (κ : ℝ) := 4 * a κ - 1

def driverValue (b : Driver) (t : ℝ) : ℝ := b t.toNNReal

def diskMap (θ : ℝ) (z : ℂ) : ℂ :=
  (z - Complex.exp (θ * Complex.I)) / (z - Complex.exp (-θ * Complex.I))

def diskMapInv (θ : ℝ) (x : ℂ) : ℂ :=
  (Complex.exp (θ * Complex.I) - x * Complex.exp (-θ * Complex.I)) / (1 - x)

 
def cutoffField (κ : ℝ) (b : Driver) (j : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  (a κ : ℂ) * star (z - driverValue b t) /
    (max (‖z - driverValue b t‖ ^ 2) ((j : ℝ) ^ (-(4 : ℤ))) : ℝ)

def mesh (N : ℕ) : ℝ := (2 : ℝ) ^ (-(N : ℤ))

def eulerSteps (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) : ℕ → ℂ
  | 0 => z
  | k + 1 => eulerSteps κ b j N z k +
      mesh N * cutoffField κ b j ((k : ℝ) * mesh N) (eulerSteps κ b j N z k)

def eulerFlow (κ : ℝ) (b : Driver) (j N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  let k := ⌊t / mesh N⌋₊
  let w :=  t / mesh N - (k : ℝ)
  (1 - w : ℝ) * eulerSteps κ b j N z k + w * eulerSteps κ b j N z (k + 1)

def cutoffFlow (κ : ℝ) (b : Driver) (j : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  limUnder atTop (fun N : ℕ => eulerFlow κ b j N z t)

def Surviving (κ : ℝ) (b : Driver) (z : ℂ) (t : ℝ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ)⁻¹ <
    sInf ((fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 t)

instance (κ : ℝ) (b : Driver) (z : ℂ) (t : ℝ) : Decidable (Surviving κ b z t) :=
  Classical.propDecidable _

def flow (κ : ℝ) (b : Driver) (z : ℂ) (t : ℝ) : ℂ :=
  if h : Surviving κ b z t then cutoffFlow κ b (Nat.find h) z t else 0

def centeredFlow (κ : ℝ) (b : Driver) (z : ℂ) (t : ℝ) : ℂ :=
  flow κ b z t - driverValue b t

 
def clock (κ θ : ℝ) (b : Driver) (x : ℂ) (t : ℝ) : ℝ :=
  ∫ u in Icc (0 : ℝ) t,
    (flow κ b (diskMapInv θ x) u).im ^ 2 /
      ‖centeredFlow κ b (diskMapInv θ x) u‖ ^ 4

def initialRadius (θ : ℝ) (x : ℂ) : ℝ :=
  2 * (diskMapInv θ x).im * ‖deriv (diskMap θ) (diskMapInv θ x)‖

def radius (κ θ : ℝ) (b : Driver) (x : ℂ) (t : ℝ) : ℝ :=
  initialRadius θ x * Real.exp (-2 * a κ * clock κ θ b x t)

def angle (κ θ : ℝ) (b : Driver) (x : ℂ) (t : ℝ) : ℝ :=
  Complex.arg (centeredFlow κ b (diskMapInv θ x) t)

def green (κ θ : ℝ) (b : Driver) (x : ℂ) (t : ℝ) : ℝ :=
  if Surviving κ b (diskMapInv θ x) t then
    radius κ θ b x t ^ (-α κ) * Real.sin (angle κ θ b x t) ^ p κ
  else 0

 
def levelTime (κ θ : ℝ) (b : Driver) (ℓ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ q : ℚ, 0 < q ∧ t = ENNReal.ofReal (q : ℝ) ∧
    Surviving κ b (diskMapInv θ 0) q ∧ ℓ < clock κ θ b 0 q}

def diskK : Set ℂ := closedBall 0 (1 / 4)

def potential (κ θ : ℝ) (b : Driver) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in diskK, ENNReal.ofReal (green κ θ b x t)

 

def concat (b c : Driver) (t : ℝ) : Driver where
  toFun u := if u ≤ t.toNNReal then b u else b t.toNNReal + c (u - t.toNNReal)
  continuous_toFun := by
    apply Continuous.if_le (map_continuous b)
      (continuous_const.add ((map_continuous c).comp (continuous_id.sub continuous_const)))
      continuous_id continuous_const
    intro u hu
    change u = t.toNNReal at hu
    subst u
    simp
  map_zero' := by simp

 
def potentialDifference (κ θ : ℝ) (W : WienerLaw) (b : Driver) (h i : ℕ) : ℝ :=
  let t := (i : ℝ) * mesh h
  let v := potential κ θ b t
  let w := ∫⁻ c, potential κ θ (concat b c t) (((i : ℝ) + 1) * mesh h) ∂W
  if v < ∞ ∧ w < ∞ then v.toReal - w.toReal else 0

def discreteMass (κ θ : ℝ) (W : WienerLaw) (b : Driver) (ℓ : ℝ) (h : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (h * 2 ^ h),
    if ENNReal.ofReal (((i : ℝ) + 1) * mesh h) ≤ levelTime κ θ b ℓ
    then potentialDifference κ θ W b h i else 0

def levelDensity (κ θ : ℝ) (b : Driver) (ℓ : ℝ) : ℝ :=
  let τ := levelTime κ θ b ℓ
  if τ < ∞ then Real.exp (2 * a κ * α κ * ℓ) *
    Real.sin (angle κ θ b 0 τ.toReal) ^ p κ / Real.sin θ ^ p κ else 0

 
def angleLaw (κ : ℝ) : Measure ℝ :=
  let unnormalized := (volume.restrict (Ioo (0 : ℝ) Real.pi)).withDensity
    (fun θ => ENNReal.ofReal (Real.sin θ ^ (4 * a κ)))
  (unnormalized Set.univ)⁻¹ • unnormalized

def clip (u x : ℝ) : ℝ := min (max x 0) u

 

def finiteMoment (κ : ℝ) (W : WienerLaw) (n : ℕ) (ℓ : ℝ) : ℝ :=
  limUnder atTop (fun u : ℕ => limUnder atTop (fun h : ℕ =>
    ∫ θ, ∫ b, levelDensity κ θ b ℓ *
      (clip u (discreteMass κ θ W b ℓ h)) ^ n ∂W ∂angleLaw κ))

def moment (κ : ℝ) (W : WienerLaw) (n : ℕ) : ℝ :=
  limUnder atTop (fun ℓ : ℕ => finiteMoment κ W n ℓ)

 
def batchLevel (κ : ℝ) (W : WienerLaw) (n : ℕ) : ℕ :=
  1 + Nat.card {j : ℕ // 1 ≤ j ∧ finiteMoment κ W n j ≤ 3 * moment κ W n / 4}

def threshold (κ : ℝ) (W : WienerLaw) (n : ℕ) : ℝ :=
  4 * moment κ W (n + 1) / moment κ W n

def multiplicity (κ : ℝ) (W : WienerLaw) (n : ℕ) (k : ℤ) : ℕ :=
  if (2 : ℝ) ^ k ≤ threshold κ W n then
    ⌊(4 : ℝ) ^ n * ((2 : ℝ) ^ k) ^ n / moment κ W n⌋₊ else 0

 

abbrev Entry := ℕ × Option (ℤ × ℕ)

def ValidEntry (κ : ℝ) (W : WienerLaw) (e : Entry) : Prop :=
  1 ≤ e.1 ∧ match e.2 with
    | none => True
    | some (k,j) => j < multiplicity κ W e.1 k

def entryValue (e : Entry) : ℝ :=
  match e.2 with
    | none => e.1
    | some (k,_) => (2 : ℝ) ^ k

def entryPosition (κ : ℝ) (W : WienerLaw) (e : Entry) : ℕ :=
  match e.2 with
    | none => ∑' k : ℤ, multiplicity κ W e.1 k
    | some (k,j) => (∑' l : ℤ, if l < k then multiplicity κ W e.1 l else 0) + j

def entryRadius (κ : ℝ) (W : WienerLaw) (e : Entry) : ℝ :=
  Real.exp (-(e.1 : ℝ) ^ 2 - 2 * a κ * (entryPosition κ W e : ℝ) *
    ((batchLevel κ W e.1 : ℝ) + (e.1 : ℝ)))

def entryCost (κ : ℝ) (W : WienerLaw) (e : Entry) (r : ℝ) : ℝ :=
  entryValue e * entryRadius κ W e ^ d κ * max 1 ((r / entryRadius κ W e) ^ 2)

 
def gauge (κ : ℝ) (W : WienerLaw) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else sInf {v | ∃ e : Entry, ValidEntry κ W e ∧ v = entryCost κ W e r}

def IsHausdorffGauge (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Ici 0) ∧ MonotoneOn h (Ici 0) ∧ h 0 = 0 ∧ ∀ r > 0, 0 < h r

 
def hausdorff (h : ℝ → ℝ) : OuterMeasure ℂ :=
  OuterMeasure.mkMetric (fun r => if r = ∞ then ∞ else ENNReal.ofReal (h r.toReal))

def inverseFlow (κ : ℝ) (b : Driver) (t : ℝ) (w : ℂ) : ℂ :=
  @ite ℂ (∃ z : ℂ, Surviving κ b z t ∧ flow κ b z t = w) (Classical.propDecidable _)
    (Classical.epsilon (fun z : ℂ => Surviving κ b z t ∧ flow κ b z t = w)) 0

 
def trace (κ : ℝ) (b : Driver) (t : ℝ) : ℂ :=
  limUnder (nhdsWithin 0 (Ioi 0)) (fun ε : ℝ =>
    inverseFlow κ b (κ * t) (driverValue b (κ * t) + ε * Complex.I))

 

def MainObligation : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 → ∀ W : WienerLaw, IsWiener W →
    IsHausdorffGauge (gauge κ W) ∧
    ∀ᵐ b ∂W, ∀ s t : ℝ, 0 < s → s < t →
      0 < hausdorff (gauge κ W) ((trace κ b) '' Icc s t) ∧
      hausdorff (gauge κ W) ((trace κ b) '' Icc s t) < ∞

end SLEExactGauge.LiteralTrace

 

noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.Cutoff

def denominator (q : ℝ) (z : ℂ) : ℝ := max (‖z‖^2) (q^2)

def inverse (q : ℝ) (z : ℂ) : ℂ := star z / (denominator q z : ℂ)

lemma denominator_pos {q : ℝ} (hq : 0 < q) (z : ℂ) : 0 < denominator q z :=
  lt_of_lt_of_le (sq_pos_of_pos hq) (le_max_right _ _)

lemma q_mul_norm_le_denominator {q : ℝ} (hq : 0 ≤ q) (z : ℂ) :
    q * ‖z‖ ≤ denominator q z := by
  by_cases he : ‖z‖ ≤ q
  · exact (mul_le_mul_of_nonneg_left he hq).trans (by
      change q*q ≤ max (‖z‖^2) (q^2)
      rw [← sq]
      exact le_max_right _ _)
  · exact (mul_le_mul_of_nonneg_right (le_of_not_ge he) (norm_nonneg _)).trans (by
      change ‖z‖*‖z‖ ≤ max (‖z‖^2) (q^2)
      rw [← sq]
      exact le_max_left _ _)

lemma norm_inverse_le {q : ℝ} (hq : 0 < q) (z : ℂ) :
    ‖inverse q z‖ ≤ q⁻¹ := by
  rw [inverse, norm_div, norm_star, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (denominator_pos hq z)]
  apply (div_le_iff₀ (denominator_pos hq z)).mpr
  have hh := q_mul_norm_le_denominator hq.le z
  have he : q⁻¹ * denominator q z = denominator q z / q := by ring
  rw [he]
  exact (le_div_iff₀ hq).mpr (by simpa only [mul_comm] using hh)

lemma denominator_sub_le {q : ℝ} {z w : ℂ} (hzw : ‖z‖ ≤ ‖w‖) :
    0 ≤ denominator q w - denominator q z ∧
    denominator q w - denominator q z ≤ (‖w‖+‖z‖)*‖w-z‖ := by
  have hn : ‖z‖^2 ≤ ‖w‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hzw
  have hden : denominator q z ≤ denominator q w := max_le_max_right _ hn
  refine ⟨sub_nonneg.mpr hden, ?_⟩
  have hd : max (‖w‖^2) (q^2) - max (‖z‖^2) (q^2) ≤ ‖w‖^2 - ‖z‖^2 := by
    by_cases hz : q^2 ≤ ‖z‖^2
    · rw [max_eq_left (hz.trans hn), max_eq_left hz]
    · rw [max_eq_right (le_of_not_ge hz)]
      by_cases hw : q^2 ≤ ‖w‖^2
      · rw [max_eq_left hw]
        linarith
      · rw [max_eq_right (le_of_not_ge hw)]
        linarith
  refine hd.trans ?_
  calc ‖w‖^2 - ‖z‖^2 = (‖w‖+‖z‖)*(‖w‖-‖z‖) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sub_norm_le w z)
         (add_nonneg (norm_nonneg _) (norm_nonneg _))

lemma inverse_sub_bound_ordered {q : ℝ} (hq : 0 < q) (z w : ℂ)
    (hzw : ‖z‖ ≤ ‖w‖) :
    ‖inverse q z - inverse q w‖ ≤ (3/q^2)*‖z-w‖ := by
  let dz := denominator q z
  let dw := denominator q w
  have hz : 0 < dz := denominator_pos hq z
  have hw : 0 < dw := denominator_pos hq w
  have hzne : (dz : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hz
  have hwne : (dw : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hw
  have he : inverse q z - inverse q w =
      (star z - star w)/(dw:ℂ) + star z * ((dw:ℂ)-(dz:ℂ))/((dz:ℂ)*(dw:ℂ)) := by
    dsimp [inverse]
    change star z/(dz:ℂ)-star w/(dw:ℂ) = _
    change star z/(dz:ℂ)-star w/(dw:ℂ) =
      (star z-star w)/(dw:ℂ)+star z*((dw:ℂ)-(dz:ℂ))/((dz:ℂ)*(dw:ℂ))
    field_simp [hzne, hwne]
    ring
  have hd := denominator_sub_le (q := q) hzw
  have hdz : q^2 ≤ dz := le_max_right _ _
  have hdw : q^2 ≤ dw := le_max_right _ _
  have hqw := q_mul_norm_le_denominator hq.le w
  have htwo : ‖z‖*(dw-dz) ≤ 2 * dw * ‖z-w‖ := by
    have hm := mul_le_mul_of_nonneg_left hd.2 (norm_nonneg z)
    rw [norm_sub_rev w z] at hm
    have hn : ‖z‖*(‖w‖+‖z‖) ≤ 2*dw := by
      have hww : ‖w‖^2 ≤ dw := le_max_left _ _
      nlinarith [norm_nonneg z, norm_nonneg w]
    calc ‖z‖*(dw-dz) ≤ ‖z‖*((‖w‖+‖z‖)*‖z-w‖) := hm
         _ = (‖z‖*(‖w‖+‖z‖))*‖z-w‖ := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  have hb₁ : ‖star z - star w‖ / dw ≤ ‖z-w‖ / q^2 := by
    rw [← star_sub, norm_star]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hq) hdw
  have hb₂ : ‖z‖*(dw-dz)/(dz*dw) ≤ 2*‖z-w‖/(q^2) := by
    calc
      _ ≤ 2*dw*‖z-w‖/(dz*dw) := div_le_div_of_nonneg_right htwo (mul_nonneg hz.le hw.le)
      _ = 2*‖z-w‖/dz := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hq) hdz
  rw [he]
  calc
    _ ≤ ‖(star z-star w)/(dw:ℂ)‖ +
        ‖star z*((dw:ℂ)-(dz:ℂ))/((dz:ℂ)*(dw:ℂ))‖ := norm_add_le _ _
    _ = ‖star z-star w‖/dw + ‖z‖*(dw-dz)/(dz*dw) := by
      rw [norm_div, norm_div, norm_mul, norm_mul, norm_star,
        ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hw, abs_of_pos hz, abs_of_nonneg hd.1]
    _ ≤ ‖z-w‖/q^2 + 2*‖z-w‖/q^2 := add_le_add hb₁ hb₂
    _ = _ := by ring

lemma inverse_sub_bound {q : ℝ} (hq : 0 < q) (z w : ℂ) :
    ‖inverse q z - inverse q w‖ ≤ (3/q^2)*‖z-w‖ := by
  rcases le_total ‖z‖ ‖w‖ with h | h
  · exact inverse_sub_bound_ordered hq z w h
  · simpa only [norm_sub_rev] using inverse_sub_bound_ordered hq w z h

lemma lipschitz_inverse {q : ℝ} (hq : 0 < q) :
    LipschitzWith ⟨3/q^2, by positivity⟩ (inverse q) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist (inverse q z) (inverse q w) ≤ (3/q^2)*dist z w
  simpa only [dist_eq_norm] using inverse_sub_bound hq z w

 
def field (a q : ℝ) (b : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ) * inverse q (z - (b t : ℂ))

lemma norm_field_le {q : ℝ} (hq : 0 < q) (a : ℝ) (b : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    ‖field a q b t z‖ ≤ |a| / q := by
  rw [field, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |a| * ‖inverse q (z - (b t : ℂ))‖ ≤ |a| * q⁻¹ :=
          mul_le_mul_of_nonneg_left (norm_inverse_le hq _) (abs_nonneg a)
       _ = _ := div_eq_mul_inv _ _ |>.symm

lemma field_sub_le {q : ℝ} (hq : 0 < q) (a : ℝ) (b : ℝ → ℝ) (t : ℝ) (z w : ℂ) :
    ‖field a q b t z - field a q b t w‖ ≤ (|a| *3/q^2)*‖z-w‖ := by
  rw [field, field, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left
    (inverse_sub_bound hq (z-(b t:ℂ)) (w-(b t:ℂ))) (abs_nonneg a)
  simpa only [sub_sub_sub_cancel_right, mul_div_assoc, mul_assoc] using hh

lemma continuous_field_time {q : ℝ} (hq : 0 < q) (a : ℝ) {b : ℝ → ℝ}
    (hb : Continuous b) (z : ℂ) : Continuous (fun t => field a q b t z) := by
  exact continuous_const.mul ((lipschitz_inverse hq).continuous.comp
    (continuous_const.sub (Complex.continuous_ofReal.comp hb)))

lemma field_joint_sub_le {q : ℝ} (hq : 0 < q) (a : ℝ) (b : ℝ → ℝ)
    (s t : ℝ) (z w : ℂ) :
    ‖field a q b s z - field a q b t w‖ ≤
      (|a| *3/q^2)*(‖z-w‖ + |b s-b t|) := by
  rw [field, field, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hdiff : (z-(b s:ℂ))-(w-(b t:ℂ)) = (z-w)-((b s:ℂ)-(b t:ℂ)) := by ring
  calc
    _ ≤ |a| * ((3/q^2)*‖(z-(b s:ℂ))-(w-(b t:ℂ))‖) :=
      mul_le_mul_of_nonneg_left (inverse_sub_bound hq _ _) (abs_nonneg _)
    _ = (|a| *3/q^2)*‖(z-w)-((b s:ℂ)-(b t:ℂ))‖ := by rw [hdiff]; ring
    _ ≤ (|a| *3/q^2)*(‖z-w‖ + ‖(b s:ℂ)-(b t:ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = _ := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

 

theorem exists_solution_on_compact {q : ℝ} (hq : 0 < q) (a : ℝ) {b : ℝ → ℝ}
    (hb : Continuous b) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ g : ℝ → ℂ, g 0 = z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt g (field a q b t (g t)) (Icc 0 T) t := by
  let M : ℝ≥0 := ⟨|a|/q, by positivity⟩
  let K : ℝ≥0 := ⟨|a| *3/q^2, by positivity⟩
  let R : ℝ≥0 := ⟨(|a|/q)*T, mul_nonneg (by positivity) hT⟩
  have hp : IsPicardLindelof (field a q b) (tmin := 0) (tmax := T)
      ⟨0, ⟨le_rfl, hT⟩⟩ z R 0 M K := by
    constructor
    · intro t ht
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro w v
      change dist (field a q b t w) (field a q b t v) ≤ (|a| *3/q^2)*dist w v
      simpa only [dist_eq_norm] using field_sub_le hq a b t w v
    · intro w hw
      exact (continuous_field_time hq a hb w).continuousOn
    · intro t ht w hw
      exact norm_field_le hq a b t w
    · change (|a|/q)*max (T-0) (0-0) ≤ (|a|/q)*T-0
      simp only [sub_zero, sub_self, max_eq_left hT, le_refl]
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end SLEExactGauge.Cutoff

 

noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.Euler

def nodes (f : ℝ → ℂ → ℂ) (h : ℝ) (z : ℂ) : ℕ → ℂ
  | 0 => z
  | k+1 => nodes f h z k + h • f ((k:ℝ)*h) (nodes f h z k)

end SLEExactGauge.Euler
end
end
end
end

end OAI
