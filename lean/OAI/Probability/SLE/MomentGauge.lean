import Mathlib

namespace OAI

/-! Quadratic moment envelopes, Hausdorff gauge admissibility and interval transfer. -/

universe u

noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

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

def IsChordalSLE {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ)
    (γ : Ω → ℝ → ℂ) (P : Measure Ω) : Prop :=
  ∃ (W : WienerLaw) (B : Ω → Driver),
    IsWiener W ∧ ProbabilityTheory.HasLaw B W P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → γ ω t = trace κ (B ω) t

end SLEExactGauge.Target

namespace SLEExactGauge.QuadraticEnvelope

variable {ι : Type*}

def profile (b R : ι → ℝ) (d : ℝ) (i : ι) (r : ℝ) : ℝ :=
  b i * R i ^ d * max 1 ((r / R i) ^ 2)

def full (b R : ι → ℝ) (d : ℝ) (r : ℝ) : ℝ :=
  if r ≤ 0 then 0 else sInf (range (fun i => profile b R d i r))

variable {b R : ι → ℝ} {d : ℝ}

lemma profile_nonneg (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (i : ι) (r : ℝ) : 0 ≤ profile b R d i r := by
  unfold profile
  exact mul_nonneg (mul_nonneg (hb i) (Real.rpow_nonneg (hR i).le d))
    (le_trans zero_le_one (le_max_left _ _))

lemma base_le_profile (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (i : ι) (r : ℝ) : b i * R i ^ d ≤ profile b R d i r := by
  unfold profile
  exact le_mul_of_one_le_right
    (mul_nonneg (hb i) (Real.rpow_nonneg (hR i).le d)) (le_max_left _ _)

lemma profile_mono (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (i : ι) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    profile b R d i r ≤ profile b R d i s := by
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (hb i) (Real.rpow_nonneg (hR i).le d))
  exact max_le_max_left _ <| pow_le_pow_left₀ (div_nonneg hr (hR i).le)
    (div_le_div_of_nonneg_right hrs (hR i).le) 2

lemma profile_scale_le (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (i : ι) {C : ℝ} (hC : 1 ≤ C) (r : ℝ) :
    profile b R d i (C * r) ≤ C ^ 2 * profile b R d i r := by
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hmax : max 1 (((C * r) / R i) ^ 2) ≤
      C ^ 2 * max 1 ((r / R i) ^ 2) := by
    apply max_le
    · exact hC2.trans <| le_mul_of_one_le_right (sq_nonneg C) (le_max_left _ _)
    · calc
        (((C * r) / R i) ^ 2) = C ^ 2 * (r / R i) ^ 2 := by ring
        _ ≤ C ^ 2 * max 1 ((r / R i) ^ 2) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg C)
  unfold profile
  calc
    _ ≤ b i * R i ^ d * (C ^ 2 * max 1 ((r / R i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hmax
        (mul_nonneg (hb i) (Real.rpow_nonneg (hR i).le d))
    _ = _ := by ring

@[simp] lemma full_zero : full b R d 0 = 0 := by simp [full]

lemma full_of_nonpos {r : ℝ} (hr : r ≤ 0) : full b R d r = 0 := by
  simp [full, hr]

lemma full_of_pos {r : ℝ} (hr : 0 < r) :
    full b R d r = sInf (range (fun i => profile b R d i r)) := by
  simp [full, hr.not_ge]

lemma profiles_bddBelow (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (r : ℝ) : BddBelow (range (fun i => profile b R d i r)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact profile_nonneg hb hR i r

variable [Nonempty ι]

lemma le_full {r v : ℝ} (hr : 0 < r)
    (hv : ∀ i, v ≤ profile b R d i r) : v ≤ full b R d r := by
  rw [full_of_pos hr]
  exact le_csInf (range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact hv i)

lemma full_nonneg (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (r : ℝ) : 0 ≤ full b R d r := by
  by_cases hr : r ≤ 0
  · rw [full_of_nonpos hr]
  · exact le_full (lt_of_not_ge hr) (fun i => profile_nonneg hb hR i r)

omit [Nonempty ι] in
lemma full_le_profile (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (i : ι) (r : ℝ) : full b R d r ≤ profile b R d i r := by
  by_cases hr : r ≤ 0
  · rw [full_of_nonpos hr]
    exact profile_nonneg hb hR i r
  · rw [full_of_pos (lt_of_not_ge hr)]
    exact csInf_le (profiles_bddBelow hb hR r) (mem_range_self i)

lemma full_monoOn (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i) :
    MonotoneOn (full b R d) (Ici 0) := by
  intro r hr s hs hrs
  by_cases hr0 : r ≤ 0
  · rw [full_of_nonpos hr0]
    exact full_nonneg hb hR s
  · have hrpos := lt_of_not_ge hr0
    apply le_full (hrpos.trans_le hrs)
    intro i
    exact (full_le_profile hb hR i r).trans (profile_mono hb hR i hr hrs)

theorem full_scale_le (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    {C r : ℝ} (hC : 1 ≤ C) (hr : 0 ≤ r) :
    full b R d (C * r) ≤ C ^ 2 * full b R d r := by
  obtain rfl | hrpos := hr.eq_or_lt
  · simp
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hC2 : 0 < C ^ 2 := sq_pos_of_pos hCpos
  have h : full b R d (C * r) / C ^ 2 ≤ full b R d r := by
    apply le_full hrpos
    intro i
    apply (div_le_iff₀ hC2).2
    calc
      full b R d (C * r) ≤ profile b R d i (C * r) := full_le_profile hb hR i _
      _ ≤ C ^ 2 * profile b R d i r := profile_scale_le hb hR i hC r
      _ = profile b R d i r * C ^ 2 := mul_comm _ _
  simpa [mul_comm] using (div_le_iff₀ hC2).1 h

lemma power_lower_bound {c r : ℝ} (hc : 0 < c) (hb : ∀ i, c ≤ b i)
    (hR : ∀ i, 0 < R i) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) (hr : 0 < r) :
    c * r ^ d ≤ full b R d r := by
  apply le_full hr
  intro i
  have hshape : r ^ d ≤ R i ^ d * max 1 ((r / R i) ^ 2) := by
    rcases le_total r (R i) with hsmall | hlarge
    · exact (Real.rpow_le_rpow hr.le hsmall hd0).trans <|
        le_mul_of_one_le_right (Real.rpow_nonneg (hR i).le d) (le_max_left _ _)
    · have hratio : 1 ≤ r / R i := (le_div_iff₀ (hR i)).2 (by simpa using hlarge)
      have hp : (r / R i) ^ d ≤ (r / R i) ^ 2 := by
        exact_mod_cast Real.rpow_le_rpow_of_exponent_le hratio hd2
      calc
        r ^ d = R i ^ d * (r / R i) ^ d := by
          rw [← Real.mul_rpow (hR i).le (div_nonneg hr.le (hR i).le)]
          congr 1
          field_simp [(hR i).ne']
        _ ≤ R i ^ d * (r / R i) ^ 2 :=
          mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (hR i).le d)
        _ ≤ R i ^ d * max 1 ((r / R i) ^ 2) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_nonneg (hR i).le d)
  calc
    c * r ^ d ≤ b i * r ^ d := mul_le_mul_of_nonneg_right (hb i) (Real.rpow_nonneg hr.le d)
    _ ≤ b i * (R i ^ d * max 1 ((r / R i) ^ 2)) :=
      mul_le_mul_of_nonneg_left hshape (hc.le.trans (hb i))
    _ = profile b R d i r := by rw [profile]; ring

lemma full_pos {c r : ℝ} (hc : 0 < c) (hb : ∀ i, c ≤ b i)
    (hR : ∀ i, 0 < R i) (hd0 : 0 ≤ d) (hd2 : d ≤ 2) (hr : 0 < r) :
    0 < full b R d r :=
  (mul_pos hc (Real.rpow_pos_of_pos hr d)).trans_le
    (power_lower_bound hc hb hR hd0 hd2 hr)

lemma ratio_bounds (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    min 1 ((s / r) ^ 2) * full b R d r ≤ full b R d s ∧
      full b R d s ≤ max 1 ((s / r) ^ 2) * full b R d r := by
  have hmono := full_monoOn (d := d) hb hR
  have hnonneg := full_nonneg (d := d) hb hR r
  constructor
  · rcases le_total r s with hrs | hsr
    · calc
        _ ≤ 1 * full b R d r := mul_le_mul_of_nonneg_right (min_le_left _ _) hnonneg
        _ = full b R d r := one_mul _
        _ ≤ full b R d s := hmono hr.le hs.le hrs
    · have hC : 1 ≤ r / s := (le_div_iff₀ hs).2 (by simpa using hsr)
      have hscale := full_scale_le (d := d) hb hR hC hs.le
      rw [div_mul_cancel₀ r hs.ne'] at hscale
      calc
        _ ≤ (s / r) ^ 2 * full b R d r :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hnonneg
        _ ≤ (s / r) ^ 2 * ((r / s) ^ 2 * full b R d s) :=
          mul_le_mul_of_nonneg_left hscale (sq_nonneg _)
        _ = full b R d s := by field_simp
  · rcases le_total s r with hsr | hrs
    · exact (hmono hs.le hr.le hsr).trans <| by
        simpa using mul_le_mul_of_nonneg_right (le_max_left 1 ((s / r) ^ 2)) hnonneg
    · have hC : 1 ≤ s / r := (le_div_iff₀ hr).2 (by simpa using hrs)
      have hscale := full_scale_le (d := d) hb hR hC hr.le
      rw [div_mul_cancel₀ s hr.ne'] at hscale
      exact hscale.trans <| mul_le_mul_of_nonneg_right (le_max_right _ _) hnonneg

lemma continuousAt_pos (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    {r : ℝ} (hr : 0 < r) : ContinuousAt (full b R d) r := by
  have hlow : ContinuousAt (fun s : ℝ => min 1 ((s / r) ^ 2) * full b R d r) r := by
    fun_prop
  have hupp : ContinuousAt (fun s : ℝ => max 1 ((s / r) ^ 2) * full b R d r) r := by
    fun_prop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa [hr.ne'] using hlow.tendsto)
    (by simpa [hr.ne'] using hupp.tendsto)
  · filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (ratio_bounds hb hR hr hs).1
  · filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (ratio_bounds hb hR hr hs).2

lemma continuousAt_zero (hb : ∀ i, 0 ≤ b i) (hR : ∀ i, 0 < R i)
    (hsmall : ∀ ε > 0, ∃ i, b i * R i ^ d < ε) :
    ContinuousAt (full b R d) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨i, hi⟩ := hsmall ε hε
  refine ⟨R i, hR i, ?_⟩
  intro x hx
  rw [full_zero, Real.dist_eq, sub_zero, abs_of_nonneg (full_nonneg hb hR x)]
  by_cases hx0 : x ≤ 0
  · rw [full_of_nonpos hx0]
    exact hε
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hxr : x < R i := by
      simpa [Real.dist_eq, abs_of_pos hxpos] using hx
    have hratio : 0 ≤ x / R i := div_nonneg hxpos.le (hR i).le
    have hratio1 : x / R i ≤ 1 := (div_le_one (hR i)).2 hxr.le
    have hp : (x / R i) ^ 2 ≤ 1 := by
      simpa using (pow_le_pow_left₀ hratio hratio1 2)
    calc
      full b R d x ≤ profile b R d i x := full_le_profile hb hR i x
      _ = b i * R i ^ d := by simp [profile, max_eq_left hp]
      _ < ε := hi

theorem isHausdorffGauge {c : ℝ} (hc : 0 < c) (hb : ∀ i, c ≤ b i)
    (hR : ∀ i, 0 < R i) (hd0 : 0 ≤ d) (hd2 : d ≤ 2)
    (hsmall : ∀ ε > 0, ∃ i, b i * R i ^ d < ε) :
    SLEExactGauge.Target.IsHausdorffGauge (full b R d) := by
  have hb0 : ∀ i, 0 ≤ b i := fun i => hc.le.trans (hb i)
  refine ⟨?_, full_monoOn hb0 hR, full_zero, fun r hr => full_pos hc hb hR hd0 hd2 hr⟩
  intro r hr
  obtain rfl | hrpos := (show 0 ≤ r from hr).eq_or_lt
  · exact (continuousAt_zero hb0 hR hsmall).continuousWithinAt
  · exact (continuousAt_pos hb0 hR hrpos).continuousWithinAt

theorem restore_finite (hb : ∀ i, 0 < b i) (hR : ∀ i, 0 < R i)
    (discarded : Finset ι) (F : ℝ → ℝ) {M C : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r > 0, F r ≤ M)
    (htail : ∀ i, i ∉ discarded → ∀ r > 0, F r ≤ C * profile b R d i r) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ r > 0, F r ≤ C' * full b R d r := by
  let C' := max C 0 + 1 + ∑ i ∈ discarded, M / (b i * R i ^ d)
  have hbase : ∀ i, 0 < b i * R i ^ d :=
    fun i => mul_pos (hb i) (Real.rpow_pos_of_pos (hR i) d)
  have hterm : ∀ i, 0 ≤ M / (b i * R i ^ d) :=
    fun i => div_nonneg hM (hbase i).le
  have hsum : 0 ≤ ∑ i ∈ discarded, M / (b i * R i ^ d) :=
    Finset.sum_nonneg (fun i _ => hterm i)
  have hC' : 0 < C' := by
    dsimp [C']
    linarith [le_max_right C 0]
  have hCC' : C ≤ C' := by
    dsimp [C']
    linarith [le_max_left C 0]
  have hall : ∀ r > 0, ∀ i, F r ≤ C' * profile b R d i r := by
    intro r hr i
    by_cases hi : i ∈ discarded
    · have hi_le : M / (b i * R i ^ d) ≤ C' := by
        have hh := Finset.single_le_sum (fun i (_ : i ∈ discarded) => hterm i) hi
        dsimp [C']
        linarith [le_max_right C 0]
      calc
        F r ≤ M := hbound r hr
        _ ≤ C' * (b i * R i ^ d) := (div_le_iff₀ (hbase i)).1 hi_le
        _ ≤ C' * profile b R d i r := mul_le_mul_of_nonneg_left
          (base_le_profile (fun i => (hb i).le) hR i r) hC'.le
    · exact (htail i hi r hr).trans <| mul_le_mul_of_nonneg_right hCC'
        (profile_nonneg (fun i => (hb i).le) hR i r)
  refine ⟨C', hC', fun r hr => ?_⟩
  have h : F r / C' ≤ full b R d r := by
    apply le_full hr
    intro i
    exact (div_le_iff₀ hC').2 (by simpa [mul_comm] using hall r hr i)
  simpa [mul_comm] using (div_le_iff₀ hC').1 h

end SLEExactGauge.QuadraticEnvelope

namespace SLEExactGauge.Target

def diskMap (θ : ℝ) (z : ℂ) : ℂ :=
  (z - Complex.exp (θ * Complex.I)) / (z - Complex.exp (-θ * Complex.I))

def diskMapInv (θ : ℝ) (x : ℂ) : ℂ :=
  (Complex.exp (θ * Complex.I) - x * Complex.exp (-θ * Complex.I)) / (1 - x)

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

end SLEExactGauge.Target

namespace SLEExactGauge.Intervals

theorem all_real_of_all_rational {X : Type*} (μ : OuterMeasure X) (γ : ℝ → X)
    (h : ∀ q r : ℚ, 0 < q → q < r →
      0 < μ (γ '' Icc (q : ℝ) (r : ℝ)) ∧ μ (γ '' Icc (q : ℝ) (r : ℝ)) < ∞) :
    ∀ s t : ℝ, 0 < s → s < t →
      0 < μ (γ '' Icc s t) ∧ μ (γ '' Icc s t) < ∞ := by
  intro s t hs hst
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hst
  obtain ⟨r, hqr, hrt⟩ := exists_rat_btwn hqt
  have hq0 : 0 < q := by exact_mod_cast hs.trans hsq
  have hqr' : q < r := by exact_mod_cast hqr
  have hpos := (h q r hq0 hqr').1
  have hlower : γ '' Icc (q : ℝ) (r : ℝ) ⊆ γ '' Icc s t :=
    image_mono (Icc_subset_Icc hsq.le hrt.le)
  obtain ⟨u, hu0, hus⟩ := exists_rat_btwn hs
  obtain ⟨v, htv⟩ := exists_rat_gt t
  have hu0' : 0 < u := by exact_mod_cast hu0
  have huv : u < v := by exact_mod_cast hus.trans (hst.trans htv)
  have hfinite := (h u v hu0' huv).2
  have hupper : γ '' Icc s t ⊆ γ '' Icc (u : ℝ) (v : ℝ) :=
    image_mono (Icc_subset_Icc hus.le htv.le)
  exact ⟨hpos.trans_le (μ.mono hlower), (μ.mono hupper).trans_lt hfinite⟩

theorem ae_all_real_of_ae_rational {Ω X : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : OuterMeasure X) (γ : Ω → ℝ → X)
    (h : ∀ q r : ℚ, 0 < q → q < r →
      ∀ᵐ ω ∂P, 0 < μ (γ ω '' Icc (q : ℝ) (r : ℝ)) ∧
        μ (γ ω '' Icc (q : ℝ) (r : ℝ)) < ∞) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 < s → s < t →
      0 < μ (γ ω '' Icc s t) ∧ μ (γ ω '' Icc s t) < ∞ := by
  have hall : ∀ᵐ ω ∂P, ∀ q r : ℚ, 0 < q → q < r →
      0 < μ (γ ω '' Icc (q : ℝ) (r : ℝ)) ∧
        μ (γ ω '' Icc (q : ℝ) (r : ℝ)) < ∞ := by
    simpa only [ae_all_iff] using h
  exact hall.mono (fun ω hω => all_real_of_all_rational μ (γ ω) hω)

end SLEExactGauge.Intervals

namespace SLEExactGauge.Target

abbrev GaugeIndex (κ : ℝ) (W : WienerLaw) := {e : Entry // ValidEntry κ W e}

def cleanupIndex (κ : ℝ) (W : WienerLaw) (n : ℕ) (hn : 1 ≤ n) : GaugeIndex κ W :=
  ⟨(n, none), hn, trivial⟩

instance (κ : ℝ) (W : WienerLaw) : Nonempty (GaugeIndex κ W) :=
  ⟨cleanupIndex κ W 1 le_rfl⟩

abbrev weights (κ : ℝ) (W : WienerLaw) (i : GaugeIndex κ W) : ℝ := entryValue i.val
abbrev radii (κ : ℝ) (W : WienerLaw) (i : GaugeIndex κ W) : ℝ := entryRadius κ W i.val

lemma weights_pos (κ : ℝ) (W : WienerLaw) (i : GaugeIndex κ W) : 0 < weights κ W i := by
  rcases i with ⟨⟨n, o⟩, hn, _⟩
  cases o with
  | none =>
      change (0 : ℝ) < (n : ℝ)
      exact Nat.cast_pos.mpr (Nat.succ_le_iff.mp hn)
  | some kj =>
      rcases kj with ⟨k, j⟩
      exact zpow_pos (by norm_num : (0 : ℝ) < 2) k

lemma radii_pos (κ : ℝ) (W : WienerLaw) (i : GaugeIndex κ W) : 0 < radii κ W i :=
  Real.exp_pos _

lemma gauge_eq_full (κ : ℝ) (W : WienerLaw) :
    gauge κ W = QuadraticEnvelope.full (weights κ W) (radii κ W) (d κ) := by
  funext r
  unfold gauge QuadraticEnvelope.full
  split_ifs with hr
  · rfl
  · congr 1
    ext v
    constructor
    · rintro ⟨e, he, hv⟩
      exact ⟨⟨e, he⟩, hv.symm⟩
    · rintro ⟨⟨e, he⟩, hv⟩
      exact ⟨e, he, hv.symm⟩

lemma internal_a_pos {κ : ℝ} (hκ : 0 < κ) : 0 < a κ := div_pos (by norm_num) hκ

lemma dimension_pos {κ : ℝ} (hκ : 0 < κ) : 0 < d κ := by
  have ha := internal_a_pos hκ
  unfold d
  positivity

lemma cleanup_radius_le {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw) (n : ℕ) (hn : 1 ≤ n) :
    radii κ W (cleanupIndex κ W n hn) ≤ Real.exp (-(n : ℝ) ^ 2) := by
  unfold radii cleanupIndex entryRadius
  apply Real.exp_le_exp.mpr
  dsimp only
  have ha := internal_a_pos hκ
  have hnonneg : 0 ≤ 2 * a κ * (entryPosition κ W (n, none) : ℝ) *
      ((batchLevel κ W n : ℝ) + (n : ℝ)) := by positivity
  linarith

lemma cleanup_base_le {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw) (n : ℕ) (hn : 1 ≤ n) :
    weights κ W (cleanupIndex κ W n hn) * radii κ W (cleanupIndex κ W n hn) ^ d κ ≤
      (n : ℝ) * Real.exp (-d κ * (n : ℝ) ^ 2) := by
  have hd := dimension_pos hκ
  change (n : ℝ) * radii κ W (cleanupIndex κ W n hn) ^ d κ ≤ _
  calc
    _ ≤ (n : ℝ) * Real.exp (-(n : ℝ) ^ 2) ^ d κ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      exact Real.rpow_le_rpow (radii_pos κ W _).le (cleanup_radius_le hκ W n hn) hd.le
    _ = _ := by rw [← Real.exp_mul]; congr 2; ring

lemma cleanup_small {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw) :
    ∀ ε > 0, ∃ i : GaugeIndex κ W, weights κ W i * radii κ W i ^ d κ < ε := by
  have hd := dimension_pos hκ
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-d κ * (n : ℝ))) atTop (𝓝 0) := by
    convert (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (d κ) hd).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop) using 1
    ext n
    simp only [Function.comp_apply, Real.rpow_one]
  intro ε hε
  obtain ⟨n, hnε, hn⟩ :=
    ((hlim.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 1)).exists
  refine ⟨cleanupIndex κ W n hn, lt_of_le_of_lt ?_ hnε⟩
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  calc
    _ ≤ (n : ℝ) * Real.exp (-d κ * (n : ℝ) ^ 2) := cleanup_base_le hκ W n hn
    _ ≤ (n : ℝ) * Real.exp (-d κ * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hd.le))

theorem gauge_basic_properties {κ : ℝ} (hκ : 0 < κ) (W : WienerLaw) :
    ContinuousOn (gauge κ W) (Ici 0) ∧
    MonotoneOn (gauge κ W) (Ici 0) ∧
    gauge κ W 0 = 0 ∧
    (∀ r : ℝ, 0 ≤ gauge κ W r) ∧
    ∀ C ≥ 1, ∀ r ≥ 0, gauge κ W (C * r) ≤ C ^ 2 * gauge κ W r := by
  rw [gauge_eq_full]
  have hb : ∀ i, 0 ≤ weights κ W i := fun i => (weights_pos κ W i).le
  have hR := radii_pos κ W
  refine ⟨?_, QuadraticEnvelope.full_monoOn hb hR, QuadraticEnvelope.full_zero,
    QuadraticEnvelope.full_nonneg hb hR, fun _ hC _ hr => QuadraticEnvelope.full_scale_le hb hR hC hr⟩
  intro r hr
  obtain rfl | hrpos := (show 0 ≤ r from hr).eq_or_lt
  · exact (QuadraticEnvelope.continuousAt_zero hb hR (cleanup_small hκ W)).continuousWithinAt
  · exact (QuadraticEnvelope.continuousAt_pos hb hR hrpos).continuousWithinAt



theorem hausdorff_arbitrary_covers (h : ℝ → ℝ) (h0 : h 0 = 0) (E : Set ℂ) :
    hausdorff h E =
      ⨆ (δ : ℝ≥0∞) (_ : 0 < δ),
        ⨅ (U : ℕ → Set ℂ) (_ : E ⊆ ⋃ j, U j) (_ : ∀ j, Metric.ediam (U j) ≤ δ),
          ∑' j, if Metric.ediam (U j) = ∞ then ∞
            else ENNReal.ofReal (h (Metric.ediam (U j)).toReal) := by
  let m : ℝ≥0∞ → ℝ≥0∞ := fun r => if r = ∞ then ∞ else ENNReal.ofReal (h r.toReal)
  have hm0 : m 0 = 0 := by simp [m, h0]
  have hnonempty (U : Set ℂ) : (⨆ _ : U.Nonempty, m (Metric.ediam U)) = m (Metric.ediam U) := by
    by_cases hU : U.Nonempty
    · simp [hU]
    · rw [not_nonempty_iff_eq_empty.mp hU]
      simp [hm0]
  change OuterMeasure.mkMetric m E = _
  rw [OuterMeasure.coe_mkMetric, Measure.mkMetric_apply]
  simp only [hnonempty]
  rfl



lemma trace_isChordalSLE (κ : ℝ) {W : WienerLaw} (hW : IsWiener W) :
    IsChordalSLE κ (trace κ) W := by
  refine ⟨W, id, hW, ProbabilityTheory.HasLaw.id, ?_⟩
  exact ae_of_all _ (fun _ _ _ => rfl)

theorem transfer_interval_estimates {κ : ℝ} {h : ℝ → ℝ}
    (hcanonical : ∀ W : WienerLaw, IsWiener W →
      ∀ᵐ b ∂W, ∀ s t : ℝ, 0 < s → s < t →
        0 < hausdorff h (trace κ b '' Icc s t) ∧
        hausdorff h (trace κ b '' Icc s t) < ∞)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : Ω → ℝ → ℂ)
    (hγ : IsChordalSLE κ γ P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 < s → s < t →
      0 < hausdorff h (γ ω '' Icc s t) ∧
      hausdorff h (γ ω '' Icc s t) < ∞ := by
  obtain ⟨W, B, hW, hB, htrace⟩ := hγ
  have hmap := hcanonical W hW
  rw [← hB.map_eq] at hmap
  have hpull := ae_of_ae_map hB.aemeasurable hmap
  filter_upwards [hpull, htrace] with ω hω htr
  intro s t hs hst
  have heq : γ ω '' Icc s t = trace κ (B ω) '' Icc s t := by
    apply Set.image_congr
    intro v hv
    exact htr v (hs.le.trans hv.1)
  rw [heq]
  exact hω s t hs hst



lemma dimension_eq (κ : ℝ) : d κ = 1 + κ / 8 := by
  unfold d a
  field_simp
  ring

lemma dimension_lt_two {κ : ℝ} (hκ8 : κ < 8) : d κ < 2 := by
  rw [dimension_eq κ]
  linarith

lemma multiplicity_positive_bounds (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1 ^ n ≤ moment κ W n) {k : ℤ}
    (hNk : 0 < multiplicity κ W n k) :
    moment κ W 1 / 4 ≤ (2 : ℝ) ^ k ∧ (2 : ℝ) ^ k ≤ threshold κ W n := by
  have hcut : (2 : ℝ) ^ k ≤ threshold κ W n := by
    by_contra hcut
    simp [multiplicity, hcut] at hNk
  have hmn : 0 < moment κ W n := (pow_pos hm1 n).trans_le hJ
  have hfloor : 0 < ⌊(4 : ℝ) ^ n * ((2 : ℝ) ^ k) ^ n / moment κ W n⌋₊ := by
    simpa [multiplicity, hcut] using hNk
  have hw := Nat.floor_pos.mp hfloor
  have hnum : moment κ W n ≤ ((4 : ℝ) * 2 ^ k) ^ n := by
    simpa only [one_mul, mul_pow] using (le_div_iff₀ hmn).1 hw
  have hb : moment κ W 1 ≤ (4 : ℝ) * 2 ^ k :=
    le_of_pow_le_pow_left₀ (by omega) (by positivity) (hJ.trans hnum)
  exact ⟨(div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith), hcut⟩

lemma weights_lower_of_moment_inequalities (κ : ℝ) (W : WienerLaw)
    (hm1 : 0 < moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → moment κ W 1 ^ n ≤ moment κ W n)
    (i : GaugeIndex κ W) : min 1 (moment κ W 1 / 4) ≤ weights κ W i := by
  rcases i with ⟨⟨n, o⟩, hn, ho⟩
  cases o with
  | none =>
      change min 1 (moment κ W 1 / 4) ≤ (n : ℝ)
      exact (min_le_left _ _).trans (by exact_mod_cast hn)
  | some kj =>
      rcases kj with ⟨k, j⟩
      change j < multiplicity κ W n k at ho
      change min 1 (moment κ W 1 / 4) ≤ (2 : ℝ) ^ k
      exact (min_le_right _ _).trans
        (multiplicity_positive_bounds κ W hn hm1 (hJ n hn)
          ((Nat.zero_le j).trans_lt ho)).1

theorem gauge_admissible_of_moment_inequalities {κ : ℝ}
    (hκ0 : 0 < κ) (hκ8 : κ < 8) (W : WienerLaw)
    (hm1 : 0 < moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → moment κ W 1 ^ n ≤ moment κ W n) :
    IsHausdorffGauge (gauge κ W) := by
  rw [gauge_eq_full]
  exact QuadraticEnvelope.isHausdorffGauge
    (c := min 1 (moment κ W 1 / 4))
    (lt_min zero_lt_one (div_pos hm1 (by norm_num)))
    (weights_lower_of_moment_inequalities κ W hm1 hJ)
    (radii_pos κ W) (dimension_pos hκ0).le (dimension_lt_two hκ8).le
    (cleanup_small hκ0 W)

lemma multiplicity_support_finite (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1 ^ n ≤ moment κ W n) :
    Set.Finite {k : ℤ | 0 < multiplicity κ W n k} := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (Set.finite_Icc (⌈Real.log (moment κ W 1 / 4) / Real.log 2⌉ : ℤ)
    (⌊Real.log (threshold κ W n) / Real.log 2⌋ : ℤ)).subset
  intro k hk
  obtain ⟨hlo, hhi⟩ := multiplicity_positive_bounds κ W hn hm1 hJ hk
  constructor
  · apply Int.ceil_le.mpr
    apply (div_le_iff₀ hlog).2
    exact (Real.le_zpow_iff_log_le (div_pos hm1 (by norm_num))
      (by norm_num : (0 : ℝ) < 2)).1 hlo
  · apply Int.le_floor.mpr
    apply (le_div_iff₀ hlog).2
    exact Real.le_log_of_zpow_le (by norm_num : (0 : ℝ) < 2) hhi

lemma repeated_entries_finite (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1 ^ n ≤ moment κ W n) :
    Set.Finite {kj : ℤ × ℕ | kj.2 < multiplicity κ W n kj.1} := by
  have hfin := (multiplicity_support_finite κ W hn hm1 hJ).biUnion
    (fun k _ => (Set.finite_Iio (multiplicity κ W n k)).image (fun j : ℕ => (k, j)))
  apply hfin.subset
  rintro ⟨k, j⟩ hj
  exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨(Nat.zero_le j).trans_lt hj, j, hj, rfl⟩⟩

lemma batch_entries_finite (κ : ℝ) (W : WienerLaw) {n : ℕ}
    (hn : 1 ≤ n) (hm1 : 0 < moment κ W 1)
    (hJ : moment κ W 1 ^ n ≤ moment κ W n) :
    Set.Finite {e : Entry | e.1 = n ∧ ValidEntry κ W e} := by
  have hfin := ((repeated_entries_finite κ W hn hm1 hJ).image
    (fun kj : ℤ × ℕ => (n, (some kj : Option (ℤ × ℕ))))).insert (n, none)
  apply hfin.subset
  rintro ⟨m, o⟩ ⟨heq, hm, ho⟩
  dsimp at heq
  subst m
  cases o with
  | none => exact Or.inl rfl
  | some kj => exact Or.inr ⟨kj, ho, rfl⟩

lemma early_entries_finite (κ : ℝ) (W : WienerLaw)
    (hm1 : 0 < moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → moment κ W 1 ^ n ≤ moment κ W n)
    (n₀ : ℕ) : Set.Finite {e : Entry | ValidEntry κ W e ∧ e.1 < n₀} := by
  have hfin := (Set.finite_Ico 1 n₀).biUnion (fun n hn =>
    batch_entries_finite κ W hn.1 hm1 (hJ n hn.1))
  apply hfin.subset
  intro e he
  exact mem_iUnion.2 ⟨e.1, mem_iUnion.2 ⟨⟨he.1.1, he.2⟩, rfl, he.1⟩⟩

theorem gauge_restore_early_batches (κ : ℝ) (W : WienerLaw)
    (hm1 : 0 < moment κ W 1)
    (hJ : ∀ n : ℕ, 1 ≤ n → moment κ W 1 ^ n ≤ moment κ W n)
    (n₀ : ℕ) (F : ℝ → ℝ) {M C : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ r > 0, F r ≤ M)
    (htail : ∀ e : Entry, ValidEntry κ W e → n₀ ≤ e.1 →
      ∀ r > 0, F r ≤ C * entryCost κ W e r) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ r > 0, F r ≤ C' * gauge κ W r := by
  classical
  have hfin : Set.Finite {i : GaugeIndex κ W | i.val.1 < n₀} := by
    apply ((early_entries_finite κ W hm1 hJ n₀).preimage
      (f := fun i : GaugeIndex κ W => i.val) Subtype.val_injective.injOn).subset
    intro i hi
    exact ⟨i.property, hi⟩
  rw [gauge_eq_full]
  apply QuadraticEnvelope.restore_finite (weights_pos κ W) (radii_pos κ W)
    hfin.toFinset F hM hbound
  intro i hi r hr
  have hn : n₀ ≤ i.val.1 := by
    have hnot : ¬ i.val.1 < n₀ := by simpa using hi
    exact le_of_not_gt hnot
  exact htail i.val i.property hn r hr

end SLEExactGauge.Target

end

end OAI
