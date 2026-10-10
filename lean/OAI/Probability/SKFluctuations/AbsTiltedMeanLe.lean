import Mathlib
import OAI.Probability.SKFluctuations.LineDerivatives

namespace OAI

/-! Abs Tilted Mean Le. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

 
theorem abs_tiltedMean_le {m : ℝ} {F A : Ω → ℝ} {B : ℝ}
    (hA : Measurable A) (hi : Integrable (fun x => Real.exp (m * F x)) μ)
    (hb : ∀ x, |A x| ≤ B) : |tiltedMean μ m F A| ≤ B := by
  rw [tiltedMean, abs_div, abs_of_pos (partition_pos m hi), div_le_iff₀ (partition_pos m hi)]
  calc
    |∫ x, A x * Real.exp (m * F x) ∂μ| ≤ ∫ x, |A x * Real.exp (m * F x)| ∂μ :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => A x * Real.exp (m * F x))
    _ ≤ ∫ x, B * Real.exp (m * F x) ∂μ := by
      apply integral_mono (integrable_weighted hi hA hb).norm (hi.const_mul B)
      intro x
      change |A x * Real.exp (m * F x)| ≤ B * Real.exp (m * F x)
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hb x) (Real.exp_nonneg _)
    _ = B * ∫ x, Real.exp (m * F x) ∂μ := integral_const_mul _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

 
def shiftedMean (ν : Measure E) (m : ℝ) (F A : E → ℝ) (x : E) : ℝ :=
  tiltedMean ν m (fun z => F (x + z)) (fun z => A (x + z))

def shiftedContinuation (ν : Measure E) (m : ℝ) (F : E → ℝ) (x : E) : ℝ :=
  Real.log (∫ z, Real.exp (m * F (x + z)) ∂ν) / m

omit [NormedSpace ℝ E] [IsProbabilityMeasure ν] in
 

theorem continuous_tested_partition {F A : E → ℝ} {C : ℝ≥0} {B m : ℝ}
    (hF : LipschitzWith C F) (hA : Continuous A) (hB : 0 ≤ B)
    (hb : ∀ x, |A x| ≤ B)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    Continuous (fun x => ∫ z, A (x + z) * Real.exp (m * F (x + z)) ∂ν) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated
    (bound := fun z => (B * Real.exp (|m| * C)) * Real.exp (m * F (x + z)))
  · exact Eventually.of_forall fun y =>
      ((hA.comp (continuous_const.add continuous_id)).mul
        (Real.continuous_exp.comp ((hF.continuous.comp (continuous_const.add continuous_id)).const_mul m))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    apply Eventually.of_forall
    intro z
    have hv : |F (y + z) - F (x + z)| ≤ C := by
      calc
        _ ≤ C * dist (y + z) (x + z) := hF.dist_le_mul _ _
        _ = C * dist y x := by rw [dist_add_right]
        _ ≤ C := by have := (Metric.mem_ball.mp hy).le; nlinarith [C.coe_nonneg]
    have he : Real.exp (m * F (y + z)) ≤ Real.exp (|m| * C) * Real.exp (m * F (x + z)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have hm' := mul_le_mul_of_nonneg_left hv (abs_nonneg m)
      have hm'' := le_abs_self (m * (F (y + z) - F (x + z)))
      rw [abs_mul] at hm''
      nlinarith
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ B * (Real.exp (|m| * C) * Real.exp (m * F (x + z))) :=
        mul_le_mul (hb _) he (Real.exp_nonneg _) hB
      _ = _ := by ring
  · exact (hi x).const_mul _
  · exact Eventually.of_forall fun z =>
      ((hA.comp (continuous_id.add continuous_const)).mul
        (Real.continuous_exp.comp ((hF.continuous.comp (continuous_id.add continuous_const)).const_mul m))).continuousAt

omit [NormedSpace ℝ E] in
theorem continuous_shiftedMean {F A : E → ℝ} {C : ℝ≥0} {B m : ℝ}
    (hF : LipschitzWith C F) (hA : Continuous A) (hB : 0 ≤ B)
    (hb : ∀ x, |A x| ≤ B)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    Continuous (shiftedMean ν m F A) := by
  have hp : Continuous (fun x => ∫ z, Real.exp (m * F (x + z)) ∂ν) := by
    simpa only [one_mul] using continuous_tested_partition hF
      (A := fun _ => 1) continuous_const (B := 1) (by norm_num) (fun _ => by norm_num) hi
  exact (continuous_tested_partition hF hA hB hb hi).div hp
    (fun x => (partition_pos m (hi x)).ne')

omit [NormedSpace ℝ E] in
theorem continuous_shiftedContinuation {F : E → ℝ} {C : ℝ≥0} {m : ℝ}
    (hF : LipschitzWith C F)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    Continuous (shiftedContinuation ν m F) := by
  have hp : Continuous (fun x => ∫ z, Real.exp (m * F (x + z)) ∂ν) := by
    simpa only [one_mul] using continuous_tested_partition hF
      (A := fun _ => 1) continuous_const (B := 1) (by norm_num) (fun _ => by norm_num) hi
  exact (hp.log (fun x => (partition_pos m (hi x)).ne')).div_const m

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

def BddSmooth : ℕ → (E → ℝ) → Prop
  | 0, f => Continuous f ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B
  | n + 1, f => BddSmooth n f ∧ ∀ v : E, ∃ g : E → ℝ, BddSmooth n g ∧
      ∀ x t, HasDerivAt (fun s : ℝ => f (x + s • v)) (g (x + t • v)) t

theorem BddSmooth.down {n : ℕ} {f : E → ℝ} (h : BddSmooth (n + 1) f) :
    BddSmooth n f := h.1

theorem BddSmooth.continuous {n : ℕ} {f : E → ℝ} (h : BddSmooth n f) : Continuous f := by
  induction n with
  | zero => exact h.1
  | succ n ih => exact ih h.down

theorem BddSmooth.bound {n : ℕ} {f : E → ℝ} (h : BddSmooth n f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B := by
  induction n with
  | zero => exact h.2
  | succ n ih => exact ih h.down

theorem BddSmooth.const (n : ℕ) (c : ℝ) : BddSmooth n (fun _ : E => c) := by
  induction n generalizing c with
  | zero => exact ⟨continuous_const, |c|, abs_nonneg _, fun _ => le_rfl⟩
  | succ n ih =>
    exact ⟨ih c, fun v => ⟨fun _ => 0, ih 0, fun _ t => hasDerivAt_const t c⟩⟩

theorem BddSmooth.add {n : ℕ} {f g : E → ℝ} (hf : BddSmooth n f) (hg : BddSmooth n g) :
    BddSmooth n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero =>
    obtain ⟨B, hB, hb⟩ := hf.bound
    obtain ⟨C, hC, hc⟩ := hg.bound
    exact ⟨hf.continuous.add hg.continuous, B + C, add_nonneg hB hC,
      fun x => (abs_add_le _ _).trans (add_le_add (hb x) (hc x))⟩
  | succ n ih =>
    refine ⟨ih hf.1 hg.1, ?_⟩
    intro v
    obtain ⟨f', hf', hdf⟩ := hf.2 v
    obtain ⟨g', hg', hdg⟩ := hg.2 v
    exact ⟨fun x => f' x + g' x, ih hf' hg', fun x t => (hdf x t).add (hdg x t)⟩

theorem BddSmooth.mul {n : ℕ} {f g : E → ℝ} (hf : BddSmooth n f) (hg : BddSmooth n g) :
    BddSmooth n (fun x => f x * g x) := by
  induction n generalizing f g with
  | zero =>
    obtain ⟨B, hB, hb⟩ := hf.bound
    obtain ⟨C, hC, hc⟩ := hg.bound
    refine ⟨hf.continuous.mul hg.continuous, B * C, mul_nonneg hB hC, ?_⟩
    intro x
    rw [abs_mul]
    exact mul_le_mul (hb x) (hc x) (abs_nonneg _) hB
  | succ n ih =>
    refine ⟨ih hf.1 hg.1, ?_⟩
    intro v
    obtain ⟨f', hf', hdf⟩ := hf.2 v
    obtain ⟨g', hg', hdg⟩ := hg.2 v
    exact ⟨fun x => f' x * g x + f x * g' x,
      (ih hf' hg.1).add (ih hf.1 hg'), fun x t => (hdf x t).mul (hdg x t)⟩

theorem BddSmooth.const_mul {n : ℕ} {f : E → ℝ} (hf : BddSmooth n f) (c : ℝ) :
    BddSmooth n (fun x => c * f x) := (BddSmooth.const n c).mul hf

theorem BddSmooth.neg {n : ℕ} {f : E → ℝ} (hf : BddSmooth n f) :
    BddSmooth n (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)

theorem BddSmooth.sub {n : ℕ} {f g : E → ℝ} (hf : BddSmooth n f) (hg : BddSmooth n g) :
    BddSmooth n (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

 
def PotentialRegularity (n : ℕ) (F : E → ℝ) : Prop :=
  (∃ C : ℝ≥0, LipschitzWith C F) ∧ ∀ v : E, ∃ g : E → ℝ, BddSmooth n g ∧
    ∀ x t, HasDerivAt (fun s : ℝ => F (x + s • v)) (g (x + t • v)) t

theorem PotentialRegularity.down {n : ℕ} {F : E → ℝ}
    (h : PotentialRegularity (n + 1) F) : PotentialRegularity n F := by
  refine ⟨h.1, fun v => ?_⟩
  obtain ⟨g, hg, hdg⟩ := h.2 v
  exact ⟨g, hg.down, hdg⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

theorem hasDerivAt_shiftedMean {F F₁ A A₁ : E → ℝ} {C B m : ℝ} {v : E}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF : Continuous F) (hF₁ : Continuous F₁) (hA : Continuous A) (hA₁ : Continuous A₁)
    (hdF : ∀ x t, HasDerivAt (fun s : ℝ => F (x + s • v)) (F₁ (x + t • v)) t)
    (hdA : ∀ x t, HasDerivAt (fun s : ℝ => A (x + s • v)) (A₁ (x + t • v)) t)
    (hbF : ∀ x, |F₁ x| ≤ C) (hbA : ∀ x, |A x| ≤ B) (hbA₁ : ∀ x, |A₁ x| ≤ B)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => shiftedMean ν m F A (x + s • v))
      (SKFluctuations.Hierarchy.shiftedMean ν m F A₁ (x + t • v) + m *
        (SKFluctuations.Hierarchy.shiftedMean ν m F (fun y => A y * F₁ y) (x + t • v) -
          SKFluctuations.Hierarchy.shiftedMean ν m F A (x + t • v) * SKFluctuations.Hierarchy.shiftedMean ν m F F₁ (x + t • v))) t := by
  exact hasDerivAt_tiltedMean
    (F := fun s z => F (x + s • v + z)) (F₁ := fun s z => F₁ (x + s • v + z))
    (A := fun s z => A (x + s • v + z)) (A₁ := fun s z => A₁ (x + s • v + z)) hC hB
    (fun s => (hF.comp (continuous_const.add continuous_id)).measurable)
    (fun s => (hF₁.comp (continuous_const.add continuous_id)).measurable)
    (fun s => (hA.comp (continuous_const.add continuous_id)).measurable)
    (fun s => (hA₁.comp (continuous_const.add continuous_id)).measurable)
    (fun s z => by simpa only [add_assoc, add_comm z] using hdF (x + z) s)
    (fun s z => by simpa only [add_assoc, add_comm z] using hdA (x + z) s)
    (fun s z => hbF _) (fun s z => hbA _) (fun s z => hbA₁ _) m t (hi _)

 

theorem BddSmooth.shiftedMean {n : ℕ} {F A : E → ℝ} {m : ℝ}
    (hF : PotentialRegularity n F) (hA : BddSmooth n A)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    BddSmooth n (SKFluctuations.Hierarchy.shiftedMean ν m F A) := by
  induction n generalizing A with
  | zero =>
    obtain ⟨C, hC⟩ := hF.1
    obtain ⟨B, hB, hb⟩ := hA.bound
    exact ⟨continuous_shiftedMean hC hA.continuous hB hb hi, B, hB,
      fun x => abs_tiltedMean_le
        (hA.continuous.comp (continuous_const.add continuous_id)).measurable (hi x)
        (fun z => hb _)⟩
  | succ n ih =>
    have hf := hF.down
    refine ⟨ih hf hA.down, ?_⟩
    intro v
    obtain ⟨F₁, hF₁, hdF⟩ := hF.2 v
    obtain ⟨A₁, hA₁, hdA⟩ := hA.2 v
    refine ⟨fun x => SKFluctuations.Hierarchy.shiftedMean ν m F A₁ x + m *
      (SKFluctuations.Hierarchy.shiftedMean ν m F (fun y => A y * F₁ y) x -
        SKFluctuations.Hierarchy.shiftedMean ν m F A x * SKFluctuations.Hierarchy.shiftedMean ν m F F₁ x), ?_, ?_⟩
    · exact (ih hf hA₁).add (((ih hf (hA.down.mul hF₁.down)).sub
        ((ih hf hA.down).mul (ih hf hF₁.down))).const_mul m)
    · obtain ⟨C, hC, hbC⟩ := hF₁.bound
      obtain ⟨B₀, hB₀, hbB₀⟩ := hA.bound
      obtain ⟨B₁, hB₁, hbB₁⟩ := hA₁.bound
      obtain ⟨K, hK⟩ := hF.1
      exact hasDerivAt_shiftedMean hC (add_nonneg hB₀ hB₁)
        hK.continuous hF₁.continuous hA.continuous hA₁.continuous hdF hdA
        hbC (fun x => (hbB₀ x).trans (by linarith))
        (fun x => (hbB₁ x).trans (by linarith)) hi

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem lipschitzWith_shiftedContinuation {F : E → ℝ} {C : ℝ≥0} {m : ℝ}
    (hF : LipschitzWith C F) (hm : 0 < m)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    LipschitzWith C (shiftedContinuation ν m F) := by
  have hle (x y : E) : shiftedContinuation ν m F x - shiftedContinuation ν m F y ≤ C * dist x y := by
    have hz : (∫ z, Real.exp (m * F (x + z)) ∂ν) ≤
        Real.exp (m * (C * dist x y)) * (∫ z, Real.exp (m * F (y + z)) ∂ν) := by
      rw [← integral_const_mul]
      apply integral_mono (hi x) ((hi y).const_mul _)
      intro z
      change Real.exp (m * F (x + z)) ≤ Real.exp (m * (C * dist x y)) * Real.exp (m * F (y + z))
      rw [← Real.exp_add, Real.exp_le_exp]
      have hd : F (x + z) - F (y + z) ≤ C * dist x y := by
        have ht := (le_abs_self _).trans (hF.dist_le_mul (x + z) (y + z))
        simpa only [dist_add_right] using ht
      nlinarith
    have hl := Real.log_le_log (partition_pos m (hi x)) hz
    rw [Real.log_mul (Real.exp_ne_zero _) (partition_pos m (hi y)).ne', Real.log_exp] at hl
    dsimp [shiftedContinuation]
    apply (sub_le_iff_le_add).mpr
    calc
      _ ≤ (m * (C * dist x y) + Real.log (∫ z, Real.exp (m * F (y + z)) ∂ν)) / m :=
        (div_le_div_iff_of_pos_right hm).mpr hl
      _ = _ := by field_simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  exact ⟨by have := hle y x; rw [dist_comm y x] at this; linarith, hle x y⟩

 

theorem PotentialRegularity.shiftedContinuation {n : ℕ} {F : E → ℝ} {m : ℝ}
    (hF : PotentialRegularity n F) (hm : 0 < m)
    (hi : ∀ x, Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    PotentialRegularity n (shiftedContinuation ν m F) := by
  obtain ⟨C, hC⟩ := hF.1
  refine ⟨⟨C, lipschitzWith_shiftedContinuation hC hm hi⟩, ?_⟩
  intro v
  obtain ⟨F₁, hF₁, hdF⟩ := hF.2 v
  refine ⟨shiftedMean ν m F F₁, hF₁.shiftedMean hF hi, ?_⟩
  obtain ⟨B, hB, hb⟩ := hF₁.bound
  intro x t
  exact hasDerivAt_continuation
    (F := fun s z => F (x + s • v + z)) (F₁ := fun s z => F₁ (x + s • v + z)) hB hm.ne'
    (fun s => (hC.continuous.comp (continuous_const.add continuous_id)).measurable)
    (fun s => (hF₁.continuous.comp (continuous_const.add continuous_id)).measurable)
    (fun s z => by simpa only [add_assoc, add_comm z] using hdF (x + z) s)
    (fun s z => hb _) t (hi _)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BddSmooth.sum {ι : Type*} {n : ℕ} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, BddSmooth n (f i)) : BddSmooth n (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BddSmooth.const n (0 : ℝ)
  | @insert i s his ih =>
    simpa only [Finset.sum_insert his] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

variable {S : Type*} [Fintype S] [Nonempty S]

def spinPartition (w : S → ℝ) (φ : S → E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∑ s, w s * Real.exp (φ s x)

def spinWeight (w : S → ℝ) (φ : S → E →L[ℝ] ℝ) (x : E) (s : S) : ℝ :=
  w s * Real.exp (φ s x) / spinPartition w φ x

def spinLogPartition (w : S → ℝ) (φ : S → E →L[ℝ] ℝ) (x : E) : ℝ :=
  Real.log (spinPartition w φ x)

theorem spinPartition_pos {w : S → ℝ} (hw : ∀ s, 0 < w s) (φ : S → E →L[ℝ] ℝ) (x : E) :
    0 < spinPartition w φ x := by
  exact Finset.sum_pos (fun s _ => mul_pos (hw s) (Real.exp_pos _)) Finset.univ_nonempty

omit [Nonempty S] in
theorem continuous_spinPartition (w : S → ℝ) (φ : S → E →L[ℝ] ℝ) :
    Continuous (spinPartition w φ) := by
  exact continuous_finsetSum _ (fun s _ => (Real.continuous_exp.comp (φ s).continuous).const_mul _)

theorem continuous_spinWeight {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (s : S) : Continuous (fun x => spinWeight w φ x s) :=
  ((Real.continuous_exp.comp (φ s).continuous).const_mul _).div
    (continuous_spinPartition w φ) (fun x => (spinPartition_pos hw φ x).ne')

theorem spinWeight_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (x : E) (s : S) : 0 ≤ spinWeight w φ x s :=
  div_nonneg (mul_nonneg (hw s).le (Real.exp_nonneg _)) (spinPartition_pos hw φ x).le

theorem sum_spinWeight {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (x : E) : ∑ s, spinWeight w φ x s = 1 := by
  simp only [spinWeight, ← Finset.sum_div]
  exact div_self (spinPartition_pos hw φ x).ne'

theorem spinWeight_le_one {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (x : E) (s : S) : spinWeight w φ x s ≤ 1 := by
  rw [← sum_spinWeight hw φ x]
  exact Finset.single_le_sum (fun i _ => spinWeight_nonneg hw φ x i) (Finset.mem_univ s)

theorem line_derivative_linear (φ : E →L[ℝ] ℝ) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) (φ v) t := by
  simp only [map_add, map_smul, smul_eq_mul]
  simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const (φ v)).const_add (φ x)

omit [Nonempty S] in
theorem hasDerivAt_spinPartition (w : S → ℝ) (φ : S → E →L[ℝ] ℝ) (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => spinPartition w φ (x + s • v))
      (∑ s, w s * (Real.exp (φ s (x + t • v)) * φ s v)) t := by
  simpa only [spinPartition, Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ) (fun s _ => ((line_derivative_linear (φ s) x v t).exp).const_mul (w s))

theorem hasDerivAt_spinWeight {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (s : S) (x v : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => spinWeight w φ (x + r • v) s)
      (spinWeight w φ (x + t • v) s *
        (φ s v - ∑ j, spinWeight w φ (x + t • v) j * φ j v)) t := by
  have h := (((line_derivative_linear (φ s) x v t).exp).const_mul (w s)).div
    (hasDerivAt_spinPartition w φ x v t) (spinPartition_pos hw φ (x + t • v)).ne'
  apply h.congr_deriv
  simp only [spinWeight, div_mul_eq_mul_div, ← Finset.sum_div]
  have he : (∑ j, w j * (Real.exp (φ j (x + t • v)) * φ j v)) =
      ∑ j, w j * Real.exp (φ j (x + t • v)) * φ j v := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  field_simp [(spinPartition_pos hw φ (x + t • v)).ne']

theorem bddSmooth_spinWeight {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (n : ℕ) (s : S) : BddSmooth n (fun x => spinWeight w φ x s) := by
  induction n generalizing s with
  | zero =>
    refine ⟨continuous_spinWeight hw φ s, 1, by norm_num, ?_⟩
    intro x
    rw [abs_of_nonneg (spinWeight_nonneg hw φ x s)]
    exact spinWeight_le_one hw φ x s
  | succ n ih =>
    refine ⟨ih s, fun v => ?_⟩
    refine ⟨fun x => spinWeight w φ x s * (φ s v - ∑ j, spinWeight w φ x j * φ j v), ?_, ?_⟩
    · apply (ih s).mul
      apply (BddSmooth.const n (φ s v)).sub
      exact BddSmooth.sum Finset.univ (fun j _ => (ih j).mul (BddSmooth.const n (φ j v)))
    · exact hasDerivAt_spinWeight hw φ s (v := v)

theorem hasDerivAt_spinLogPartition {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (x v : E) (t : ℝ) :
    HasDerivAt (fun r : ℝ => spinLogPartition w φ (x + r • v))
      (∑ s, spinWeight w φ (x + t • v) s * φ s v) t := by
  have h := (hasDerivAt_spinPartition w φ x v t).log (spinPartition_pos hw φ (x + t • v)).ne'
  apply h.congr_deriv
  simp only [spinWeight, div_mul_eq_mul_div, ← Finset.sum_div, mul_assoc]

theorem lipschitzWith_spinLogPartition {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) :
    LipschitzWith (∑ s, ‖φ s‖₊) (spinLogPartition w φ) := by
  let C : ℝ≥0 := ∑ s, ‖φ s‖₊
  have hφ (s : S) : LipschitzWith C (φ s) :=
    (φ s).lipschitzWith.weaken (Finset.single_le_sum (fun j _ => (zero_le (a := ‖φ j‖₊))) (Finset.mem_univ s))
  have hle (x y : E) : spinLogPartition w φ x - spinLogPartition w φ y ≤ C * dist x y := by
    have hz : spinPartition w φ x ≤ Real.exp (C * dist x y) * spinPartition w φ y := by
      rw [spinPartition, spinPartition, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      have hd : φ s x ≤ C * dist x y + φ s y := by
        have h := (le_abs_self _).trans ((hφ s).dist_le_mul x y)
        linarith
      have he := Real.exp_le_exp.mpr hd
      rw [Real.exp_add] at he
      have h := mul_le_mul_of_nonneg_left he (hw s).le
      nlinarith
    have hl := Real.log_le_log (spinPartition_pos hw φ x) hz
    rw [Real.log_mul (Real.exp_ne_zero _) (spinPartition_pos hw φ y).ne', Real.log_exp] at hl
    exact sub_le_iff_le_add.mpr hl
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  exact ⟨by have := hle y x; rw [dist_comm y x] at this; linarith, hle x y⟩

 

theorem potentialRegularity_spinLogPartition {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (φ : S → E →L[ℝ] ℝ) (n : ℕ) : PotentialRegularity n (spinLogPartition w φ) := by
  refine ⟨⟨_, lipschitzWith_spinLogPartition hw φ⟩, fun v => ?_⟩
  exact ⟨fun x => ∑ s, spinWeight w φ x s * φ s v,
    BddSmooth.sum Finset.univ (fun s _ => (bddSmooth_spinWeight hw φ n s).mul
      (BddSmooth.const n (φ s v))), fun x t => hasDerivAt_spinLogPartition hw φ x v t⟩

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

 

def ExponentialIncrement (ν : Measure E) : Prop :=
  ∀ c : ℝ, Integrable (fun z : E => Real.exp (c * ‖z‖)) ν

theorem ExponentialIncrement.integrable_shift {ν : Measure E}
    (hν : ExponentialIncrement ν) {F : E → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (m : ℝ) (x : E) :
    Integrable (fun z => Real.exp (m * F (x + z))) ν := by
  apply ((hν (|m| * C)).const_mul (Real.exp (m * F x))).mono'
    (Real.continuous_exp.comp ((hF.continuous.comp
      (continuous_const.add continuous_id)).const_mul m)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖Real.exp (m * F (x + z))‖ ≤ Real.exp (m * F x) * Real.exp (|m| * C * ‖z‖)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd : |F (x + z) - F x| ≤ C * ‖z‖ := by
    simpa only [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs] using hF.dist_le_mul (x + z) x
  have h := mul_le_mul_of_nonneg_left hd (abs_nonneg m)
  have he := le_abs_self (m * (F (x + z) - F x))
  rw [abs_mul] at he
  nlinarith

theorem integrable_exp_mul_abs_gaussianReal (c : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (gaussianReal 0 v) := by
  apply ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) c).add
    (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-c))).mono'
  · exact (Real.continuous_exp.comp (continuous_abs.const_mul c)).aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change Real.exp (c * |z|) ≤ Real.exp (c * z) + Real.exp (-c * z)
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hz, mul_neg, neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)

 

theorem exponentialIncrement_gaussian {ι : Type*} [Fintype ι]
    (v : ι → ℝ≥0) : ExponentialIncrement (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  intro c
  have hi := Integrable.fintype_prod (fun i => integrable_exp_mul_abs_gaussianReal |c| (v i))
  have heq (z : ι → ℝ) : (∏ i, Real.exp (|c| * |z i|)) =
      Real.exp (|c| * ∑ i, |z i|) := by rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [heq] at hi
  apply hi.mono' (Real.continuous_exp.comp (continuous_norm.const_mul c)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖Real.exp (c * ‖z‖)‖ ≤ Real.exp (|c| * ∑ i, |z i|)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hn : ‖z‖ ≤ ∑ i, |z i| := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg (z i))).mpr
    intro i
    exact Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i)
  calc
    c * ‖z‖ ≤ |c| * ‖z‖ := mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _)
    _ ≤ |c| * ∑ i, |z i| := mul_le_mul_of_nonneg_left hn (abs_nonneg _)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {F A B : E → ℝ} {m : ℝ}

omit [IsProbabilityMeasure ν] in
theorem BddSmooth.integrable_shifted_weighted {n : ℕ} (hA : BddSmooth n A)
    {x : E} (hi : Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    Integrable (fun z => A (x + z) * Real.exp (m * F (x + z))) ν := by
  obtain ⟨C, _, hb⟩ := hA.bound
  exact integrable_weighted hi
    (hA.continuous.comp (continuous_const.add continuous_id)).measurable (fun z => hb _)

omit [IsProbabilityMeasure ν] in
theorem shiftedMean_add (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    {x : E} (hi : Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    shiftedMean ν m F (fun y => A y + B y) x =
      shiftedMean ν m F A x + shiftedMean ν m F B x := by
  simp only [shiftedMean, tiltedMean, add_mul]
  rw [integral_add (hA.integrable_shifted_weighted hi) (hB.integrable_shifted_weighted hi), add_div]

omit [IsProbabilityMeasure ν] in
theorem shiftedMean_sub (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    {x : E} (hi : Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    shiftedMean ν m F (fun y => A y - B y) x =
      shiftedMean ν m F A x - shiftedMean ν m F B x := by
  simp only [shiftedMean, tiltedMean, sub_mul]
  rw [integral_sub (hA.integrable_shifted_weighted hi) (hB.integrable_shifted_weighted hi), sub_div]

omit [NormedSpace ℝ E] [BorelSpace E] [IsProbabilityMeasure ν] in
theorem shiftedMean_const_mul (c : ℝ) (x : E) :
    shiftedMean ν m F (fun y => c * A y) x = c * shiftedMean ν m F A x := by
  simp only [shiftedMean, tiltedMean, mul_assoc, integral_const_mul, mul_div_assoc]

theorem shiftedMean_mono (hA : BddSmooth 0 A) (hB : BddSmooth 0 B)
    (hab : ∀ y, A y ≤ B y) {x : E}
    (hi : Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    shiftedMean ν m F A x ≤ shiftedMean ν m F B x := by
  apply div_le_div_of_nonneg_right _ (partition_pos m hi).le
  exact integral_mono (hA.integrable_shifted_weighted hi) (hB.integrable_shifted_weighted hi)
    (fun z => mul_le_mul_of_nonneg_right (hab _) (Real.exp_nonneg _))

omit [NormedSpace ℝ E] [BorelSpace E] in
theorem shiftedMean_nonneg (hA : ∀ y, 0 ≤ A y) {x : E}
    (hi : Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    0 ≤ shiftedMean ν m F A x := tiltedMean_nonneg hi (fun _z => hA _)

theorem shiftedMean_square_sub_nonneg (hF : Continuous F) (hA : BddSmooth 0 A) {x : E}
    (hi : Integrable (fun z => Real.exp (m * F (x + z))) ν) :
    0 ≤ shiftedMean ν m F (fun y => (A y)^2) x - (shiftedMean ν m F A x)^2 := by
  obtain ⟨C, _, hb⟩ := hA.bound
  exact tiltedMean_square_sub_nonneg
    (hF.comp (continuous_const.add continuous_id)).measurable
    (hA.continuous.comp (continuous_const.add continuous_id)).measurable hi (fun z => hb _)

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

structure SourceContinuation (v : E) (a : ℝ) where
  potential : E → ℝ
  mean : E → ℝ
  secondMoment : E → ℝ
  hessian : E → ℝ
  regular : ∀ n, PotentialRegularity n potential
  mean_smooth : ∀ n, BddSmooth n mean
  second_smooth : ∀ n, BddSmooth n secondMoment
  hessian_smooth : ∀ n, BddSmooth n hessian
  first : ∀ x t, HasDerivAt (fun s : ℝ => potential (x + s • v)) (mean (x + t • v)) t
  second : ∀ x t, HasDerivAt (fun s : ℝ => mean (x + s • v)) (hessian (x + t • v)) t
  mass_nonneg : 0 ≤ a
  mass_le_one : a ≤ 1
  variance_nonneg : ∀ x, 0 ≤ secondMoment x - (mean x)^2
  lower : ∀ x, a * (secondMoment x - (mean x)^2) ≤ hessian x
  upper : ∀ x, hessian x ≤ secondMoment x - (mean x)^2

variable [MeasurableSpace E] [BorelSpace E]

 

def SourceContinuation.step {v : E} {a : ℝ} (T : SourceContinuation v a)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν : ExponentialIncrement ν)
    (m : ℝ) (hm : 0 < m) (hma : m ≤ a) : SourceContinuation v m := by
  let C := Classical.choose (T.regular 0).1
  have hC : LipschitzWith C T.potential := Classical.choose_spec (T.regular 0).1
  have hi (x : E) := hν.integrable_shift hC m x
  let M := shiftedMean ν m T.potential T.mean
  let Q := shiftedMean ν m T.potential T.secondMoment
  let V := fun x => shiftedMean ν m T.potential (fun y => (T.mean y)^2) x - (M x)^2
  let H := fun x => shiftedMean ν m T.potential T.hessian x + m * V x
  have hMs (n : ℕ) : BddSmooth n M := (T.mean_smooth n).shiftedMean (T.regular n) hi
  have hQs (n : ℕ) : BddSmooth n Q := (T.second_smooth n).shiftedMean (T.regular n) hi
  have hMsq (n : ℕ) : BddSmooth n (fun y => (T.mean y)^2) := by
    simpa only [pow_two] using (T.mean_smooth n).mul (T.mean_smooth n)
  have hVs (n : ℕ) : BddSmooth n V := by
    simpa only [V, pow_two] using ((hMsq n).shiftedMean (T.regular n) hi).sub ((hMs n).mul (hMs n))
  have hHs (n : ℕ) : BddSmooth n H :=
    ((T.hessian_smooth n).shiftedMean (T.regular n) hi).add ((hVs n).const_mul m)
  have hV (x : E) : 0 ≤ V x := shiftedMean_square_sub_nonneg hC.continuous (T.mean_smooth 0) (hi x)
  let K := fun y => T.secondMoment y - (T.mean y)^2
  have hKs : BddSmooth 0 K := (T.second_smooth 0).sub (hMsq 0)
  have hK (x : E) : 0 ≤ shiftedMean ν m T.potential K x :=
    shiftedMean_nonneg T.variance_nonneg (hi x)
  have hKeq (x : E) : shiftedMean ν m T.potential K x =
      Q x - shiftedMean ν m T.potential (fun y => (T.mean y)^2) x :=
    shiftedMean_sub (T.second_smooth 0) (hMsq 0) (hi x)
  have hul (x : E) : shiftedMean ν m T.potential T.hessian x ≤
      shiftedMean ν m T.potential K x :=
    shiftedMean_mono (T.hessian_smooth 0) hKs T.upper (hi x)
  have hll (x : E) : m * shiftedMean ν m T.potential K x ≤
      shiftedMean ν m T.potential T.hessian x := by
    rw [← shiftedMean_const_mul]
    apply shiftedMean_mono (hKs.const_mul m) (T.hessian_smooth 0) _ (hi x)
    intro y
    exact (mul_le_mul_of_nonneg_right hma (T.variance_nonneg y)).trans (T.lower y)
  refine { potential := shiftedContinuation ν m T.potential
           mean := M, secondMoment := Q, hessian := H
           regular := fun n => (T.regular n).shiftedContinuation hm hi
           mean_smooth := hMs, second_smooth := hQs, hessian_smooth := hHs
           mass_nonneg := hm.le, mass_le_one := hma.trans T.mass_le_one
           first := ?_, second := ?_, variance_nonneg := ?_, lower := ?_, upper := ?_ }
  · obtain ⟨B, hB, hb⟩ := (T.mean_smooth 0).bound
    intro x t
    exact hasDerivAt_continuation
      (F := fun s z => T.potential (x + s • v + z))
      (F₁ := fun s z => T.mean (x + s • v + z)) hB hm.ne'
      (fun s => (hC.continuous.comp (continuous_const.add continuous_id)).measurable)
      (fun s => ((T.mean_smooth 0).continuous.comp (continuous_const.add continuous_id)).measurable)
      (fun s z => by simpa only [add_assoc, add_comm z] using T.first (x + z) s)
      (fun s z => hb _) t (hi _)
  · obtain ⟨B, hB, hb⟩ := (T.mean_smooth 0).bound
    obtain ⟨D, hD, hd⟩ := (T.hessian_smooth 0).bound
    intro x t
    simpa only [H, V, M, pow_two] using hasDerivAt_shiftedMean hB (add_nonneg hB hD)
      hC.continuous (T.mean_smooth 0).continuous (T.mean_smooth 0).continuous
      (T.hessian_smooth 0).continuous T.first T.second hb
      (fun y => (hb y).trans (by linarith)) (fun y => (hd y).trans (by linarith)) hi x t
  · intro x
    have hv := hV x
    have hk := hK x
    rw [hKeq x] at hk
    dsimp [V] at hv
    linarith
  · intro x
    have hl := hll x
    rw [hKeq x] at hl
    dsimp [H, V]
    nlinarith
  · intro x
    have hu := hul x
    rw [hKeq x] at hu
    have hv := hV x
    have hm1 : m ≤ 1 := hma.trans T.mass_le_one
    dsimp [H, V] at *
    nlinarith

end SKFluctuations.Hierarchy

end

end OAI
