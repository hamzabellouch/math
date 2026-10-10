import Mathlib

namespace OAI

section

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced

universe u

structure PatternModel where
  Color : Type u
  [colorFintype : Fintype Color]
  [colorDecidableEq : DecidableEq Color]
  Value : Color → Type u
  [valueMeasurable : ∀ c, MeasurableSpace (Value c)]
  law : ∀ c, Measure (Value c)
  [lawProbability : ∀ c, IsProbabilityMeasure (law c)]
  Label : Type u
  [labelFintype : Fintype Label]
  support : Label → Finset Color
  event : Label → Set (∀ c, Value c)
  eventMeasurable : ∀ a, MeasurableSet (event a)
  dependsOn : ∀ a x y, (∀ c ∈ support a, x c = y c) → (x ∈ event a ↔ y ∈ event a)

attribute [instance] PatternModel.colorFintype PatternModel.colorDecidableEq PatternModel.valueMeasurable
  PatternModel.lawProbability PatternModel.labelFintype

namespace PatternModel

abbrev Sample (P : PatternModel) := ∀ c, P.Value c

noncomputable def measure (P : PatternModel) : Measure P.Sample := Measure.pi P.law

noncomputable def fixCoordinates (P : PatternModel) (K : Finset P.Color)
    (x ω : P.Sample) : P.Sample := by
  classical
  exact fun c => if c ∈ K then x c else ω c

noncomputable def indicator (P : PatternModel) (a : P.Label) (ω : P.Sample) : ℝ :=
  (P.event a).indicator (fun _ => 1) ω

noncomputable def count (P : PatternModel) (ω : P.Sample) : ℝ :=
  ∑ a, P.indicator a ω

noncomputable def fixedExpectation (P : PatternModel) (K : Finset P.Color)
    (x : P.Sample) (f : P.Sample → ℝ) : ℝ :=
  ∫ ω, f (P.fixCoordinates K x ω) ∂P.measure

noncomputable def overlapCount (P : PatternModel) (K₀ K : Finset P.Color)
    (ω : P.Sample) : ℝ := by
  classical
  exact ∑ a, if Disjoint (P.support a \ K₀) K then 0 else P.indicator a ω

end PatternModel

def UniformPatternSupports (P : ℕ → PatternModel.{u}) : Prop :=
  ∃ r : ℕ, ∀ q a, ((P q).support a).card ≤ r

def BoundedInitialColors (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) : Prop :=
  ∃ r₀ : ℕ, ∀ q, (K₀ q).card ≤ r₀

def UniformPatternTotalBound (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) (scale : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
    ∀ K : Finset (P q).Color, K.card ≤ m → ∀ x : (P q).Sample,
      (P q).fixedExpectation (K₀ q ∪ K) x (P q).count ≤ C * scale q

def UniformPatternOverlapBound (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q →
    ∀ K : Finset (P q).Color, K.card ≤ m → ∀ x : (P q).Sample,
      (P q).fixedExpectation (K₀ q ∪ K) x ((P q).overlapCount (K₀ q) K) ≤ C

def UniformPatternMoments (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) : Prop :=
  ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).fixedExpectation (K₀ q) x (fun ω => (P q).count ω ^ s) ≤ C

def UniformCenteredPatternMoments (P : ℕ → PatternModel.{u})
    (K₀ : ∀ q, Finset (P q).Color) : Prop :=
  ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
    ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).fixedExpectation (K₀ q) x
        (fun ω => |(P q).count ω -
          (P q).fixedExpectation (K₀ q) x (P q).count| ^ (2 * s)) ≤ C * (q : ℝ) ^ s

def PatternMomentsResult : Prop :=
  ∀ (P : ℕ → PatternModel.{u}) (K₀ : ∀ q, Finset (P q).Color),
    UniformPatternSupports P → BoundedInitialColors P K₀ →
    (UniformPatternTotalBound P K₀ (fun _ => 1) → UniformPatternMoments P K₀) ∧
    (UniformPatternTotalBound P K₀ (fun q => (q : ℝ)) →
      UniformPatternOverlapBound P K₀ → UniformCenteredPatternMoments P K₀)

end Balanced

end

section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory

namespace Balanced.ConditionalFailure
open scoped _root_.Balanced

theorem joint_eq_cond_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (B : Set Ω) :
    μ.real (A ∩ B) = (cond μ A).real B * μ.real A := by
  have h := congrArg ENNReal.toReal (cond_mul_eq_inter hA B μ)
  simpa only [measureReal_def, ENNReal.toReal_mul] using h.symm

theorem joint_le_cond {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (B : Set Ω) :
    μ.real (A ∩ B) ≤ (cond μ A).real B := by
  rw [joint_eq_cond_mul μ hA B]
  exact mul_le_of_le_one_right (measureReal_nonneg) measureReal_le_one

theorem cond_le_joint_div {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) (B : Set Ω) {a : ℝ}
    (ha : 0 < a) (hprob : a ≤ μ.real A) :
    (cond μ A).real B ≤ μ.real (A ∩ B) / a := by
  apply (le_div_iff₀ ha).2
  rw [joint_eq_cond_mul μ hA B]
  exact mul_le_mul_of_nonneg_left hprob measureReal_nonneg

theorem tendsto_joint_zero_of_cond {ι : Type*} {l : Filter ι}
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i))
    (h : Tendsto (fun i => (cond (μ i) (A i)).real (B i)) l (𝓝 0)) :
    Tendsto (fun i => (μ i).real (A i ∩ B i)) l (𝓝 0) := by
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun i => joint_le_cond (μ i) (hA i) (B i)) h

theorem tendsto_cond_zero_of_joint {ι : Type*} {l : Filter ι}
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsFiniteMeasure (μ i)]
    (A B : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i))
    {a : ℝ} (ha : 0 < a) (hprob : ∀ᶠ i in l, a ≤ (μ i).real (A i))
    (h : Tendsto (fun i => (μ i).real (A i ∩ B i)) l (𝓝 0)) :
    Tendsto (fun i => (cond (μ i) (A i)).real (B i)) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg)
  · filter_upwards [hprob] with i hi
    exact cond_le_joint_div (μ i) (hA i) (B i) ha hi
  · simpa using h.div_const a

theorem joint_preimage_eq_map_cond_mul
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {A : Set Ω}
    (hA : MeasurableSet A) {D : Ω → Ξ} (hD : Measurable D)
    {bad : Set Ξ} (hbad : MeasurableSet bad) :
    μ.real (A ∩ D ⁻¹' bad) = ((cond μ A).map D).real bad * μ.real A := by
  rw [map_measureReal_apply hD hbad]
  exact joint_eq_cond_mul μ hA (D ⁻¹' bad)

theorem tendsto_joint_preimage_zero_of_map_cond
    {ι : Type*} {l : Filter ι} {Ω Ξ : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSpace (Ξ i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ∀ i, Set (Ω i)) (hA : ∀ i, MeasurableSet (A i))
    (D : ∀ i, Ω i → Ξ i) (hD : ∀ i, Measurable (D i))
    (bad : ∀ i, Set (Ξ i)) (hbad : ∀ i, MeasurableSet (bad i))
    (h : Tendsto (fun i => ((cond (μ i) (A i)).map (D i)).real (bad i))
      l (𝓝 0)) :
    Tendsto (fun i => (μ i).real (A i ∩ D i ⁻¹' bad i)) l (𝓝 0) := by
  apply tendsto_joint_zero_of_cond μ A (fun i => D i ⁻¹' bad i) hA
  simpa only [map_measureReal_apply (hD _) (hbad _)] using h

end Balanced.ConditionalFailure

end

section

open MeasureTheory
open scoped ENNReal

namespace Balanced.PatternExposureKernel
open scoped _root_.Balanced

variable {ι : Type*} [DecidableEq ι]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem lmarginal_idempotent (K : Finset ι) (f : (∀ i, X i) → ℝ≥0∞) :
    lmarginal μ K (lmarginal μ K f) = lmarginal μ K f := by
  funext x
  have hconstant (y : (i : K) → X i) :
      lmarginal μ K f (Function.updateFinset x K y) = lmarginal μ K f x := by
    apply lmarginal_congr μ f
    intro i hi
    simp [Function.updateFinset_def, hi]
  change (∫⁻ y : (i : K) → X i,
    lmarginal μ K f (Function.updateFinset x K y)
      ∂Measure.pi (fun i : K => μ i)) = lmarginal μ K f x
  simp_rw [hconstant]
  simp

theorem lmarginal_tower {K L : Finset ι} (hKL : K ⊆ L)
    (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    lmarginal μ L (lmarginal μ K f) = lmarginal μ L f := by
  exact lmarginal_eq_of_subset hKL (hf.lmarginal μ) hf
    (lmarginal_idempotent μ K f)

theorem exposure_tower [Fintype ι] {K₀ K : Finset ι} (hK : K₀ ⊆ K)
    (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    lmarginal μ (Finset.univ \ K₀) (lmarginal μ (Finset.univ \ K) f) =
      lmarginal μ (Finset.univ \ K₀) f := by
  apply lmarginal_tower μ (f := f) (hf := hf)
  intro i hi
  obtain ⟨hiU, hiK⟩ := Finset.mem_sdiff.mp hi
  exact Finset.mem_sdiff.mpr ⟨hiU, fun hi₀ => hiK (hK hi₀)⟩

theorem lintegral_lmarginal [Fintype ι] (K : Finset ι)
    (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, lmarginal μ K f x ∂Measure.pi μ) = ∫⁻ x, f x ∂Measure.pi μ := by
  exact lintegral_eq_of_lmarginal_eq K (hf.lmarginal μ) hf
    (lmarginal_idempotent μ K f)

end Balanced.PatternExposureKernel

end

section

namespace Balanced
open scoped _root_.Balanced

open scoped BigOperators

theorem inv_one_sub_le_exp_two_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - x := by linarith
  have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    apply (inv_le_iff_one_le_mul₀ hpos).2
    nlinarith
  exact hinv.trans (by simpa [add_comm] using Real.add_one_le_exp (2 * x))

theorem avoidance_prod_pos {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, x i ≤ 1 / 2) :
    0 < ∏ i ∈ s, (1 - x i) := by
  exact Finset.prod_pos fun i hi => by linarith [hx i hi]

theorem one_sub_sum_le_avoidance_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hx' : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxa' := hx' a (Finset.mem_insert_self a s)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hxs' : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx' i (Finset.mem_insert_of_mem hi)
    have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxs
    have hmul := mul_le_mul_of_nonneg_left (ih hxs hxs') (show 0 ≤ 1 - x a by linarith)
    simp only [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hxa hsum]

theorem prod_inv_one_sub_le_exp_two_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hx' : ∀ i ∈ s, x i ≤ 1 / 2) :
    (∏ i ∈ s, (1 - x i)⁻¹) ≤ Real.exp (2 * ∑ i ∈ s, x i) := by
  calc
    (∏ i ∈ s, (1 - x i)⁻¹) ≤ ∏ i ∈ s, Real.exp (2 * x i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact inv_nonneg.mpr (by linarith [hx' i hi])
      · intro i hi
        exact inv_one_sub_le_exp_two_mul (hx i hi) (hx' i hi)
    _ = Real.exp (2 * ∑ i ∈ s, x i) := by
      rw [← Real.exp_sum, Finset.mul_sum]

theorem prod_inv_one_sub_le_exp_half {ι : Type*} (t : Finset ι) (x : ι → ℝ)
    (s : ℝ) (hx : ∀ i ∈ t, 0 ≤ x i) (hx' : ∀ i ∈ t, x i ≤ 1 / 2)
    (hs : ∑ i ∈ t, x i ≤ s / 4) :
    (∏ i ∈ t, (1 - x i)⁻¹) ≤ Real.exp (s / 2) := by
  apply (prod_inv_one_sub_le_exp_two_sum t x hx hx').trans
  apply Real.exp_le_exp.mpr
  linarith

end Balanced

end

end OAI
