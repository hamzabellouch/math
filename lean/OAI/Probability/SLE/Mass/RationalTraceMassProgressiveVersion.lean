import OAI.Probability.SLE.Mass.RationalTraceMassAdaptedVersion
import OAI.Probability.SLE.Mass.CanonicalRadonLimit
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! A single reconstruction from rational left samples is progressive in
the uncompleted filtration and agrees at every time on the common good set. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def leftRationalSample (n : ℕ) (t : ℝ≥0) : ℚ :=
  (⌊(t:ℝ)*((n:ℝ)+1)⌋₊ : ℚ)/((n:ℚ)+1)

lemma leftRationalSample_nonneg (n : ℕ) (t : ℝ≥0) : 0 ≤ leftRationalSample n t := by
  unfold leftRationalSample
  positivity

lemma leftRationalSample_le (n : ℕ) (t : ℝ≥0) : (leftRationalSample n t : ℝ) ≤ t := by
  unfold leftRationalSample
  push_cast
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
  exact Nat.floor_le (mul_nonneg t.coe_nonneg (by positivity))

lemma leftRationalSample_tendsto (t : ℝ≥0) :
    Tendsto (fun n => (leftRationalSample n t : ℝ)) atTop (𝓝 (t:ℝ)) := by
  have h := (tendsto_nat_floor_mul_div_atTop t.coe_nonneg).comp
    (tendsto_atTop_add_const_right atTop (1:ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa only [leftRationalSample,Rat.cast_div,Rat.cast_natCast,Rat.cast_add,Rat.cast_one,
    Function.comp_def] using h

lemma leftRationalSample_measurable (n : ℕ) : Measurable (leftRationalSample n) := by
  exact (measurable_of_countable (fun k : ℕ => (k:ℚ)/((n:ℚ)+1))).comp
    ((NNReal.continuous_coe.measurable.mul_const ((n:ℝ)+1)).nat_floor)

def rationalRadonExtension {Ω : Type*} (μ : ℚ → Ω → Measure upperHalfPlane)
    (t : ℝ≥0) (ω : Ω) : Measure upperHalfPlane :=
  canonicalRadonLimit (fun n => μ (leftRationalSample n t) ω)

theorem rationalRadonExtension_regular {Ω : Type*}
    (μ : ℚ → Ω → Measure upperHalfPlane) (t : ℝ≥0) (ω : Ω) :
    (rationalRadonExtension μ t ω).Regular ∧
      IsFiniteMeasureOnCompacts (rationalRadonExtension μ t ω) := by
  have h : (rationalRadonExtension μ t ω).Regular :=
    canonicalRadonLimit_regular (fun n => μ (leftRationalSample n t) ω)
  let := h
  exact ⟨h,inferInstance⟩

theorem rationalRadonExtension_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (μ : ℚ → Ω → Measure upperHalfPlane)
    (hμr : ∀ q ω, (μ q ω).Regular)
    (hμm : ∀ q : ℚ, 0 ≤ q → Measurable[ℱ (q : ℝ).toNNReal] (μ q)) :
    IsProgressive ℱ (rationalRadonExtension μ) := by
  classical
  intro T
  let : MeasurableSpace Ω := ℱ T
  have hm (n : ℕ) : Measurable (fun p : Iic T × Ω => μ (leftRationalSample n p.1) p.2) := by
    let ν (q : ℚ) (ω : Ω) := if 0 ≤ q ∧ (q:ℝ) ≤ T then μ q ω else 0
    have hνm (q : ℚ) : Measurable (ν q) := by
      by_cases hq : 0 ≤ q ∧ (q:ℝ) ≤ T
      · have hqt : (q:ℝ).toNNReal ≤ T := by
          simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hq.2
        simpa only [ν,ite_eq_left hq] using (hμm q hq.1).mono (ℱ.mono hqt) le_rfl
      · simpa only [ν,ite_eq_right hq] using (measurable_const : Measurable (fun _ : Ω => (0 : Measure upperHalfPlane)))
    have hv : Measurable (fun p : ℚ × Ω => ν p.1 p.2) :=
      measurable_from_prod_countable_right hνm
    have hq : Measurable (fun p : Iic T × Ω => (leftRationalSample n p.1,p.2)) :=
      ((leftRationalSample_measurable n).comp
        (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd
    have h := hv.comp hq
    convert h using 1
    funext p
    dsimp only [Function.comp_def,ν]
    rw [ite_eq_left ⟨leftRationalSample_nonneg n p.1,
      (leftRationalSample_le n p.1).trans (NNReal.coe_le_coe.mpr p.1.property)⟩]
  apply canonicalRadonLimit_measurable (fun (n : ℕ) (p : Iic T × Ω) => μ (leftRationalSample n p.1) p.2)
  · intro n p
    let := hμr (leftRationalSample n p.1) p.2
    infer_instance
  · intro n f
    exact measurable_halfPlane_compact_test_integral _ (hm n)
      (fun p => hμr (leftRationalSample n p.1) p.2) f

theorem rationalRadonExtension_common_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℚ → Ω → Measure upperHalfPlane) (M : ℝ → Ω → Measure upperHalfPlane)
    (hMr : ∀ t ω, (M t ω).Regular)
    (hcont : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t ω))
    (hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, M q ω = μ q ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, rationalRadonExtension μ t ω = M t ω := by
  filter_upwards [hcont,hrat] with ω hc hr
  intro t
  apply canonicalRadonLimit_identified _ (M t ω)
  refine ⟨hMr t ω,?_⟩
  intro f
  simpa only [Function.comp_def,hr] using
    (hc f).continuousAt.tendsto.comp (leftRationalSample_tendsto t)

end SLEExactGauge

end

end OAI
