import Mathlib
import OAI.Geometry.WeakHessian.Geodesics.MidpointSigmaLower

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian

variable {X : Type*} [MeasurableSpace X]

def FiniteEntropy (m μ : Measure X) : Prop :=
  μ ≪ m ∧ Integrable (llr μ m) μ

def entropyReal (m μ : Measure X) : ℝ := ∫ x, llr μ m x ∂μ

lemma entropyReal_eq_integral_density {m μ : Measure X} [SigmaFinite μ]
    [μ.HaveLebesgueDecomposition m] (h : μ ≪ m) :
    entropyReal m μ = ∫ x, (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal ∂m := by
  exact (integral_rnDeriv_mul_log h).symm

lemma absolutelyContinuous_exponentialMeasure {m μ : Measure X} {V : X → ℝ}
    (hV : Measurable V) : μ ≪ exponentialMeasure m V ↔ μ ≪ m := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) := by fun_prop
  have hpos : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ 0 :=
    ae_of_all m fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  exact ⟨fun h => h.trans (withDensity_absolutelyContinuous _ _),
    fun h => h.trans (withDensity_absolutelyContinuous' hmeas.aemeasurable hpos)⟩

lemma llr_exponentialMeasure {m μ : Measure X} [SigmaFinite m] [IsFiniteMeasure μ]
    {V : X → ℝ} (hμ : μ ≪ m) (hV : Measurable V) :
    llr μ (exponentialMeasure m V) =ᵐ[μ] fun x => llr μ m x - V x := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (V x))) := by fun_prop
  have hpos : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ 0 :=
    ae_of_all m fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have htop : ∀ᵐ x ∂m, ENNReal.ofReal (Real.exp (V x)) ≠ ∞ :=
    ae_of_all m fun _ => ENNReal.ofReal_ne_top
  have hrn := Measure.rnDeriv_withDensity_right μ m hmeas.aemeasurable hpos htop
  filter_upwards [hμ.ae_eq hrn, Measure.rnDeriv_pos hμ,
    hμ.ae_le (Measure.rnDeriv_lt_top μ m)] with x hx hp ht
  change Real.log (μ.rnDeriv (exponentialMeasure m V) x).toReal =
    Real.log (μ.rnDeriv m x).toReal - V x
  dsimp only [exponentialMeasure]
  rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (inv_ne_zero (Real.exp_ne_zero _))
      (ENNReal.toReal_ne_zero.mpr ⟨hp.ne', ht.ne⟩), Real.log_inv, Real.log_exp]
  ring

lemma finiteEntropy_exponentialMeasure_iff {m μ : Measure X}
    [SigmaFinite m] [IsFiniteMeasure μ] {V : X → ℝ}
    (hV : Measurable V) (hVi : Integrable V μ) :
    FiniteEntropy (exponentialMeasure m V) μ ↔ FiniteEntropy m μ := by
  constructor
  · rintro ⟨ha, hi⟩
    have ha' := (absolutelyContinuous_exponentialMeasure hV).mp ha
    refine ⟨ha', ?_⟩
    have hs : Integrable (fun x => llr μ m x - V x) μ :=
      hi.congr (llr_exponentialMeasure ha' hV)
    have hh : Integrable (fun x => (llr μ m x - V x) + V x) μ := hs.add hVi
    simpa only [sub_add_cancel] using hh
  · rintro ⟨ha, hi⟩
    exact ⟨(absolutelyContinuous_exponentialMeasure hV).mpr ha,
      (hi.sub hVi).congr (llr_exponentialMeasure ha hV).symm⟩

theorem entropyReal_exponentialMeasure {m μ : Measure X}
    [SigmaFinite m] [IsFiniteMeasure μ] {V : X → ℝ}
    (hμ : FiniteEntropy m μ) (hV : Measurable V) (hVi : Integrable V μ) :
    entropyReal (exponentialMeasure m V) μ = entropyReal m μ - ∫ x, V x ∂μ := by
  rw [entropyReal, integral_congr_ae (llr_exponentialMeasure hμ.1 hV),
    integral_sub hμ.2 hVi, entropyReal]
lemma llr_restrict_self {m : Measure X} [SigmaFinite m] {Q : Set X}
    (hQ : MeasurableSet Q) : llr (m.restrict Q) m =ᵐ[m.restrict Q] 0 := by
  filter_upwards [ae_restrict_of_ae (Measure.rnDeriv_restrict_self m hQ),
    ae_restrict_mem hQ] with x hx hxi
  simp only [llr_def, hx, indicator_of_mem hxi, Pi.one_apply,
    ENNReal.toReal_one, Real.log_one, Pi.zero_apply]

lemma llr_normalizedRestriction {m : Measure X} [SigmaFinite m] {Q : Set X}
    (hQ : MeasurableSet Q) (h₀ : m Q ≠ 0) (htop : m Q ≠ ∞) :
    llr (normalizedRestriction m Q) m =ᵐ[normalizedRestriction m Q]
      fun _ => -Real.log (m Q).toReal := by
  let _ : IsFiniteMeasure (m.restrict Q) := ⟨by simpa using htop.lt_top⟩
  have he := llr_smul_left (μ := m.restrict Q) (ν := m)
    Measure.absolutelyContinuous_restrict (m Q)⁻¹
    (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr h₀)
  have hac : normalizedRestriction m Q ≪ m.restrict Q :=
    Measure.AbsolutelyContinuous.rfl.smul_left _
  filter_upwards [hac.ae_eq he, hac.ae_eq (llr_restrict_self hQ)] with x hx hy
  simpa only [normalizedRestriction, hy, Pi.zero_apply, zero_add, ENNReal.toReal_inv, Real.log_inv] using hx

theorem normalizedRestriction_finiteEntropy {m : Measure X} [SigmaFinite m] {Q : Set X}
    (hQ : MeasurableSet Q) (h₀ : m Q ≠ 0) (htop : m Q ≠ ∞) :
    FiniteEntropy m (normalizedRestriction m Q) := by
  let _ := normalizedRestriction_probability m h₀ htop
  exact ⟨normalizedRestriction_ac m Q,
    (integrable_const _).congr (llr_normalizedRestriction hQ h₀ htop).symm⟩

theorem entropyReal_normalizedRestriction {m : Measure X} [SigmaFinite m] {Q : Set X}
    (hQ : MeasurableSet Q) (h₀ : m Q ≠ 0) (htop : m Q ≠ ∞) :
    entropyReal m (normalizedRestriction m Q) = -Real.log (m Q).toReal := by
  let _ := normalizedRestriction_probability m h₀ htop
  rw [entropyReal, integral_congr_ae (llr_normalizedRestriction hQ h₀ htop)]
  simp

lemma absolutelyContinuous_restrict_of_ae_mem {m μ : Measure X} {Q : Set X}
    (hμ : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) : μ ≪ m.restrict Q := by
  simpa only [Measure.restrict_eq_self_of_ae_mem hs] using hμ.restrict Q

lemma llr_restrict_right_of_ae_mem {m μ : Measure X} [SigmaFinite m]
    [IsFiniteMeasure μ] {Q : Set X} (hQ : MeasurableSet Q)
    (hμ : μ ≪ m) (hs : ∀ᵐ x ∂μ, x ∈ Q) :
    llr μ (m.restrict Q) =ᵐ[μ] llr μ m := by
  have hac := absolutelyContinuous_restrict_of_ae_mem hμ hs
  have hrn := Measure.rnDeriv_mul_rnDeriv (κ := m) hac
  filter_upwards [hμ.ae_eq hrn, hμ.ae_eq (Measure.rnDeriv_restrict_self m hQ), hs]
    with x hx hy hxi
  simp only [Pi.mul_apply, hy, indicator_of_mem hxi, Pi.one_apply, mul_one] at hx
  simp only [llr_def, hx]

theorem entropyReal_lower_bound {m μ : Measure X} [SigmaFinite m]
    [IsProbabilityMeasure μ] {Q : Set X} (hQ : MeasurableSet Q)
    (htop : m Q ≠ ∞) (hs : ∀ᵐ x ∂μ, x ∈ Q) (hμ : FiniteEntropy m μ) :
    -Real.log (m Q).toReal ≤ entropyReal m μ := by
  let _ : IsFiniteMeasure (m.restrict Q) := ⟨by simpa using htop.lt_top⟩
  have he := llr_restrict_right_of_ae_mem hQ hμ.1 hs
  have ht := InformationTheory.integral_llr_add_mul_log_nonneg
    (absolutelyContinuous_restrict_of_ae_mem hμ.1 hs) (hμ.2.congr he.symm)
  rw [integral_congr_ae he] at ht
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_mul,
    Measure.restrict_apply_univ, add_sub_cancel_right] at ht
  dsimp only [entropyReal]
  linarith

end WeakHessian

open Set Filter MeasureTheory InformationTheory
open scoped Topology

end

end OAI
