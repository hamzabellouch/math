import OAI.Probability.SLE.Mass.LocallyFiniteMeasureSubtract
import OAI.Probability.SLE.Mass.RationalTraceMassAdapted

namespace OAI

/-! Positive differences of locally finite random Radon measures admit
measurable versions. No finite total mass is required. -/

noncomputable section
open Set Filter MeasureTheory Classical
open scoped ENNReal Topology CompactlySupported

namespace SLEExactGauge

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma halfPlane_sub_finite_on_compacts (μ ν : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (μ-ν) :=
  ⟨fun K hK => lt_of_le_of_lt (Measure.sub_le K) hK.measure_lt_top⟩

lemma integral_halfPlane_sub (μ ν : Measure upperHalfPlane) [μ.Regular] [ν.Regular]
    (hle : ν ≤ μ) (f : C_c(upperHalfPlane,ℝ)) :
    (∫ z, f z ∂(μ-ν)) = (∫ z, f z ∂μ) - ∫ z, f z ∂ν := by
  let := halfPlane_sub_finite_on_compacts μ ν
  have hi := integral_add_measure (μ := μ-ν) (ν := ν) f.integrable f.integrable
  rw [sigmaFinite_sub_add_cancel_of_le hle] at hi
  linarith

theorem measurable_halfPlane_sub_of_le
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Ω → Measure upperHalfPlane)
    (hμ : Measurable μ) (hν : Measurable ν)
    (hμr : ∀ ω, (μ ω).Regular) (hνr : ∀ ω, (ν ω).Regular)
    (hle : ∀ ω, ν ω ≤ μ ω) : Measurable (fun ω => μ ω-ν ω) := by
  let (ω : Ω) : (μ ω).Regular := hμr ω
  let (ω : Ω) : (ν ω).Regular := hνr ω
  let (ω : Ω) : IsFiniteMeasureOnCompacts (μ ω-ν ω) :=
    halfPlane_sub_finite_on_compacts (μ ω) (ν ω)
  apply measurable_radon_of_tests _ (fun _ => inferInstance)
  intro f
  simp_rw [integral_halfPlane_sub _ _ (hle _) f]
  exact (measurable_halfPlane_compact_test_integral μ hμ hμr f).sub
    (measurable_halfPlane_compact_test_integral ν hν hνr f)

theorem exists_measurable_halfPlane_difference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ ν : Ω → Measure upperHalfPlane)
    (hμ : Measurable μ) (hν : Measurable ν)
    (hμr : ∀ ω, (μ ω).Regular) (hνr : ∀ ω, (ν ω).Regular)
    (hle : ∀ᵐ ω ∂P, ν ω ≤ μ ω) :
    ∃ η : Ω → Measure upperHalfPlane, Measurable η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧
      (∀ᵐ ω ∂P, η ω + ν ω = μ ω) := by
  obtain ⟨E,hE,hEm,hEsub⟩ := hle.exists_measurable_mem
  let μ' (ω : Ω) := if ω ∈ E then μ ω else 0
  let ν' (ω : Ω) := if ω ∈ E then ν ω else 0
  have hμ' : Measurable μ' := hμ.ite hEm measurable_const
  have hν' : Measurable ν' := hν.ite hEm measurable_const
  have hμr' (ω : Ω) : (μ' ω).Regular := by
    dsimp only [μ']; split_ifs; exacts [hμr ω,inferInstance]
  have hνr' (ω : Ω) : (ν' ω).Regular := by
    dsimp only [ν']; split_ifs; exacts [hνr ω,inferInstance]
  have hle' (ω : Ω) : ν' ω ≤ μ' ω := by
    dsimp only [μ',ν']; split_ifs with he
    · exact hEsub ω he
    · exact le_rfl
  refine ⟨fun ω => μ' ω-ν' ω,measurable_halfPlane_sub_of_le μ' ν' hμ' hν' hμr' hνr' hle',?_,?_⟩
  · intro ω
    let := hμr' ω
    let := halfPlane_sub_finite_on_compacts (μ' ω) (ν' ω)
    exact ⟨inferInstance,inferInstance⟩
  · filter_upwards [hE] with ω hω
    let := hνr ω
    simpa only [μ',ν',ite_eq_left hω] using sigmaFinite_sub_add_cancel_of_le (hEsub ω hω)

end SLEExactGauge

end

end OAI
