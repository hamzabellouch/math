import OAI.Analysis.CircleDomains.Modulus.CodeModulusExtraction

namespace OAI

/-! The prescribed-countable-set conclusion from positive modulus. The
occupation and tuple densities, full visit bound, and atomless whole-image
test are obtained for the same law on actual base codes. -/

open Set MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y D : Type*} [MetricSpace X] [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace D] [BorelSpace D] [MeasurableSingletonClass D]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]
  [SecondCountableTopology X] [Countable D] [PolishSpace Y] [PolishSpace D]

theorem prescribed_countable_law_of_positive_modulus (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (hB : IsClosed d.dust)
    (hH : ∀ i, IsClosed (d.levels i))
    (p : D → X) (hp : Function.Injective p) (c : D → ℝ≥0∞)
    (hc0 : ∀ s, c s ≠ 0) (hct : ∀ s, c s ≠ ∞) (hc : (∑' s, c s ^ 2) < ∞)
    (ν : Measure X) [IsFiniteMeasure ν] [NullSingletonClass ν]
    [StandardBorelSpace (ConstrainedCostCode d p c ν)]
    (flags : Set X) (hflags : flags.Countable) (hν : ν d.dustᶜ = 0)
    (hunique : ∀ x ∈ d.dust \ flags, ∀ i t u,
      (t, x) ∈ d.levels i → (u, x) ∈ d.levels i → t = u)
    (μ : Measure Y) [IsFiniteMeasure μ]
    (ω : TupleType → ℝ≥0∞) (hω : (∑' i, ω i) < ∞)
    (hdual : MeasureImageDuality (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (hlift : MeasurePlanLifting (ConstrainedCostCode d p c ν) (PathCostSpace Y D))
    (r : ℝ≥0) (hr : 0 < r)
    (hmod : (r : ℝ≥0∞) < measureFamilyModulus (ConstrainedCostCode d p c ν)
      (PathCostSpace Y D) (pathCostReference μ c (tupleReference ω))
        (constrainedCodeMeasure d p c ν)) :
    ∃ (P : ProbabilityMeasure (BasePathCode d)) (g : Y → ℝ≥0∞) (q : LevelTuple → ℝ≥0∞),
      Measurable g ∧ Measurable q ∧
      meanCodeOccupation d P = μ.withDensity g ∧
      (∫⁻ y, g y ^ 2 ∂μ) ≤ (r : ℝ≥0∞)⁻¹ ∧
      countingSquareNorm (fun s => meanVisitCount (codePathLaw d P) (p s)) ≤
        (r : ℝ≥0∞)⁻¹ ^ (1 / 2 : ℝ) + 1 ∧
      meanCodeTuple d P = (tupleReference ω).withDensity q ∧
      (∫⁻ t, q t ^ 2 ∂tupleReference ω) ≤ (r : ℝ≥0∞)⁻¹ ∧
      (∀ k, slotLaw d P k ≪ tupleReference ω) ∧
      (∫⁻ x, pathHitProbability (codePathLaw d P) x ∂ν) = 0 ∧
      (∀ᵐ Γ ∂(P : Measure (BasePathCode d)), ν (residualImage d.dust Γ.val) = 0) := by
  let : IsFiniteMeasure (tupleReference ω) := finite_tupleReference hω
  obtain ⟨P, Q, hQ, hbar, henergy, _, hres⟩ := positive_modulus_code_law d hU hB
    p c ν μ (tupleReference ω) hc hdual hlift r hr hmod
  have hd := codeLaw_component_densities d hU p c P μ (tupleReference ω) Q hQ hbar
  have he := codeReference_component_energies μ c (tupleReference ω) Q hQ
  refine ⟨P, Q ∘ costPhysical, Q ∘ costTuple, hQ.comp measurable_costPhysical,
    hQ.comp measurable_costTuple, hd.1, he.1.trans henergy, ?_, hd.2.2,
    he.2.trans henergy, ?_, ?_, hres⟩
  · exact (meanVisitCount_codePathLaw_budget d hU p hp c hc0 hct P μ
      (tupleReference ω) Q hQ hbar).trans
      (add_le_add (ENNReal.rpow_le_rpow henergy (by norm_num)) le_rfl)
  · exact codeLaw_slot_absolutelyContinuous d hU p c P μ (tupleReference ω) Q hbar
  · simp_rw [pathHitProbability_codePathLaw]
    exact codeLaw_whole_image_test d hU hB hH p c P μ ω Q hbar ν
      (ae_free_level_sections d.levels d.dust flags ν hflags hν hunique) hres

end CircleDomainRigidity

end

end OAI
