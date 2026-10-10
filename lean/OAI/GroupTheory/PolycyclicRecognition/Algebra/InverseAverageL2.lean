import OAI.GroupTheory.PolycyclicRecognition.Algebra.CouplingLocalL2
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiberAverageL2

namespace OAI

/-! # The inverse transfer belongs to L²

The transfer in inverse coordinates is averaged over an actual positive
compact Haar region. Local L² integrability and Jensen's estimate justify
this construction for the finite inverse-section measure.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [SecondCountableTopology W]

omit [CompleteSpace W] [NormedSpace ℝ W] in
/-- The corrected inverse transfer is square integrable on a normalized
compact fiber region. -/
theorem inverseFiberTransfer_memLp_normalized
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) :
    MemLp (inverseFiberTransfer π l φ) 2 (ν.prod (normalizedRestriction m B)) := by
  have hf := inverseFiberTransfer_memLp_compact m μ π l hπ hl hφ
    (isCompact_univ.prod hB)
  rw [hprod, ← Measure.prod_restrict, Measure.restrict_univ] at hf
  exact memLp_normalizedRestriction_product ν m hB0 hf

omit [CompleteSpace W] in
/-- Translating the compact fiber region by its evaluation center retains
square integrability. Stationarity handles the normalized section shift. -/
theorem inverseFiberTransfer_shift_memLp
    (ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure ν]
    [SMulInvariantMeasure G (NormalizedPair G Λ) ν]
    (β : Measure G) [IsProbabilityMeasure β]
    (π l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    (φ : NormalizedPair G Λ → W)
    (hD : MemLp (inverseFiberTransfer π l φ) 2 (ν.prod β)) (y : G) :
    MemLp (fun q : NormalizedPair G Λ × G =>
      inverseFiberTransfer π l φ (q.1, q.1.val.1 y * q.2)) 2 (ν.prod β) := by
  have hT : MeasurePreserving (normalizedTranslate (Λ := Λ) y) ν ν := by
    have h := measurePreserving_smul y⁻¹ ν
    change MeasurePreserving (fun p => normalizedTranslate (y⁻¹)⁻¹ p) ν ν at h
    simpa only [inv_inv] using h
  have hshift := hD.comp_measurePreserving (hT.prod (MeasurePreserving.id β))
  let c : C(NormalizedPair G Λ, W) :=
    ⟨fun p => (π y).toAdd - (l (p.val.1 y)).toAdd,
      continuous_const.sub (hl.comp ((continuous_eval_const y).comp continuous_subtype_val.fst))⟩
  have hc : MemLp (fun p : NormalizedPair G Λ => (π y).toAdd - (l (p.val.1 y)).toAdd) 2 ν :=
    ContinuousMap.memLp (μ := ν) (p := 2) ℝ c
  have hs : MemLp (fun q : NormalizedPair G Λ × G =>
      inverseFiberTransfer π l φ (normalizedTranslate y q.1, q.2) +
        ((π y).toAdd - (l (q.1.val.1 y)).toAdd)) 2 (ν.prod β) :=
    hshift.add (hc.comp_fst β)
  apply (memLp_congr_ae ?_).mp hs
  filter_upwards with q
  have h := inverseFiberTransfer_normalizedTranslate π l φ y q.1 q.2
  change inverseFiberTransfer π l φ (normalizedTranslate y q.1, q.2) +
      ((π y).toAdd - (l (q.1.val.1 y)).toAdd) = _
  rw [h]
  abel

omit [CompleteSpace W] in
/-- The averaged inverse transfer is an actual square-integrable function
for the section measure constructed by Haar factorization. -/
theorem inverseAveragedTransfer_memLp
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ ν : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {B : Set G} (hB : IsCompact B) (hB0 : m B ≠ 0) :
    MemLp (inverseAveragedTransfer (normalizedRestriction m B) π l φ) 2 ν := by
  let := normalizedRestriction_probability m hB0 hB.measure_ne_top
  exact (memLp_fiberAverage ν (normalizedRestriction m B)
    (inverseFiberTransfer_memLp_normalized m μ ν hprod π l hπ hl hφ hB hB0)).1

omit [SecondCountableTopology G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [SecondCountableTopology W] in
/-- For two square-integrable fiber restrictions, the average error is
bounded by their whole-product squared oscillation. -/
theorem inverseAverageError_sq_le
    (β : Measure G) [IsProbabilityMeasure β]
    (π l : G →* Multiplicative W) (φ : NormalizedPair G Λ → W)
    (y : G) (p : NormalizedPair G Λ)
    (h₁ : MemLp (fun x => inverseFiberTransfer π l φ (p, p.val.1 y * x)) 2 β)
    (h₂ : MemLp (fun x => inverseFiberTransfer π l φ (p, x)) 2 β) :
    ‖inverseAverageError β π l φ y p‖ ^ 2 ≤
      ∫ x₁, ∫ x₂, ‖pairTransferDefect π l φ (x₂⁻¹ * (p.val.1 y * x₁))
        (pairChartTransition.symm (p, x₂)).2‖ ^ 2 ∂β ∂β := by
  have h := norm_sub_integral_sq_le β h₁ h₂
  rw [inverseAverageError, integral_sub
    (h₁.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (h₂.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  simpa only [inverseFiberTransfer_sub] using h

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Algebraic final step of the inverse transfer: the linear coefficient is
precisely the inverse of the original coefficient. -/
theorem inverse_transfer_linear_coefficient (A : W ≃L[ℝ] W)
    {v w ψ ψ' R : W} (h : ψ' - ψ = -v + A w + R) :
    w + (-A.symm ψ') - (-A.symm ψ) = A.symm v - A.symm R := by
  have ha := congrArg A.symm h
  simp only [map_sub, map_neg, map_add, ContinuousLinearEquiv.symm_apply_apply] at ha
  have heq : A.symm ψ' - A.symm ψ = -A.symm v + w + A.symm R := ha
  rw [sub_eq_iff_eq_add] at heq
  rw [heq]
  abel

end PolycyclicRecognition

end

end OAI
