import OAI.Probability.InvariantIsing.Arrays.QuantizedFieldPressure
import OAI.Probability.InvariantIsing.Fields.FieldQuantizerError

namespace OAI

/-! The physical mean pressure formula for general first-moment field laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology Classical
namespace InvariantIsing

theorem general_mean_wasserstein_field_pressure_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    (P : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (P N)]
    [∀ N, (P N).IsMulRightInvariant] (eig : (N : ℕ) → Fin N → ℝ)
    (ν : ProbabilityMeasure ℝ) (a b : ℝ)
    (hcompact : IsCompact (ν : Measure ℝ).support)
    (hbound : (ν : Measure ℝ).support ⊆ Icc a b)
    (ha : a∈(ν : Measure ℝ).support) (hb : b∈(ν : Measure ℝ).support)
    (hno : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i, a-ε ≤ eig N i ∧ eig N i ≤ b+ε)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (Nat.succ_pos k) (eig (k+1))) atTop (𝓝 ν))
    (field : (N : ℕ) → Fin N → ℝ) (ξ : ProbabilityMeasure ℝ)
    (hξ : Integrable (fun x : ℝ => x) (ξ : Measure ℝ))
    (hw : Tendsto (fun k => fieldWassersteinOne (empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))) ξ)
      atTop (𝓝 0)) :
    Tendsto (fun N => ∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹) (field N) ∂P N)
      atTop (𝓝 (magneticFieldFunctional (ν : Measure ℝ) b ξ)) := by
  let μs := fun k => empiricalSpectralLaw (Nat.succ_pos k) (field (k+1))
  have hm k : Integrable (fun x : ℝ => x) (μs k : Measure ℝ) :=
    empiricalField_integrable (Nat.succ_pos k) (field (k+1)) id
  have hfw : Tendsto μs atTop (𝓝 ξ) := weak_tendsto_of_fieldWasserstein ξ μs hξ hm hw
  let mean := fun N => ∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹) (field N) ∂P N
  let F := magneticFieldFunctional (ν : Measure ℝ) b ξ
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := ((fieldTail_integral_tendsto (ξ : Measure ℝ) hξ).eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ)<ε/64))).exists
  let δ : ℝ := ε/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n,c,r,hc,hr,hn,hcover⟩ := exists_field_ball_quantizer (ξ : Measure ℝ)
    (M := (M : ℝ)) hδ
  let V := simpleFieldValue (ξ : Measure ℝ) (fieldBallSimple c r) (measureR (ν : Measure ℝ) b)
  let quant := fun N => ∫ U, rotatedPressure (eig N) (matrixRotation U⁻¹)
    (fun i => fieldBallSimple c r (field N i)) ∂P N
  have hq : Tendsto quant atTop (𝓝 V) := quantized_mean_field_pressure_tendsto
    hhaar hgauss hpub P eig ν a b hcompact hbound ha hb hno hweak field ξ hfw c r hn
  have hq' := hq.comp (tendsto_add_atTop_nat 1)
  have ht := fieldTail_integral_tendsto_of_wasserstein ξ μs hξ hm hw (M : ℝ)
  have hv : |F-V| ≤ δ+4*(∫ x, fieldTail M x ∂(ξ : Measure ℝ)) := by
    refine (magneticFieldFunctional_simple_error ν ξ a b hcompact hbound ha hb hξ
      (fieldBallSimple c r)).trans ?_
    simpa only [abs_sub_comm] using fieldBallSimple_integral_error (ξ : Measure ℝ) hξ
      c r (Nat.cast_nonneg M) hδ.le hc hr hcover
  have hqe := (Metric.tendsto_nhds.mp hq') (ε/4) (by positivity)
  have hte := ht.eventually (Iio_mem_nhds (lt_add_of_pos_right _ (by positivity : (0 : ℝ)<ε/64)))
  filter_upwards [hqe,hte] with k hk htk
  have he := mean_field_quantizer_error (Nat.succ_pos k) (P (k+1)) (eig (k+1)) (field (k+1))
    c r (Nat.cast_nonneg M) hδ.le hc hr hcover
  change |mean (k+1)-quant (k+1)| ≤ _ at he
  rw [Real.dist_eq] at hk ⊢
  change |quant (k+1)-V|<ε/4 at hk
  change |mean (k+1)-F|<ε
  have htriangle := abs_sub_le (mean (k+1)) (quant (k+1)) F
  have htriangle' := abs_sub_le (quant (k+1)) V F
  rw [abs_sub_comm V F] at htriangle'
  dsimp only [δ] at he hv
  change (∫ x, fieldTail M x ∂(μs k : Measure ℝ))<_ at htk
  linarith

end InvariantIsing

end

end OAI
