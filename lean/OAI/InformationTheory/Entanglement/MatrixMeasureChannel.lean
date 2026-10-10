import OAI.InformationTheory.Entanglement.FiniteRecovery
import OAI.InformationTheory.Entanglement.FactorizedLawGap
import OAI.InformationTheory.Entanglement.ChoiTransfer

namespace OAI

noncomputable section
open MeasureTheory Matrix Filter
open scoped MeasureTheory BigOperators ComplexOrder MatrixOrder
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T] {n m : Type} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]
namespace PositiveMatrixMeasure
omit [Fintype m] [DecidableEq m] in
lemma channel_entry_value (W : PositiveMatrixMeasure T n) (F : Map n m) (s : Set T) :
    (fun a b => (∑ i, ∑ j, F (Matrix.single i j 1) a b • W.entry i j) s)=F (W.value s) := by
  rw [linearMap_entries F (W.value s)]
  ext a b
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,Matrix.sum_apply,Matrix.smul_apply,value]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

def channel (W : PositiveMatrixMeasure T n) (F : Map n m) (hF : CP F) : PositiveMatrixMeasure T m where
  entry a b := ∑ i, ∑ j, F (Matrix.single i j 1) a b • W.entry i j
  positive s hs := by
    rw [channel_entry_value]
    exact cp_positive hF (W.positive s hs)
omit [DecidableEq m] in
lemma channel_value (W : PositiveMatrixMeasure T n) (F : Map n m) (hF : CP F) (s : Set T) :
    (W.channel F hF).value s=F (W.value s) := channel_entry_value W F s
omit [DecidableEq m] in
lemma channel_traceMeasure (W : PositiveMatrixMeasure T n) (F : Map n m)
    (hF : CP F) (hT : TracePreserving F) : (W.channel F hF).traceMeasure=W.traceMeasure := by
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (W.channel F hF).traceMeasure.real s=W.traceMeasure.real s
  rw [traceMeasure_real _ hs,traceMeasure_real _ hs,channel_value,hT]
omit [Fintype m] [DecidableEq m] in
lemma channel_entry (F : Map n m) (D : Mat n) (a b : m) :
    F D a b=∑ i, ∑ j, D i j*F (Matrix.single i j 1) a b := by
  rw [linearMap_entries F D]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
omit [Fintype m] [DecidableEq m] in
lemma channel_density_integrable (F : Map n m) {μ : Measure T} (D : T → Mat n)
    (hi : ∀ a b, Integrable (fun t => D t a b) μ) (a b : m) :
    Integrable (fun t => F (D t) a b) μ := by
  have he : (fun t => F (D t) a b)=(fun t => ∑ i, ∑ j, D t i j*F (Matrix.single i j 1) a b) :=
    funext fun t => channel_entry F (D t) a b
  rw [he]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi i j).mul_const _
omit [Fintype m] [DecidableEq m] in
lemma channel_setIntegral (F : Map n m) {μ : Measure T} (D : T → Mat n)
    (hi : ∀ a b, Integrable (fun t => D t a b) μ) (s : Set T) (a b : m) :
    (∫ t in s, F (D t) a b ∂μ)=F (fun i j => ∫ t in s, D t i j ∂μ) a b := by
  have he : (fun t => F (D t) a b)=(fun t => ∑ i, ∑ j, D t i j*F (Matrix.single i j 1) a b) :=
    funext fun t => channel_entry F (D t) a b
  rw [he]
  apply Eq.trans ?_ (channel_entry F (Matrix.of fun i j => ∫ t in s, D t i j ∂μ) a b).symm
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hi i j).integrableOn.mul_const _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (hi i j).integrableOn.mul_const _)]
  simp only [integral_mul_const,Matrix.of_apply]
omit [DecidableEq m] in
lemma channel_positiveDensity (W : PositiveMatrixMeasure T n) (F : Map n m)
    (hF : CP F) (hT : TracePreserving F) {μ : Measure T} [IsFiniteMeasure μ]
    (hW : W.traceMeasure≪μ) :
    (fun t => F (W.positiveDensity μ t))=ᵐ[μ](W.channel F hF).positiveDensity μ := by
  apply (W.channel F hF).density_unique
    (by simpa only [channel_traceMeasure W F hF hT] using hW)
  · exact channel_density_integrable F _ (W.positiveDensity_integrable hW)
  · intro s hs a b
    rw [channel_setIntegral F _ (W.positiveDensity_integrable hW),channel_value]
    have he : (Matrix.of fun i j => ∫ t in s, W.positiveDensity μ t i j ∂μ)=W.value s := by
      ext i j
      exact W.positiveDensity_setIntegral hW hs i j
    exact congrArg (fun M : Mat n => F M a b) he
end PositiveMatrixMeasure
omit [DecidableEq m] in
lemma bitComparisonMeasure_channel (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) (F : Map n m) (hF : CP F) (hT : TracePreserving F) :
    bitComparisonMeasure (fun i j => (W i j).channel F hF) (σ.channel F hF)=bitComparisonMeasure W σ := by
  simp only [bitComparisonMeasure,familyTraceMeasure,PositiveMatrixMeasure.channel_traceMeasure _ F hF hT]
omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma measurable_matrix_map (F : Map n m) : Measurable F := by
  exact F.continuous_of_finiteDimensional.measurable
omit [MeasurableSpace T] [Fintype n] [DecidableEq n] in
lemma idealDensity_psd (σ : T → Mat n) (hσ : ∀ t, (σ t).PosSemidef) (i j : Fin 2) (t : T) :
    (idealDensity σ i j t).PosSemidef := by
  unfold idealDensity halfDensity
  split_ifs
  · exact (hσ t).smul (by rw [Complex.nonneg_iff]; norm_num)
  · exact Matrix.PosSemidef.zero
omit [Fintype n] [DecidableEq n] in
lemma idealDensity_measurable (σ : T → Mat n) (hσ : Measurable σ) (i j : Fin 2) :
    Measurable (idealDensity σ i j) := by
  unfold idealDensity halfDensity
  split_ifs
  · exact hσ.const_smul (1/2 : ℂ)
  · exact measurable_const
omit [DecidableEq n] in
lemma idealDensity_trace_integrable (σ : T → Mat n) {μ : Measure T}
    (hσ : Integrable (fun t => (Matrix.trace (σ t)).re) μ) (i j : Fin 2) :
    Integrable (fun t => (Matrix.trace (idealDensity σ i j t)).re) μ := by
  unfold idealDensity
  split_ifs
  · simpa only [halfDensity_trace] using hσ.div_const 2
  · simp only [Matrix.trace_zero,Complex.zero_re]; exact integrable_zero _ _ _
omit [MeasurableSpace T] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma channel_idealDensity (F : Map n m) (σ : T → Mat n) (i j : Fin 2) (t : T) :
    F (idealDensity σ i j t)=idealDensity (fun t => F (σ t)) i j t := by
  unfold idealDensity halfDensity
  split_ifs <;> simp only [map_smul,map_zero]

theorem cqBitDistance_channel (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) (F : Map n m) (hF : CP F) (hT : TracePreserving F) :
    cqBitDistance (fun i j => (W i j).channel F hF) (σ.channel F hF) ≤ cqBitDistance W σ := by
  have htr : ∀ A, Matrix.trace (F A)=Matrix.trace A := hT
  let μ := bitComparisonMeasure W σ
  have hW (i j : Fin 2) := (W i j).channel_positiveDensity F hF hT (bitComparison_actual_dom W σ i j)
  have hσ := σ.channel_positiveDensity F hF hT (bitComparison_ideal_dom W σ)
  unfold cqBitDistance
  rw [bitComparisonMeasure_channel W σ F hF hT,
    ← bitDistance_congr_ae hW hσ]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  apply integral_mono
  · apply integrable_traceNorm_sub
    · exact (measurable_matrix_map F).comp ((W i j).positiveDensity_measurable μ)
    · exact idealDensity_measurable _ ((measurable_matrix_map F).comp (σ.positiveDensity_measurable μ)) i j
    · intro t; exact cp_positive hF ((W i j).positiveDensity_psd μ t)
    · exact idealDensity_psd _ (fun t => cp_positive hF (σ.positiveDensity_psd μ t)) i j
    · simpa only [htr] using (W i j).positiveDensity_trace_integrable (bitComparison_actual_dom W σ i j)
    · apply idealDensity_trace_integrable
      simpa only [htr] using σ.positiveDensity_trace_integrable (bitComparison_ideal_dom W σ)
  · apply integrable_traceNorm_sub
    · exact (W i j).positiveDensity_measurable μ
    · exact idealDensity_measurable _ (σ.positiveDensity_measurable μ) i j
    · exact (W i j).positiveDensity_psd μ
    · exact idealDensity_psd _ (σ.positiveDensity_psd μ) i j
    · exact (W i j).positiveDensity_trace_integrable (bitComparison_actual_dom W σ i j)
    · exact idealDensity_trace_integrable _ (σ.positiveDensity_trace_integrable (bitComparison_ideal_dom W σ)) i j
  · intro t
    dsimp only
    rw [← channel_idealDensity F (σ.positiveDensity μ) i j t,← map_sub]
    exact traceNorm_cptp F hF hT (((W i j).positiveDensity_psd μ t).isHermitian.sub
      (idealDensity_psd _ (σ.positiveDensity_psd μ) i j t).isHermitian)

end SecretKey

end

end OAI
