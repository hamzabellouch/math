import OAI.InformationTheory.Entanglement.MatrixDensityChange

namespace OAI

noncomputable section
open MeasureTheory Matrix Filter
open scoped MeasureTheory BigOperators ComplexOrder MatrixOrder Kronecker
namespace SecretKey
open ChannelCompletion
variable {T : Type*} [MeasurableSpace T] {n m : Type} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def bitComparisonMeasure (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) : Measure T :=
  familyTraceMeasure (fun p : Fin 2 × Fin 2 => W p.1 p.2)+σ.traceMeasure
instance bitComparisonMeasureIsFiniteMeasure (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) : IsFiniteMeasure (bitComparisonMeasure W σ) := by
  unfold bitComparisonMeasure
  infer_instance
omit [DecidableEq n] in
lemma bitComparison_actual_dom (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) (i j : Fin 2) :
    (W i j).traceMeasure≪bitComparisonMeasure W σ :=
  (trace_absolutelyContinuous_family (fun p : Fin 2 × Fin 2 => W p.1 p.2) (i,j)).trans
    (Measure.absolutelyContinuous_of_le (le_add_of_nonneg_right bot_le))
omit [DecidableEq n] in
lemma bitComparison_ideal_dom (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) : σ.traceMeasure≪bitComparisonMeasure W σ :=
  Measure.absolutelyContinuous_of_le (le_add_of_nonneg_left bot_le)

def cqBitDistance (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) : ℝ :=
  bitDistance (fun i j => (W i j).positiveDensity (bitComparisonMeasure W σ))
    (σ.positiveDensity (bitComparisonMeasure W σ)) (bitComparisonMeasure W σ)
lemma cqBitDistance_enlarge (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n)
    (σ : PositiveMatrixMeasure T n) {ν : Measure T} [IsFiniteMeasure ν]
    (hν : bitComparisonMeasure W σ≪ν) :
    cqBitDistance W σ=bitDistance (fun i j => (W i j).positiveDensity ν)
      (σ.positiveDensity ν) ν :=
  (bitLawDistance_change W σ (bitComparison_actual_dom W σ) (bitComparison_ideal_dom W σ) hν).symm
omit [DecidableEq n] in
lemma integral_trace_of_entry_integrals {μ : Measure T} (D : T → Mat n) (M : Mat n)
    (hi : ∀ a b, Integrable (fun t => D t a b) μ)
    (he : ∀ a b, (∫ t, D t a b ∂μ)=M a b) :
    (∫ t, (Matrix.trace (D t)).re ∂μ)=(Matrix.trace M).re := by
  change (∫ t, RCLike.re (∑ i, D t i i) ∂μ)=_
  rw [integral_re (integrable_finsetSum _ (fun i _ => hi i i))]
  rw [integral_finsetSum _ (fun i _ => hi i i)]
  simp only [he,Matrix.trace,Matrix.diag]
  rfl
lemma measurable_factorized_eveBlock (R : Mat (n×m)) {X : T → Mat n} {Y : T → Mat m}
    (hX : Measurable X) (hY : Measurable Y) : Measurable (fun t => eveBlock R (X t ⊗ₖ Y t)) := by
  change @Measurable T (n → n → ℂ) _ (borel _) X at hX
  change @Measurable T (m → m → ℂ) _ (borel _) Y at hY
  rw [← @BorelSpace.measurable_eq (n → n → ℂ) _ MeasurableSpace.pi _] at hX
  rw [← @BorelSpace.measurable_eq (m → m → ℂ) _ MeasurableSpace.pi _] at hY
  change @Measurable T ((n×m) → (n×m) → ℂ) _ (borel _) _
  rw [← @BorelSpace.measurable_eq ((n×m) → (n×m) → ℂ) _ MeasurableSpace.pi _]
  apply Measurable.of_eval
  intro a
  apply Measurable.of_eval
  intro b
  simp only [eveBlock,Matrix.transpose_apply,Matrix.mul_apply,Matrix.kroneckerMap_apply]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul _ measurable_const
  apply Finset.measurable_sum
  intro k _
  exact measurable_const.mul (((measurable_pi_apply j.1).comp ((measurable_pi_apply k.1).comp hX)).mul
    ((measurable_pi_apply j.2).comp ((measurable_pi_apply k.2).comp hY)))
lemma scaled_eveBlock_coherence (R : Mat (n×m)) (hR : Represented R)
    (X : Fin 2 → Mat n) (Y : Fin 2 → Mat m)
    (hX : ∀ i, (X i).PosSemidef) (hY : ∀ i, (Y i).PosSemidef)
    (c : ℝ) (hc : 0≤c) :
    let τ := fun i j => (c : ℂ) • eveBlock R (X i ⊗ₖ Y j)
    let p := fun i j => (Matrix.trace (τ i j)).re
    fidelity (τ 0 0) (τ 1 1) ≤
      Real.sqrt (p 0 0*p 0 1)+Real.sqrt (p 1 0*p 1 1)+2*Real.sqrt (p 0 1*p 1 0) := by
  dsimp only
  have he (i j : Fin 2) : (c : ℂ) • eveBlock R (X i ⊗ₖ Y j)=
      eveBlock R (((c : ℂ) • X i) ⊗ₖ Y j) := by
    rw [Matrix.smul_kronecker,eveBlock_smul]
  simp only [he]
  exact eveBlock_coherence R hR (fun i => (c : ℂ) • X i) Y
    (fun i => (hX i).smul (by rw [Complex.nonneg_iff]; exact ⟨hc,by simp⟩)) hY

theorem factorized_law_gap (R : Mat (n×m)) (hR : Represented R)
    (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T (n×m))
    (σ : PositiveMatrixMeasure T (n×m)) (μ : Measure T) [IsFiniteMeasure μ]
    (X : Fin 2 → T → Mat n) (Y : Fin 2 → T → Mat m)
    (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
    (hXp : ∀ i t, (X i t).PosSemidef) (hYp : ∀ j t, (Y j t).PosSemidef)
    (hDi : ∀ i j a b, Integrable (fun t => eveBlock R (X i t ⊗ₖ Y j t) a b) μ)
    (hDs : ∀ i j s, MeasurableSet s → ∀ a b,
      (∫ t in s, eveBlock R (X i t ⊗ₖ Y j t) a b ∂μ)=(W i j).value s a b)
    (hW1 : (∑ i, ∑ j, (Matrix.trace ((W i j).value Set.univ)).re)=1)
    (hσ1 : (Matrix.trace (σ.value Set.univ)).re=1) :
    1/5≤cqBitDistance W σ := by
  let ν := μ+bitComparisonMeasure W σ
  have hμν : μ≪ν := Measure.absolutelyContinuous_of_le (le_add_of_nonneg_right bot_le)
  have hκν : bitComparisonMeasure W σ≪ν :=
    Measure.absolutelyContinuous_of_le (le_add_of_nonneg_left bot_le)
  let D := fun i j t => eveBlock R (X i t ⊗ₖ Y j t)
  let D' := fun i j t => (densityWeight μ ν t : ℂ) • D i j t
  have hD'm : ∀ i j, Measurable (D' i j) := by
    intro i j
    have hd : Measurable (D i j) := measurable_factorized_eveBlock R (hXm i) (hYm j)
    exact (densityWeight_measurable μ ν).complex_ofReal.smul hd
  have hD'p : ∀ i j t, (D' i j t).PosSemidef := by
    intro i j t
    exact (eveBlock_psd ((hXp i t).kronecker (hYp j t))).smul
      (by rw [Complex.nonneg_iff]; exact ⟨densityWeight_nonneg μ ν t,by simp⟩)
  have hD'i : ∀ i j a b, Integrable (fun t => D' i j t a b) ν := by
    intro i j a b
    simpa only [D',D,Matrix.smul_apply,smul_eq_mul,Complex.real_smul] using
      densityWeight_integrable μ ν hμν (hDi i j a b)
  have hD's : ∀ i j s, MeasurableSet s → ∀ a b,
      (∫ t in s, D' i j t a b ∂ν)=(W i j).value s a b := by
    intro i j s hs a b
    simpa only [D',D,Matrix.smul_apply,smul_eq_mul,Complex.real_smul] using
      (densityWeight_setIntegral μ ν hμν (fun t => D i j t a b) hs).trans (hDs i j s hs a b)
  have hDeq : ∀ i j, D' i j=ᵐ[ν](W i j).positiveDensity ν := by
    intro i j
    exact (W i j).density_unique ((bitComparison_actual_dom W σ i j).trans hκν)
      (D' i j) (hD'i i j) (hD's i j)
  rw [cqBitDistance_enlarge W σ hκν,
    ← bitDistance_congr_ae hDeq (Filter.EventuallyEq.rfl : σ.positiveDensity ν=ᵐ[ν]σ.positiveDensity ν)]
  apply matrix_density_gap _ _ hD'm (σ.positiveDensity_measurable ν) hD'p
    (σ.positiveDensity_psd ν)
  · intro i j
    exact (integrable_finsetSum _ (fun a _ => hD'i i j a a)).re
  · exact σ.positiveDensity_trace_integrable ((bitComparison_ideal_dom W σ).trans hκν)
  · have he : (∑ i, ∑ j, ∫ t, (Matrix.trace (D' i j t)).re ∂ν)=
        (∑ i, ∑ j, (Matrix.trace ((W i j).value Set.univ)).re) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply integral_trace_of_entry_integrals _ _ (hD'i i j)
      intro a b
      simpa using hD's i j Set.univ MeasurableSet.univ a b
    exact he.trans hW1
  · rw [← σ.traceMeasure_real MeasurableSet.univ] at hσ1
    simpa only [Measure.restrict_univ] using
      (σ.positiveDensity_trace_setIntegral ((bitComparison_ideal_dom W σ).trans hκν)
        MeasurableSet.univ).trans hσ1
  · intro t
    exact scaled_eveBlock_coherence R hR (fun i => X i t) (fun j => Y j t)
      (fun i => hXp i t) (fun j => hYp j t) (densityWeight μ ν t) (densityWeight_nonneg μ ν t)

end SecretKey

end

end OAI
