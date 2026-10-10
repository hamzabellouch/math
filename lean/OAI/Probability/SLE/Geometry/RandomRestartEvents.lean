import OAI.Probability.SLE.Gauge.StoppedTubePassage

namespace OAI

/-! Random geometric restrictions after restart. The actual restricted
restart law determines the joint law of the stopped past and the fresh path.
Consequently a past-measurable family of positive-probability passage events
has positive conditional probability, without countable past certificates. -/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

theorem restart_joint_law
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν) :
    @Measure.map Ω (Ω × X) mΩ (m.prod mX) (fun ω => (ω, Y ω)) P =
      @Measure.prod Ω X m mX (P.trim hm) ν := by
  have hj : @Measurable Ω (Ω × X) mΩ (m.prod mX) (fun ω => (ω, Y ω)) :=
    (measurable_id'' hm).prodMk hY
  apply @Measure.ext_prod Ω X m mX
  intro A B hA hB
  rw [Measure.map_apply hj (hA.prod hB), Measure.prod_prod,
    trim_measurableSet_eq hm hA]
  have he : (fun ω => (ω, Y ω)) ⁻¹' (A ×ˢ B) = Y ⁻¹' B ∩ A := by
    ext ω
    simp only [mem_preimage, mem_prod, mem_inter_iff, and_comm]
  rw [he, ← Measure.restrict_apply (hY hB), ← Measure.map_apply hY hB,
    hlaw A hA, Measure.smul_apply, smul_eq_mul]

theorem restart_lintegral_random_test
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ f) :
    (∫⁻ ω, f (ω, Y ω) ∂P) = ∫⁻ ω, ∫⁻ x, f (ω, x) ∂ν ∂P := by
  have hj : @Measurable Ω (Ω × X) mΩ (m.prod mX) (fun ω => (ω, Y ω)) :=
    (measurable_id'' hm).prodMk hY
  calc
    _ = @lintegral (Ω × X) (m.prod mX)
        (@Measure.map Ω (Ω × X) mΩ (m.prod mX) (fun ω => (ω, Y ω)) P) f :=
      (@lintegral_map Ω (Ω × X) mΩ (m.prod mX) P f (fun ω => (ω, Y ω)) hf hj).symm
    _ = @lintegral (Ω × X) (m.prod mX) (@Measure.prod Ω X m mX (P.trim hm) ν) f := by
      rw [@restart_joint_law Ω X mΩ mX P inferInstance ν inferInstance m hm Y hY hlaw]
    _ = @lintegral Ω m (P.trim hm) (fun ω => ∫⁻ x, f (ω, x) ∂ν) :=
      lintegral_prod f hf.aemeasurable
    _ = _ := lintegral_trim hm hf.lintegral_prod_right'

/-- Conditional integration for a genuinely random restriction on the
fresh path, provided its dependence on the stopped past is measurable. -/
theorem restart_condLExp_random_test
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (f : Ω × X → ℝ≥0∞) (hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ f) :
    (fun ω => ∫⁻ x, f (ω, x) ∂ν) =ᵐ[P]
      P⁻[(fun ω => f (ω, Y ω)) | m] := by
  apply ae_eq_condLExp hm P _ hf.lintegral_prod_right'
  intro A hA
  let fA : Ω × X → ℝ≥0∞ := (A ×ˢ (univ : Set X)).indicator f
  have hfA : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ fA :=
    hf.indicator (hA.prod MeasurableSet.univ)
  have h := @restart_lintegral_random_test Ω X mΩ mX P inferInstance ν inferInstance
    m hm Y hY hlaw fA hfA
  have hleft : (fun ω => fA (ω, Y ω)) = A.indicator (fun ω => f (ω, Y ω)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [fA, hω]
  have hright : (fun ω => ∫⁻ x, fA (ω, x) ∂ν) =
      A.indicator (fun ω => ∫⁻ x, f (ω, x) ∂ν) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [fA, hω]
  rw [hleft, hright, lintegral_indicator (hm A hA), lintegral_indicator (hm A hA)] at h
  exact h.symm

theorem conditional_passage_positive_of_random_sections
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure X) [IsFiniteMeasure ν]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (Y : Ω → X) (hY : Measurable[mΩ] Y)
    (hlaw : ∀ A : Set Ω, MeasurableSet[m] A →
      @Measure.map Ω X mΩ mX Y (P.restrict A) = P A • ν)
    (E : Set Ω) (C : Set (Ω × X)) (hC : @MeasurableSet (Ω × X) (m.prod mX) C)
    (hpositive : ∀ᵐ ω ∂P, ω ∈ E → 0 < ν {x | (ω, x) ∈ C}) :
    ∀ᵐ ω ∂P, ω ∈ E →
      0 < P⁻[({ω | (ω, Y ω) ∈ C}).indicator (fun _ => 1) | m] ω := by
  have hf : @Measurable (Ω × X) ℝ≥0∞ (m.prod mX) _ (C.indicator (fun _ => 1)) := by
    let : MeasurableSpace (Ω × X) := m.prod mX
    exact measurable_const.indicator hC
  have he := @restart_condLExp_random_test Ω X mΩ mX P inferInstance ν inferInstance m hm Y hY hlaw
    (C.indicator (fun _ => 1)) hf
  filter_upwards [he, hpositive] with ω hω hp hωE
  have hs : MeasurableSet {x | (ω, x) ∈ C} := hC.preimage measurable_prodMk_left
  have hsection : (∫⁻ x, C.indicator (fun _ => 1) (ω, x) ∂ν) = ν {x | (ω, x) ∈ C} := by
    have heq : (fun x => C.indicator (fun _ => (1 : ℝ≥0∞)) (ω, x)) =
        ({x | (ω, x) ∈ C}).indicator (fun _ => 1) := by
      funext x
      rfl
    rw [heq, lintegral_indicator hs, setLIntegral_const, one_mul]
  rw [hsection] at hω
  exact hω ▸ hp hωE

end SLEExactGauge

end

end OAI
