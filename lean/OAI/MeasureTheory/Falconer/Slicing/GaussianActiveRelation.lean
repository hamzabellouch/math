import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedPair
import OAI.MeasureTheory.Falconer.Slicing.GaussianActiveLoss

namespace OAI

/-! # Original-pair incidence after the active-cover deletion -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def gaussianActiveRelation (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ)
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
  {q | q.2 ∈ E ∧ if good then
      (gaussianActiveAnchorCount q.1.1 (J q.2.2) a R q.1.2 : ℝ≥0∞) ≤ T
    else T < (gaussianActiveAnchorCount q.1.1 (J q.2.2) a R q.1.2 : ℝ≥0∞)}

omit [Fintype ι] in
theorem gaussianActiveRelation_measurable (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space d) (R : ℝ) (T : ℝ≥0∞) (good : Bool) :
    MeasurableSet (gaussianActiveRelation (h := h) E J a R T good) := by
  have hm := (gaussianActiveFamily_measurable (h := h) J hJ a R).comp
    (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
      (q.1,q.2.2)) from by fun_prop)
  cases good
  · exact (hE.preimage measurable_snd).inter (measurableSet_lt measurable_const hm)
  · exact (hE.preimage measurable_snd).inter (measurableSet_le hm measurable_const)

theorem gaussian_active_bad_integral
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P) :
    (∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M
      (gaussianActiveRelation E J a R T false) p ∂(gaussianRows d h).prod volume) ≤
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  rw [lintegral_prod _ (show AEMeasurable
    (gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T false))
    ((gaussianRows d h).prod volume) from
    (gaussianPrunedPairMass_measurable μ ν δ r TP TD M _
      (gaussianActiveRelation_measurable E hE J hJ a R T false)).aemeasurable)]
  calc
    _ ≤ ∫⁻ _ : Fin h → Space d, P*(N*ENNReal.ofReal ((2*R)^h)/T)*M ∂gaussianRows d h := by
      apply lintegral_mono
      intro A
      have he (z : Space h) : {t | ((A,z),t) ∈ gaussianActiveRelation E J a R T false} =
          E ∩ (univ ×ˢ {w | T < (gaussianActiveAnchorCount A (J w) a R z : ℝ≥0∞)}) := by
        ext t
        simp [gaussianActiveRelation]
      simp only [gaussianPrunedPairMass,he]
      exact gaussian_active_loss_in_row μ ν δ r TP TD M A E J hJ a hR hN hT hTfin
        (fun z => hP (A,z))
    _ = _ := by rw [lintegral_const,measure_univ,mul_one]

theorem gaussian_active_pruning_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ξ : Measure ((Fin h → Space d) × Space h)) (hξ : ξ ≤ (gaussianRows d h).prod volume)
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (J : Sphere d → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w}) (a : κ → Space d)
    {R : ℝ} (hR : 0 ≤ R) {N T P : ℝ≥0∞} (hN : ∀ w, ((J w).card : ℝ≥0∞) ≤ N)
    (hT : T ≠ 0) (hTfin : T ≠ ∞)
    (hP : ∀ p : (Fin h → Space d) × Space h,
      ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)) univ ≤ P) :
    (∫⁻ p, gaussianPrunedIncidence μ ν δ r TP TD M E p ∂ξ) ≤
      (∫⁻ p, gaussianPrunedPairMass μ ν δ r TP TD M (gaussianActiveRelation E J a R T true) p ∂ξ) +
      P*(N*ENNReal.ofReal ((2*R)^h)/T)*M := by
  let f := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M (gaussianActiveRelation E J a R T true)
  let g := gaussianPrunedPairMass (h := h) μ ν δ r TP TD M (gaussianActiveRelation E J a R T false)
  have hf : Measurable f := gaussianPrunedPairMass_measurable μ ν δ r TP TD M _
    (gaussianActiveRelation_measurable E hE J hJ a R T true)
  have hg : (∫⁻ p, g p ∂ξ) ≤ P*(N*ENNReal.ofReal ((2*R)^h)/T)*M :=
    (lintegral_mono' hξ le_rfl).trans
      (gaussian_active_bad_integral μ ν δ r TP TD M E hE J hJ a hR hN hT hTfin hP)
  calc
    _ ≤ ∫⁻ p, f p+g p ∂ξ := by
      apply lintegral_mono
      intro p
      apply (measure_mono (show E ⊆
        {t | (p,t) ∈ gaussianActiveRelation E J a R T true} ∪
        {t | (p,t) ∈ gaussianActiveRelation E J a R T false} from ?_)).trans (measure_union_le _ _)
      intro t ht
      rcases le_or_gt (gaussianActiveAnchorCount p.1 (J t.2) a R p.2 : ℝ≥0∞) T with hle | hgt
      · exact Or.inl ⟨ht,hle⟩
      · exact Or.inr ⟨ht,hgt⟩
    _ = (∫⁻ p, f p ∂ξ)+(∫⁻ p, g p ∂ξ) := lintegral_add_left hf _
    _ ≤ _ := add_le_add le_rfl hg

end Falconer

end OAI
