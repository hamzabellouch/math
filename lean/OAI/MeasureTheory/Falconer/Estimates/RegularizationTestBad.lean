import OAI.MeasureTheory.Falconer.Estimates.AllTestsRestoration
import OAI.MeasureTheory.Falconer.Estimates.ClassBadRecombination

namespace OAI

/-! # Recombining the actual class test failures on the original product law -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem regularization_class_representative (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) {T : List ℕ} (hT : T ∈ regularizationIndex Q μ N B t) :
    ∃ p ∈ regularizationLeaves Q μ N, regularizationLabel Q μ N B p = T :=
  Finset.mem_image.mp (Finset.mem_filter.mp hT).1

theorem sourceClass_eq_normalized (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (p : CellPath d) (T : List ℕ) (hp : regularizationLabel Q μ N B p = T) :
    sourceClass Q μ N B p =
      normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T := by
  unfold sourceClass
  rw [hp]

noncomputable def regularizationTestBad (w₀ : Sphere d) (Q : DyadicCube d)
    (μ : Measure (Space d)) (N B : ℕ) (t : ℝ≥0∞) (σ : ℝ) (J : ℕ)
    (p : List ℕ → CellPath d) (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  ⋃ T ∈ regularizationIndex Q μ N B t,
    (regularizationSet Q μ N B T ×ˢ univ) ∩
      allDescriptorTestBad w₀ Q (sourceClass Q μ N B (p T))
        (fun u => sourceUnitProfile Q μ N B (p T) (u/N)) N σ J G

theorem regularizationTestBad_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsProbabilityMeasure μ]
    (N B : ℕ) (t : ℝ≥0∞) (σ : ℝ) (J : ℕ) (p : List ℕ → CellPath d)
    (hp : ∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N)
    (hQ : 0 < Q.side) {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (regularizationTestBad w₀ Q μ N B t σ J p G) := by
  apply Finset.measurableSet_biUnion
  intro T hT
  let : IsProbabilityMeasure (sourceClass Q μ N B (p T)) :=
    regularization_class_probability Q hQ μ N B (hp T hT)
  exact ((regularizationSet_measurable Q μ N B T).prod MeasurableSet.univ).inter
    (allDescriptorTestBad_measurable w₀ Q _ _ N σ J hG)

theorem uniform_regularization_test_bad_mass {σ : ℝ} (hσ : 0 < σ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ ν : Measure (Space d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ B : ℕ, 0 < B → (B:ℝ) ≤ σ*(N:ℝ) →
        (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^σ →
      ∀ t : ℝ≥0∞, 0 < t → ∀ p : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N) →
      (∀ T ∈ regularizationIndex Q μ N B t, regularizationLabel Q μ N B (p T) = T) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)), MeasurableSet G →
      (∀ᵐ x ∂μ, ∀ u : Space d, ∀ r : ℝ,
        ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        originalRadialSphereLaw w₀ ν G x {w : Sphere d | dist (w:Space d) u < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ J : ℕ, (μ.prod ν) (regularizationTestBad w₀ Q μ N B t σ J p G) ≤
        (2*(N+1)^2:ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨N₀,h₀⟩ := uniform_source_test_bad_mass (d := d) hσ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ μ ν _ _ B hB hwidth hlarge t ht p hp hlabel w₀ G hG hcap J
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  apply retained_classes_bad_mass Q hside μ ν
    (fun P hP => (Finset.mem_filter.mp hP).1)
    (regularizationLabel Q μ N B) (regularizationIndex Q μ N B t)
    (fun T hT => (Finset.mem_filter.mp hT).1)
  · intro T hT
    exact (ht.trans_le (Finset.mem_filter.mp hT).2).ne'
  · intro T hT
    let : IsProbabilityMeasure (sourceClass Q μ N B (p T)) :=
      regularization_class_probability Q hside μ N B (hp T hT)
    exact allDescriptorTestBad_measurable w₀ Q _ _ N σ J hG
  · intro T hT
    change ((normalizedClass Q μ (regularizationLeaves Q μ N)
      (regularizationLabel Q μ N B) T).prod ν)
      (allDescriptorTestBad w₀ Q (sourceClass Q μ N B (p T))
        (fun u => sourceUnitProfile Q μ N B (p T) (u/N)) N σ J G) ≤ _
    rw [← sourceClass_eq_normalized Q μ N B (p T) T (hlabel T hT)]
    apply allDescriptorTestBad_mass
    intro b hb
    exact h₀ N hN Q hQ μ B hB hwidth hlarge (p T) (hp T hT) b hb ν w₀ G hG
      ((sourceClass_absolutelyContinuous Q μ N B (p T)).ae_le hcap) J

end Falconer.Regularization

end OAI
