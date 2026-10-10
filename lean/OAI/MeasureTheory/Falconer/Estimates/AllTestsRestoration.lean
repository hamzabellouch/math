import OAI.MeasureTheory.Falconer.Estimates.DescriptorTestBad

namespace OAI

/-! # One exceptional set restores every policy descriptor at the scale -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
variable {d : ℕ}

noncomputable def allDescriptorTestBad (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (G : Set (Space d × Space d)) : Set (Space d × Space d) :=
  ⋃ b ∈ validDescriptors N, descriptorTestBad w₀ Q ρ profile N σ J b G

 theorem allDescriptorTestBad_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J : ℕ) {G : Set (Space d × Space d)} (hG : MeasurableSet G) :
    MeasurableSet (allDescriptorTestBad w₀ Q ρ profile N σ J G) :=
  Finset.measurableSet_biUnion _ (fun b _ =>
    descriptorTestBad_measurable w₀ Q ρ profile N σ J b hG)

 theorem allDescriptorTestBad_mass (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ ν : Measure (Space d)) (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J : ℕ)
    (G : Set (Space d × Space d)) {ε : ℝ≥0∞}
    (hbad : ∀ b, descriptorValid N b →
      (ρ.prod ν) (descriptorTestBad w₀ Q ρ profile N σ J b G) ≤ ε) :
    (ρ.prod ν) (allDescriptorTestBad w₀ Q ρ profile N σ J G) ≤
      (2*(N+1)^2:ℕ)*ε := by
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ validDescriptors N, ε := Finset.sum_le_sum
      (fun b hb => hbad b ((mem_validDescriptors N b).mp hb))
    _ = ((validDescriptors N).card:ℝ≥0∞)*ε := by simp
    _ ≤ _ := mul_le_mul' (by exact_mod_cast validDescriptors_card N) le_rfl

 theorem normalizeToSphere_neg (w₀ : Sphere d) {v : Space d} (hv : v ≠ 0) :
    normalizeToSphere w₀ (-v) = oppositePole (normalizeToSphere w₀ v) := by
  apply Subtype.ext
  simp only [normalizeToSphere_coe_of_ne w₀ (neg_ne_zero.mpr hv),oppositePole_coe,
    normalizeToSphere_coe_of_ne w₀ hv,NormedSpace.normalize_neg]

 theorem uniform_all_tests_restoration {σ : ℝ} (hσ : 0 < σ) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (profile : ℝ → ℝ)
        (F : Finset PolicyDescriptor), F ⊆ validDescriptors N →
      ∀ S : PolicyDescriptor → Finset (Sphere d),
        (∀ b ∈ F, ∀ w : Sphere d, ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (w₀ : Sphere d) (G : Set (Space d × Space d)) (x y : Space d),
      x ∈ Q.carrier → x ≠ y → (x,y) ∈ G →
      (x,y) ∉ allDescriptorTestBad w₀ Q ρ profile N σ J G →
      descriptorAmbientProduct Q ρ profile N σ J 0 F S x (NormedSpace.normalize (x-y)) = 1 := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorProduct_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ profile F hF S hS w₀ G x y hx hxy hG hgood
  have hne : y-x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hneg : normalizeToSphere w₀ (x-y) = oppositePole (normalizeToSphere w₀ (y-x)) := by
    simpa only [neg_sub] using normalizeToSphere_neg w₀ hne
  have hcore := h₀ N hN Q hQ ρ profile F
    (fun b hb => (mem_validDescriptors N b).mp (hF hb)) S hS 0 x hx
    (normalizeToSphere w₀ (x-y)) (by
      intro b hb
      rw [hneg,descriptorEndpointGood_opposite]
      by_contra hn
      apply hgood
      exact mem_iUnion₂.mpr ⟨b,hF hb,hG,hn⟩)
  rw [← descriptorAmbientProduct_sphere] at hcore
  simpa only [normalizeToSphere_coe_of_ne w₀ (sub_ne_zero.mpr hxy)] using hcore

end Falconer

end OAI
