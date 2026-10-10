import OAI.MeasureTheory.Falconer.Fourier.PositiveFourier
import OAI.MeasureTheory.Falconer.Measures.DescriptorProduct
import OAI.MeasureTheory.Falconer.Estimates.PrunedVariation
import OAI.MeasureTheory.Falconer.Recursion.ProfileNear

namespace OAI

/-! # Positive lowpass comparison for the actual masked distance law

The comparison is made between positive measures before taking Fourier
transforms. All old masks remain in the weighted distance pushforward.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

/-- A lower bound only on the tested set suffices for positive domination. -/
theorem restrict_smul_le_withDensity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : Set X) (hG : MeasurableSet G)
    (w : X → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ᵐ x ∂μ, x ∈ G → c ≤ w x) :
    c • μ.restrict G ≤ μ.withDensity w := by
  rw [← withDensity_const,← withDensity_indicator hG]
  apply withDensity_mono
  filter_upwards [h] with x hx
  by_cases hxG : x ∈ G
  · simpa only [indicator_of_mem hxG] using hx hxG
  · simp only [indicator_of_notMem hxG]
    exact bot_le

theorem dyadic_collision_fourier_of_domination (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (c : ℝ), 0 ≤ c → ENNReal.ofReal c • μ ≤ ν →
      ∀ (a t : ℕ), a ≤ t →
      c^2 * (2:ℝ)^(t-a) * (μ.prod μ).real
        {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t), ‖charFun ν r‖^2 := by
  obtain ⟨C,hC,hb⟩ := dyadic_distance_collision_fourier d
  refine ⟨C,hC,?_⟩
  intro μ ν _ _ c hc hdom a t hat
  have hp := Measure.prod_mono hdom hdom
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,
    ← ENNReal.ofReal_mul hc] at hp
  have hr := ENNReal.toReal_mono (measure_ne_top (ν.prod ν) _)
    (hp {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t})
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hc hc)] at hr
  have hh := (mul_le_mul_of_nonneg_left hr (show 0 ≤ (2:ℝ)^(t-a) by positivity)).trans
    (hb ν a t hat)
  simpa only [measureReal_def,pow_two,mul_assoc,mul_left_comm,mul_comm] using hh

noncomputable def descriptorPairWeight (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (z : Space d × Space d) : ℝ :=
  (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2)) *
    descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1 (normalizeToSphere w₀ (z.1-z.2)) *
    descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2 (normalizeToSphere w₀ (z.1-z.2))

theorem descriptorPairWeight_measurable (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) :
    Measurable (descriptorPairWeight w₀ Q ρ m N σ J i a B S) := by
  have hw := (normalizeToSphere_measurable w₀).comp (measurable_fst.sub measurable_snd)
  exact ((measurable_fst.dist measurable_snd).mul_const _).pow_const _ |>.mul
    ((descriptorProduct_measurable Q ρ (fun u => m (u/N)) N σ J i B S).comp (measurable_fst.prodMk hw)) |>.mul
    ((descriptorProduct_measurable Q ρ (fun u => m (u/N)) N σ J i B S).comp (measurable_snd.prodMk hw))

noncomputable def maskedCellDistance (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (X Y : DyadicCube d) : Measure ℝ :=
  (((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).withDensity
    (fun z => ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 *
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z))).map
    (fun z => dist z.1 z.2)

/-- Core masks preserve the original tested pairs; only their distance weight
enters the domination constant. -/
theorem maskedCellDistance_dominates
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d))
    (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (X Y : DyadicCube d) (G : Set (Space d × Space d)) (hG : MeasurableSet G)
    (c : ℝ) (_hc : 0 ≤ c)
    (hcore : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z ∈ G →
      descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1 (normalizeToSphere w₀ (z.1-z.2)) = 1 ∧
      descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2 (normalizeToSphere w₀ (z.1-z.2)) = 1)
    (hweight : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z ∈ G →
      c ≤ (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2))) :
    ENNReal.ofReal ((profileModelMass m N a)⁻¹^2*c) • testedCellDistance ρ ρ X Y G ≤
      maskedCellDistance w₀ Q ρ m N σ J i a B S X Y := by
  have hh := restrict_smul_le_withDensity ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier))
    G hG (fun z => ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 *
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z))
    (ENNReal.ofReal ((profileModelMass m N a)⁻¹^2*c)) (by
      filter_upwards [hcore,hweight] with z hz hw
      intro hzg
      obtain ⟨h₁,h₂⟩ := hz hzg
      apply ENNReal.ofReal_le_ofReal
      simpa only [descriptorPairWeight,h₁,h₂,mul_one] using
        mul_le_mul_of_nonneg_left (hw hzg) (sq_nonneg _))
  have hm := Measure.map_mono hh (show Measurable (fun z : Space d × Space d => dist z.1 z.2) by fun_prop)
  rw [Measure.map_smul _ (by fun_prop)] at hm
  simpa only [testedCellDistance,testedCellPair,maskedCellDistance] using hm

theorem profileModelMass_inverse_four (m : ℝ → ℝ) (N a : ℕ) :
    ((profileModelMass m N a)⁻¹)^4 = ((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
  unfold profileModelMass
  rw [← Real.rpow_neg (by positivity : 0 ≤ (2:ℝ)^N),← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : 0 ≤ (2:ℝ)^N)]
  congr 1
  ring

theorem masked_distance_collision_lowpass (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w₀ : Sphere d) (Q : DyadicCube d)
      (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ)
      (σ : ℝ) (J i a t : ℕ), a ≤ t →
      ∀ (B : Finset PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
        (X Y : DyadicCube d) (G : Set (Space d × Space d)), MeasurableSet G →
      ∀ (c : ℝ), 0 ≤ c →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z ∈ G →
        descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1 (normalizeToSphere w₀ (z.1-z.2)) = 1 ∧
        descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2 (normalizeToSphere w₀ (z.1-z.2)) = 1) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z ∈ G →
        c ≤ (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2))) →
      ∀ [IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y)],
      c^2*((2:ℝ)^N)^(4*m ((a:ℝ)/N))*(2:ℝ)^(t-a) *
        ((testedCellDistance ρ ρ X Y G).prod (testedCellDistance ρ ρ X Y G)).real
          {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^t} ≤
      (C/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^t) ((2:ℝ)^t),
        ‖charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖^2 := by
  obtain ⟨C,hC,hb⟩ := dyadic_collision_fourier_of_domination d
  refine ⟨C,hC,?_⟩
  intro w₀ Q ρ _ m N σ J i a t hat B S X Y G hG c hc hcore hweight _
  have hd := maskedCellDistance_dominates w₀ Q ρ m N σ J i a B S X Y G hG c hc hcore hweight
  have hh := hb (testedCellDistance ρ ρ X Y G) (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y)
    ((profileModelMass m N a)⁻¹^2*c) (mul_nonneg (sq_nonneg _) hc) hd a t hat
  have he : ((profileModelMass m N a)⁻¹^2*c)^2 = c^2*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
    rw [mul_pow,← pow_mul,show 2*2 = 4 from rfl,profileModelMass_inverse_four]
    ring
  simpa only [he,mul_assoc] using hh

end Falconer

end OAI
