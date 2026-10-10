import OAI.MeasureTheory.Falconer.Fourier.JetStateStationary

namespace OAI

/-! # The incoming stationary pole retains the same descriptor tests -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)
open scoped Topology

 theorem perpendicularPart_neg_direction {d : ℕ} (w v : Space d) :
    perpendicularPart (-w) v = perpendicularPart w v := by
  simp [perpendicularPart,inner_neg_left]

 theorem finiteTubeCount_opposite {d : ℕ} {ι : Type*} (S : Finset ι)
    (v : ι → Space d) (W : ℝ) (w : Sphere d) :
    finiteTubeCount S v W (oppositePole w) = finiteTubeCount S v W w := by
  classical
  unfold finiteTubeCount
  congr 1
  apply Finset.filter_congr
  intro a _
  simp only [angularTubeEvent,Set.mem_ofPred_eq,oppositePole_coe,
    perpendicularPart_neg_direction]

 theorem projectionCollision_neg_direction {d : ℕ} (μ : Measure (Space d))
    (w : Space d) (W : ℝ) : projectionCollision μ (-w) W = projectionCollision μ w W := by
  simp only [projectionCollision,inner_neg_right,abs_neg]

 theorem descriptorGoodDirections_opposite {d : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (P : List (Fin d → Bool)) (b : PolicyDescriptor)
    (w : Sphere d) :
    oppositePole w ∈ descriptorGoodDirections Q ρ m N σ J i P b ↔
      w ∈ descriptorGoodDirections Q ρ m N σ J i P b := by
  classical
  cases b with
  | parallel g p =>
    simp only [descriptorGoodDirections,Regularization.parallelGoodSet]
    split_ifs <;> simp only [mem_ofPred_eq,Regularization.parallelTestCount,
      finiteTubeCount_opposite,mem_empty_iff_false]
  | projection p t =>
    simp only [descriptorGoodDirections,Regularization.conditionalProjectionGoodSet]
    split_ifs <;> simp only [projectionGoodSet,mem_ofPred_eq,oppositePole_coe,
      projectionCollision_neg_direction,mem_empty_iff_false]

 theorem descriptorEndpointGood_opposite {d : ℕ}
    (Q : DyadicCube d) (ρ : Measure (Space d)) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Space d) (w : Sphere d) :
    (x,oppositePole w) ∈ descriptorEndpointGood Q ρ m N σ J i b ↔
      (x,w) ∈ descriptorEndpointGood Q ρ m N σ J i b := by
  simp only [descriptorEndpointGood,mem_ofPred_eq,descriptorGoodDirections_opposite]

 theorem DescriptorJetSymbol.pair_incoming_stationary_support {m₀ K L : ℕ}
    {F : Finset PolicyDescriptor} {Dq : ℝ} (f : DescriptorJetSymbol (m₀+1) K L F Dq)
    (Q : DyadicCube (m₀+3)) (ρ : Measure (Space (m₀+3))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m₀+3)))
    (A : ℝ) (x y : Space (m₀+3)) (w : Sphere (m₀+3)) (j : ℕ)
    (hne : actualStationaryCoefficient m₀ j
      (antipodalConjugate (f.pairAmbient Q ρ m N σ J i S A x y)) w ≠ 0) :
    ∀ b ∈ F, (x,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b ∧
      (y,w) ∈ descriptorEndpointGood Q ρ m N σ J (i+1) b := by
  have hneg : Filter.Tendsto (fun z : Space (m₀+3) => -z)
      (𝓝 (w:Space (m₀+3))) (𝓝 (oppositePole w:Space (m₀+3))) :=
    continuous_neg.continuousAt
  intro b hb
  constructor
  · by_contra hbad
    have hbad' : (x,oppositePole w) ∉ descriptorEndpointGood Q ρ m N σ J (i+1) b :=
      fun h => hbad ((descriptorEndpointGood_opposite Q ρ m N σ J (i+1) b x w).mp h)
    have hz := (f.ambient_eventually_zero Q ρ m N σ J i S A x (oppositePole w) hb hbad').comp_tendsto hneg
    have he : antipodalConjugate (f.pairAmbient Q ρ m N σ J i S A x y) =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      change f.ambient Q ρ m N σ J i S A x (-z) = 0 at hz
      simp only [antipodalConjugate,DescriptorJetSymbol.pairAmbient,hz,Pi.zero_apply,zero_mul,star_zero]
    exact hne ((actualStationaryCoefficient_local m₀ j w he).trans
      (actualStationaryCoefficient_zero_amplitude m₀ j w))
  · by_contra hbad
    have hbad' : (y,oppositePole w) ∉ descriptorEndpointGood Q ρ m N σ J (i+1) b :=
      fun h => hbad ((descriptorEndpointGood_opposite Q ρ m N σ J (i+1) b y w).mp h)
    have hz := (f.ambient_eventually_zero Q ρ m N σ J i S A y (oppositePole w) hb hbad').comp_tendsto hneg
    have he : antipodalConjugate (f.pairAmbient Q ρ m N σ J i S A x y) =ᶠ[𝓝 (w:Space (m₀+3))] 0 := by
      filter_upwards [hz] with z hz
      change f.ambient Q ρ m N σ J i S A y (-z) = 0 at hz
      simp only [antipodalConjugate,DescriptorJetSymbol.pairAmbient,hz,Pi.zero_apply,star_zero,mul_zero]
    exact hne ((actualStationaryCoefficient_local m₀ j w he).trans
      (actualStationaryCoefficient_zero_amplitude m₀ j w))

end Falconer

end OAI
