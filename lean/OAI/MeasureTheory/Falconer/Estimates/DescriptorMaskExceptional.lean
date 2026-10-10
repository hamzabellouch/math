import OAI.MeasureTheory.Falconer.Estimates.DescriptorExceptional

namespace OAI

/-! # The actual smooth mask loses only the exceptional-direction mass -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}

 theorem uniform_descriptor_mask_exceptional {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ], ∀ B : ℕ,
      0 < B → (B:ℝ) ≤ σ*(N:ℝ) → (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^σ →
      ∀ p₀ ∈ regularizationLeaves Q μ N, ∀ b : PolicyDescriptor, descriptorValid N b →
      ∀ P : CellPath d, P.length = descriptorAnchor b →
      0 < sourceClass Q μ N B p₀ (Q.descendant P).carrier →
      ∀ ν : Measure (Sphere d), ν univ ≤ 1 →
      (∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)^(-1:ℝ) ≤ r → r ≤ 1 →
        ν {w : Sphere d | dist (w:Space d) x < r} ≤
          ENNReal.ofReal (((2:ℝ)^N)^σ*r^((d:ℝ)/2))) →
      ∀ S : Finset (Sphere d),
        (∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ x ∈ (Q.descendant P).carrier,
      ν {w : Sphere d | descriptorMask Q (sourceClass Q μ N B p₀)
        (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J 0 b S x w ≠ 1} ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨Ne,he⟩ := uniform_descriptor_exceptional (d := d) hσ
  obtain ⟨Nc,hc⟩ := uniform_descriptorMask_core (d := d) hσ hJ
  refine ⟨max Ne Nc,?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ b hb P hP hocc ν hmass hball S hS x hx
  let ρ := sourceClass Q μ N B p₀
  let m := fun u => sourceUnitProfile Q μ N B p₀ (u/N)
  let : IsProbabilityMeasure ρ := regularization_class_probability Q (by rw [hQ]; norm_num) μ N B hp₀
  have hbad := he N (by omega) Q hQ μ B hB hwidth hlarge p₀ hp₀ b hb P hP hocc ν hmass hball J
  apply (measure_mono (show {w | descriptorMask Q ρ m N σ J 0 b S x w ≠ 1} ⊆
      (descriptorGoodDirections Q ρ m N σ J 0 P b)ᶜ from ?_)).trans hbad
  intro w hw hgood
  apply hw
  exact hc N (by omega) Q hQ ρ m b hb S hS 0 x (Q.descendant_subset P hx) w
    ((descriptorEndpointGood_on_cell Q ρ m N σ J 0 b P hP hx w).mpr hgood)

end Falconer.Regularization

end OAI
