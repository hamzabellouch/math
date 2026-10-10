import OAI.MeasureTheory.Falconer.Estimates.DescriptorMasks
import OAI.MeasureTheory.Falconer.Estimates.AllDimensionalParallelExceptional
import OAI.MeasureTheory.Falconer.Geometry.ProjectionExceptional
import OAI.MeasureTheory.Falconer.Estimates.RegularizationProperties

namespace OAI

/-! # Exceptional-direction bounds for each actual level-zero descriptor

The angular measure is a restriction of the original opposite marginal;
its cap constant is never divided by a class mass.
-/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor descriptorAnchor)
variable {d : ℕ}

 theorem uniform_descriptor_exceptional {σ : ℝ} (hσ : 0 < σ) :
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
      ∀ J : ℕ,
      ν (descriptorGoodDirections Q (sourceClass Q μ N B p₀)
        (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J 0 P b)ᶜ ≤
        ENNReal.ofReal (((2:ℝ)^N)^(-σ)) := by
  obtain ⟨Np,hp⟩ := uniform_parallel_exceptional (d := d) hσ
  obtain ⟨Nt,ht⟩ := uniform_projection_exceptional (d := d) hσ
  refine ⟨max 1 (max Np Nt),?_⟩
  intro N hN Q hQ μ _ B hB hwidth hlarge p₀ hp₀ b hb P hP hocc ν hmass hball J
  have hNp : 0 < N := by omega
  have hwidthEq (n : ℕ) : angularTestWidth N σ J 0 n =
      2*((2:ℝ)^N)^(500*σ)/(2:ℝ)^n := by
    rw [angularTestWidth_zero]
    ring
  cases b with
  | parallel g p =>
    have hh := hp N (by omega) Q hQ μ B hB hwidth hlarge p₀ hp₀
      g p hb.1 hb.2 P hP hocc ν hmass hball
    simpa only [descriptorGoodDirections,hwidthEq,sourceUnitProfile_at_depth Q μ hNp] using hh
  | projection p t =>
    have hh := ht N (by omega) Q hQ μ B hB hwidth hlarge p₀ hp₀
      p t hb.1 hb.2 P hP hocc ν hmass hball
    have hgood : descriptorGoodDirections Q (sourceClass Q μ N B p₀)
        (fun u => sourceUnitProfile Q μ N B p₀ (u/N)) N σ J 0 P (.projection p t) =
        projectionGoodSet (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant P).carrier)
          (2*((2:ℝ)^N)^(500*σ)/(2:ℝ)^t)
          ((1/(2:ℝ)^(t-p))*((2:ℝ)^N)^(
            profileDrop (sourceProfile Q μ N B p₀) N ((d:ℝ)/2) p t+1000*((d:ℝ)+1)*σ)) := by
      simp only [descriptorGoodDirections,conditionalProjectionGoodSet,ite_eq_left hocc,
        hwidthEq,profileDrop,sourceUnitProfile_at_depth Q μ hNp]
    rw [hgood]
    exact hh

end Falconer.Regularization

end OAI
