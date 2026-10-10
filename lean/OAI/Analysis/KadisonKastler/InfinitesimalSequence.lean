import OAI.Analysis.KadisonKastler.TypeIIIUltraproduct
import OAI.Analysis.KadisonKastler.MatrixCommutantDistance

namespace OAI

/-! # Vanishing distance to the algebra plus its commutant

For a bounded sequence with asymptotically algebra-valued commutators,
Sakai's theorem supplies the algebra part and the constructed matrix
averaging supplies the commutant part. The full matrix corners here are
actual data; their existence is not silently assumed as a published input.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {K : ℕ → Type u} [∀ j, NormedAddCommGroup (K j)]
  [∀ j, InnerProductSpace ℂ (K j)] [∀ j, CompleteSpace (K j)]
  [∀ j, TopologicalSpace.SeparableSpace (K j)]

local instance infinitesimalSequenceSourceOrder (j : ℕ) (M : VonNeumannAlgebra (K j)) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance infinitesimalSequenceSourceStarOrder (j : ℕ) (M : VonNeumannAlgebra (K j)) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem typeIII_eventually_approximate_algebra_add_commutant
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (M : ∀ j, VonNeumannAlgebra (K j)) (hM : ∀ j, TypeIIIFactor (M j))
    (hDistance : ∀ j, PublishedBlockCommutantApproximation (Algebra (M j)) (K j))
    (E : ∀ j, Submodule ℂ (K j)) [∀ j, CompleteSpace (E j)]
    (F : ∀ j, FullMatrixCorner (E j)) (hF : ∀ j i k, (F j).entry i k ∈ M j)
    (ω : Ultrafilter ℕ) (T : VaryingBoundedSequence (fun j => K j →L[ℂ] K j))
    (hT : IsSelfAdjoint T) (ε : ℕ → ℝ)
    (hε : Tendsto ε (ω : Filter ℕ) (𝓝 0)) (hε0 : ∀ j, 0 ≤ ε j)
    {R : ℝ} (hR : ∀ j, ε j ≤ R)
    (happrox : ∀ j (x : Algebra (M j)), ∃ y : Algebra (M j),
      ‖T j * (x : K j →L[ℂ] K j) - (x : K j →L[ℂ] K j) * T j -
        (y : K j →L[ℂ] K j)‖ ≤ ε j * ‖x‖)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ j in (ω : Filter ℕ), ∃ a b : K j →L[ℂ] K j,
      a ∈ M j ∧ b ∈ (M j).commutant ∧ ‖T j - (a + b)‖ < η := by
  let : ∀ j, Nontrivial (Algebra (M j)) := fun j => (hM j).algebraNontrivial
  let : ∀ j, Nontrivial (K j →L[ℂ] K j) := fun j => ⟨⟨1, 0, (hM j).nonzero⟩⟩
  obtain ⟨a, ha, hlim⟩ := exists_typeIII_uniform_commutator_correction
    hSpectral hCompare hSakai M hM ω T hT ε hε hε0 hR happrox
  have hevent := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < η / 2 by positivity))
  filter_upwards [hevent] with j hj
  let D := T j - (a j : K j →L[ℂ] K j)
  let q := ‖commutatorAlong (M j).toStarSubalgebra.subtype D‖
  have hDj : IsSelfAdjoint D :=
    (IsSelfAdjoint.map (varyingSequenceEval (fun j => K j →L[ℂ] K j) j) hT).sub
      (IsSelfAdjoint.map (M j).toStarSubalgebra.subtype
        (IsSelfAdjoint.map (varyingSequenceEval (fun j => Algebra (M j)) j) ha))
  have hb : ∀ x ∈ M j, ‖D * x - x * D‖ ≤ q * ‖x‖ := by
    intro x hx
    exact (commutatorAlong (M j).toStarSubalgebra.subtype D).le_opNorm ⟨x, hx⟩
  obtain ⟨b, hbM, hclose⟩ := (F j).exists_commutant_approximation (M j) (hDistance j)
    (hF j) D hDj (norm_nonneg _) hb (η - q) (by change q < η / 2 at hj; linarith)
  refine ⟨a j, b, (a j).property, hbM, ?_⟩
  have he : T j - ((a j : K j →L[ℂ] K j) + b) = D - b := by dsimp [D]; abel
  rw [he]
  convert hclose using 1; ring

end

end KadisonKastler

end OAI
