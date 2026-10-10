import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSubgroupRealization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLocalProduct
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConjugationLift

namespace OAI

/-! # Ambient Cartan factorization

The simply connected nilpotent factors have normal inclusions, a conjugation
action, surjective multiplication, compact lifts and a precisely described
overlap.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExpG : IsGroupExponential ExpG)
  (dixmier : DixmierExponentialInput (E := EG) (G := G))
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace N] [ChartedSpace EN N] [Group N] [LieGroup (𝓘(ℝ, EN)) ⊤ N]
  [T2Space N] [SimplyConnectedSpace N] [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (haarN : NilpotentExponentialHaarInput EN N)
  (integrateN : NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G))
  (normality : NilpotentIdealNormalityInput (EN := EN) (N := N) (EG := EG) (G := G))
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED] [FiniteDimensional ℝ ED]
  [TopologicalSpace D] [ChartedSpace ED D] [Group D] [LieGroup (𝓘(ℝ, ED)) ⊤ D]
  [T2Space D] [SimplyConnectedSpace D] [MeasurableSpace D] [BorelSpace D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hExpD : IsGroupExponential ExpD)
  (haarD : NilpotentExponentialHaarInput ED D)
  (integrateD : NilpotentLieIntegrationInput (EN := ED) (N := D) (EG := EG) (G := G))

include T hExpG dixmier hExpN haarN integrateN normality hExpD haarD integrateD in
/-- Cartan factors with their exact ambient maps and overlap. The local and
global factorization conclusions are proved, not included in a Lie input. -/
theorem exists_ambient_cartan_factorization :
    ∃ (ι : N →* G) (κ : D →* G) (φ : D →* MulAut N),
      Topology.IsClosedEmbedding ι ∧ Topology.IsClosedEmbedding κ ∧
      (∀ x : cartanRootIdeal H, ι (ExpN (eN x)) = ExpG x) ∧
      (∀ x : H, κ (ExpD (eD x)) = ExpG x) ∧
      ι.range.Normal ∧
      (∀ d n, ι (φ d n) = κ d * ι n * (κ d)⁻¹) ∧
      Function.Surjective (fun p : N × D => ι p.1 * κ p.2) ∧
      (∀ K : Set G, IsCompact K → ∃ C : Set (N × D), IsCompact C ∧
        K ⊆ (fun p : N × D => ι p.1 * κ p.2) '' C) ∧
      Set.range ι ∩ Set.range κ = ExpG ''
        ((cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩
          (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G))) := by
  let _ : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  let _ : IsTopologicalGroup D := topologicalGroup_of_lieGroup (𝓘(ℝ, ED)) ⊤
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, EG)) ⊤
  let _ : LocallyCompactSpace N := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, EN))
  let _ : LocallyCompactSpace D := Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, ED))
  obtain ⟨ι, hi, hismooth, hid, hiExp, hirange, hinormal⟩ :=
    exists_closed_normal_cartanRootIdeal_inclusion T H ExpG hExpG dixmier
      ExpN hExpN haarN integrateN normality eN
  obtain ⟨κ, hk, hksmooth, hkd, hkExp, hkrange⟩ :=
    exists_closed_cartan_inclusion T H ExpG hExpG dixmier ExpD hExpD haarD integrateD eD
  let φ := conjugationLiftOfNormal ι κ hi.injective hinormal
  have hconj (d : D) (n : N) : ι (φ d n) = κ d * ι n * (κ d)⁻¹ :=
    conjugationLiftOfNormal_spec ι κ hi.injective hinormal d n
  have hlocal := cartanFactorProduct_map_nhds_one ι κ T H eN eD hismooth hksmooth
    (fun x => by exact hid x)
    (fun x => by exact hkd x)
  obtain ⟨hsurj, hlifts⟩ := factorProduct_surjective_and_compact_lifts ι κ φ hconj hlocal
  obtain ⟨cG, hcG⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 ExpG hExpG
  have hginj : Function.Injective ExpG := by
    rw [← show (cG : _ → G) = ExpG from funext hcG]
    exact cG.injective
  exact ⟨ι, κ, φ, hi, hk, hiExp, hkExp, hinormal, hconj, hsurj, hlifts,
    exponential_factor_intersection ExpG hginj ι κ _ _ hirange hkrange⟩

end PolycyclicRecognition

end

end OAI
