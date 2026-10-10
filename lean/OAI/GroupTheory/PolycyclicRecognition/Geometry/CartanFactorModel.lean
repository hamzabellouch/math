import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentLieModel

namespace OAI

/-! # Construction of the two Cartan factor models

The only existence premises are the cited Lie correspondence specialized to
the actual root ideal and Cartan algebra. Integration, normality and global
charts are supplied by the separately named published inputs. All assertions
about the multiplication map are derived in `CartanFactorization`.
-/

noncomputable section

namespace PolycyclicRecognition

open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
  (ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G)

/-- The concrete group part of the manuscript's Cartan model. The ambient
overlap is retained, and all lifting conclusions refer to the actual map. -/
structure CartanFactorModel where
  N : NilpotentLieModel (cartanRootIdeal H)
  D : NilpotentLieModel H
  ExpN : GroupLieAlgebra (𝓘(ℝ, N.modelSpace)) N.carrier → N.carrier
  ExpD : GroupLieAlgebra (𝓘(ℝ, D.modelSpace)) D.carrier → D.carrier
  isExpN : IsGroupExponential ExpN
  isExpD : IsGroupExponential ExpD
  inclusionN : N.carrier →* G
  inclusionD : D.carrier →* G
  action : D.carrier →* MulAut N.carrier
  closedN : Topology.IsClosedEmbedding inclusionN
  closedD : Topology.IsClosedEmbedding inclusionD
  compatibleN : ∀ x : cartanRootIdeal H, inclusionN (ExpN (N.equiv x)) = ExpG x
  compatibleD : ∀ x : H, inclusionD (ExpD (D.equiv x)) = ExpG x
  normalN : inclusionN.range.Normal
  conjugation : ∀ d n, inclusionN (action d n) =
    inclusionD d * inclusionN n * (inclusionD d)⁻¹
  surjective : Function.Surjective (fun p : N.carrier × D.carrier =>
    inclusionN p.1 * inclusionD p.2)
  compactLifts : ∀ K : Set G, IsCompact K → ∃ C : Set (N.carrier × D.carrier),
    IsCompact C ∧ K ⊆ (fun p => inclusionN p.1 * inclusionD p.2) '' C
  overlap : Set.range inclusionN ∩ Set.range inclusionD = ExpG ''
    ((cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∩
      (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)))

variable {H ExpG}

/-- The group factors now exist from the precise published inputs; the
caller does not supply arbitrary nilpotent models or a product theorem. -/
theorem nonempty_cartanFactorModel_of_published_inputs
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (hExpG : IsGroupExponential ExpG)
    (dixmier : DixmierExponentialInput (E := EG) (G := G))
    (existN : NilpotentLieExistenceInput (cartanRootIdeal H))
    (existD : NilpotentLieExistenceInput H)
    (haarN : ∀ M : NilpotentLieModel (cartanRootIdeal H),
      NilpotentExponentialHaarInput M.modelSpace M.carrier)
    (haarD : ∀ M : NilpotentLieModel H,
      NilpotentExponentialHaarInput M.modelSpace M.carrier)
    (integrateN : ∀ M : NilpotentLieModel (cartanRootIdeal H),
      NilpotentLieIntegrationInput (EN := M.modelSpace) (N := M.carrier) (EG := EG) (G := G))
    (integrateD : ∀ M : NilpotentLieModel H,
      NilpotentLieIntegrationInput (EN := M.modelSpace) (N := M.carrier) (EG := EG) (G := G))
    (normality : ∀ M : NilpotentLieModel (cartanRootIdeal H),
      NilpotentIdealNormalityInput (EN := M.modelSpace) (N := M.carrier) (EG := EG) (G := G)) :
    Nonempty (CartanFactorModel H ExpG) := by
  obtain ⟨N⟩ := existN (cartanRootIdeal_nilpotent H T)
  obtain ⟨D⟩ := existD inferInstance
  obtain ⟨ExpN, hExpN, _⟩ := N.exists_exponential_chart (cartanRootIdeal_nilpotent H T) (haarN N)
  obtain ⟨ExpD, hExpD, _⟩ := D.exists_exponential_chart inferInstance (haarD D)
  obtain ⟨ι, κ, φ, hi, hk, hiExp, hkExp, hn, hconj, hsurj, hlifts, hoverlap⟩ :=
    exists_ambient_cartan_factorization T H ExpG hExpG dixmier N.equiv ExpN hExpN
      (haarN N) (integrateN N) (normality N) D.equiv ExpD hExpD (haarD D) (integrateD D)
  exact ⟨{
    N := N, D := D, ExpN := ExpN, ExpD := ExpD, isExpN := hExpN, isExpD := hExpD,
    inclusionN := ι, inclusionD := κ, action := φ,
    closedN := hi, closedD := hk, compatibleN := hiExp, compatibleD := hkExp,
    normalN := hn, conjugation := hconj, surjective := hsurj,
    compactLifts := hlifts, overlap := hoverlap }⟩

end PolycyclicRecognition

end

end OAI
