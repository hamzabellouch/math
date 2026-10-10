import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIntegrationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularRealizationInput
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDecomposition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieIdealNormalityInput

namespace OAI

/-! # Closed Cartan factors in the actual ambient Lie group

Lie integration supplies the homomorphisms. The existing Dixmier and
nilpotent exponential inputs then prove closedness and identify their exact
ranges. Neither closedness nor the description of the overlap is assumed.
The simply connected nilpotent Lie models themselves remain explicit here.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule LieAlgebra
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
  (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
  (haarN : NilpotentExponentialHaarInput EN N)
  (integrate : NilpotentLieIntegrationInput (EN := EN) (N := N) (EG := EG) (G := G))

include T hExpG dixmier hExpN haarN integrate in
/-- The actual nonzero-root ideal integrates injectively with closed image,
which is exactly its ambient exponential image. -/
theorem exists_closed_cartanRootIdeal_inclusion
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N) :
    ∃ ι : N →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
      (∀ x : cartanRootIdeal H, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eN x) = (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      (∀ x : cartanRootIdeal H, ι (ExpN (eN x)) = ExpG x) ∧
      Set.range ι = ExpG '' (cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  let _ : SimplyConnectedSpace G := ‹SimplyConnectedSpace G›
  let _ : T2Space N := ‹T2Space N›
  let _ : BorelSpace N := ‹BorelSpace N›
  let j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G :=
    (cartanRootIdeal H).incl.comp eN.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp eN.symm.injective
  have hn := eN.nilpotent_iff_equiv_nilpotent.mp (cartanRootIdeal_nilpotent H T)
  obtain ⟨⟨cN, hcN⟩, _⟩ := haarN.2 ExpN hExpN hn
  obtain ⟨cG, hcG⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 ExpG hExpG
  obtain ⟨ι, hclosed, hsmooth, hderiv, hι, hrange⟩ := exists_closed_integration integrate hn j hj
    ExpN ExpG hExpN hExpG cN hcN cG hcG
  refine ⟨ι, hclosed, hsmooth, ?_, ?_, ?_⟩
  · intro x
    have h := hderiv (eN x)
    change mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eN x) =
      (eN.symm (eN x) : GroupLieAlgebra (𝓘(ℝ, EG)) G) at h
    simpa only [eN.symm_apply_apply] using h
  · intro x
    have h := hι (eN x)
    change ι (ExpN (eN x)) = ExpG (eN.symm (eN x)) at h
    simpa only [eN.symm_apply_apply] using h
  · rw [hrange]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eN.symm y).property
    · intro hx
      refine ⟨eN ⟨x, hx⟩, ?_⟩
      change (eN.symm (eN ⟨x, hx⟩) : GroupLieAlgebra (𝓘(ℝ, EG)) G) = x
      rw [eN.symm_apply_apply]

include T hExpG dixmier hExpN haarN integrate in
/-- The integrated root ideal is normal by the published ideal criterion,
applied to the exact differential of the constructed inclusion. -/
theorem exists_closed_normal_cartanRootIdeal_inclusion
    (normality : NilpotentIdealNormalityInput (EN := EN) (N := N) (EG := EG) (G := G))
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N) :
    ∃ ι : N →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
      (∀ x : cartanRootIdeal H, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eN x) =
        (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      (∀ x : cartanRootIdeal H, ι (ExpN (eN x)) = ExpG x) ∧
      Set.range ι = ExpG '' (cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      ι.range.Normal := by
  obtain ⟨ι, hclosed, hsmooth, hderiv, hExp, hrange⟩ :=
    exists_closed_cartanRootIdeal_inclusion T H ExpG hExpG dixmier ExpN hExpN haarN integrate eN
  let j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G :=
    (cartanRootIdeal H).incl.comp eN.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp eN.symm.injective
  have hjrange : Set.range j = (cartanRootIdeal H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eN.symm y).property
    · intro hx
      refine ⟨eN ⟨x, hx⟩, ?_⟩
      change (eN.symm (eN ⟨x, hx⟩) : GroupLieAlgebra (𝓘(ℝ, EG)) G) = x
      rw [eN.symm_apply_apply]
  have hd : ∀ x, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 x = j x := by
    intro x
    obtain ⟨y, rfl⟩ := eN.surjective x
    simpa only [j, LieHom.comp_apply, LieEquiv.coe_toLieHom, eN.symm_apply_apply,
      LieIdeal.incl_apply] using hderiv y
  have hn := eN.nilpotent_iff_equiv_nilpotent.mp (cartanRootIdeal_nilpotent H T)
  exact ⟨ι, hclosed, hsmooth, hderiv, hExp, hrange,
    normality inferInstance inferInstance hn (cartanRootIdeal H) j ι hj
      hclosed hsmooth hd hjrange⟩

include T hExpG dixmier hExpN haarN integrate in
/-- The nilpotent Cartan algebra integrates to a closed subgroup with exactly
its ambient exponential image; no complementary-subgroup claim is made. -/
theorem exists_closed_cartan_inclusion
    (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N) :
    ∃ ι : N →* G, Topology.IsClosedEmbedding ι ∧
      ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ ι ∧
      (∀ x : H, mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eD x) = (x : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∧
      (∀ x : H, ι (ExpN (eD x)) = ExpG x) ∧
      Set.range ι = ExpG '' (H : Set (GroupLieAlgebra (𝓘(ℝ, EG)) G)) := by
  let _ : SimplyConnectedSpace G := ‹SimplyConnectedSpace G›
  let _ : T2Space N := ‹T2Space N›
  let _ : BorelSpace N := ‹BorelSpace N›
  let j : GroupLieAlgebra (𝓘(ℝ, EN)) N →ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EG)) G :=
    H.incl.comp eD.symm.toLieHom
  have hj : Function.Injective j := Subtype.val_injective.comp eD.symm.injective
  have hn := eD.nilpotent_iff_equiv_nilpotent.mp (inferInstance : LieRing.IsNilpotent H)
  obtain ⟨⟨cN, hcN⟩, _⟩ := haarN.2 ExpN hExpN hn
  obtain ⟨cG, hcG⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 ExpG hExpG
  obtain ⟨ι, hclosed, hsmooth, hderiv, hι, hrange⟩ := exists_closed_integration integrate hn j hj
    ExpN ExpG hExpN hExpG cN hcN cG hcG
  refine ⟨ι, hclosed, hsmooth, ?_, ?_, ?_⟩
  · intro x
    have h := hderiv (eD x)
    change mfderiv (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ι 1 (eD x) =
      (eD.symm (eD x) : GroupLieAlgebra (𝓘(ℝ, EG)) G) at h
    simpa only [eD.symm_apply_apply] using h
  · intro x
    have h := hι (eD x)
    change ι (ExpN (eD x)) = ExpG (eD.symm (eD x)) at h
    simpa only [eD.symm_apply_apply] using h
  · rw [hrange]
    congr 1
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eD.symm y).property
    · intro hx
      refine ⟨eD ⟨x, hx⟩, ?_⟩
      change (eD.symm (eD ⟨x, hx⟩) : GroupLieAlgebra (𝓘(ℝ, EG)) G) = x
      rw [eD.symm_apply_apply]

omit [MetricSpace G] [Group G] [SimplyConnectedSpace G] in
/-- Injectivity of the ambient exponential retains precisely the Cartan
intersection, even when it is nontrivial. -/
theorem exponential_factor_intersection
    {V A B : Type*} (Exp : V → G) (hExp : Function.Injective Exp)
    (iA : A → G) (iB : B → G) (SA SB : Set V)
    (hA : Set.range iA = Exp '' SA) (hB : Set.range iB = Exp '' SB) :
    Set.range iA ∩ Set.range iB = Exp '' (SA ∩ SB) := by
  rw [hA, hB, Set.image_inter hExp]

end PolycyclicRecognition

end

end OAI
