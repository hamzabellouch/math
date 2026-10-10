import OAI.GroupTheory.PolycyclicRecognition.Algebra.DistortedHomomorphisms
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGeneratorSchemes

namespace OAI

/-! # Vanishing on the actual Cartan root factor

Logarithmic distortion kills each root generator under a linearly bounded
continuous homomorphism. The proved generator schemes then kill the whole
constructed nilpotent factor, including every point of its group model.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

include T M hExp realize hl hL hbound

/-- The actual homogeneous letters lie in the kernel. -/
theorem hom_eq_one_on_letter (i : Fin M.letterCount) (t : ℝ) :
    l (Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 :=
  hom_eq_one_on_root_exp T H (M.weight i) (M.weight_nonzero i) Exp hExp realize
    l hl hL hbound ⟨M.letter i, M.letter_root i⟩ t

/-- Every exponential in the root ideal lies in the kernel. -/
theorem hom_eq_one_on_root_factor_exp
    (F : CartanFactorModel H Exp)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (v : cartanRootIdeal H) : l (F.inclusionN (F.ExpN (F.N.equiv v))) = 1 := by
  obtain ⟨_, _, _, hgen⟩ := M.exists_bounded_cartan_generator_words T F hExp realize
    haarN dynkinN ‖(finBasis ℝ (cartanRootIdeal H)).equivFun v‖
  obtain ⟨u, _, _, hu⟩ := hgen v le_rfl
  rw [← hu]
  unfold generatorGroupWord
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  have he : ∀ z ∈ u, l (F.inclusionN ((F.ExpN ∘ F.N.equiv) (z.2 • M.letter z.1))) = 1 := by
    intro z _
    rw [Function.comp_apply, F.compatibleN]
    exact M.hom_eq_one_on_letter T hExp realize l hl hL hbound z.1 z.2
  exact List.prod_eq_one (by simpa only [List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Function.comp_apply] using he)

/-- Surjectivity of the intrinsic nilpotent exponential gives vanishing on
all points of the factor, not only its logarithmic coordinate model. -/
theorem hom_eq_one_on_root_factor
    (F : CartanFactorModel H Exp)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (n : F.N.carrier) : l (F.inclusionN n) = 1 := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨x, hx⟩ := chartN.surjective n
  have hex : F.ExpN x = n := (hchartN x).symm.trans hx
  rw [← hex]
  simpa only [F.N.equiv.apply_symm_apply] using
    M.hom_eq_one_on_root_factor_exp T hExp realize l hl hL hbound F haarN dynkinN
      (F.N.equiv.symm x)

end PolycyclicRecognition.CartanWordModel

end

end OAI
