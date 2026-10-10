import OAI.Analysis.OperatorAlgebra.IntertwinerTensorCompression
import OAI.Analysis.OperatorAlgebra.StandardMultiplicationEvaluation

namespace OAI

/-! The represented-quotient tensor map obtained from the actual standard
multiplication map and the completely positive commutant compression. -/
noncomputable section
open Filter
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

attribute [local irreducible] minimalRightCPMap minimalMapAny
  standardLeftFactor intertwinerOppositeCP standardCommutantEquiv

lemma standard_starHomContinuousLinear_apply {X Y : Type*}
    [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    (f : X →⋆ₙₐ[ℂ] Y) (x : X) : starHomContinuousLinear f x = f x := rfl

variable {A Q B H K : Type*} [CStarAlgebra A] [CStarAlgebra Q] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def standardTensorCompression
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (ρ : Q →⋆ₐ[ℂ] (K →L[ℂ] K)) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    MinimalTensor Q B →L[ℂ] (K →L[ℂ] K) :=
  (starHomContinuousLinear (nuclearQuotientStandardMultiplication ω hω hA q hq ρ S hS)).comp
    ((starHomContinuousLinear (minimalMapAny
      (standardLeftFactor ρ S hS).toNonUnitalStarAlgHom
      (NonUnitalStarAlgHom.id ℂ S.M.toStarSubalgebraᵐᵒᵖ))).comp
      (minimalRightCPMap (intertwinerOppositeCP ρ π V hV η hc S hS)))

lemma standardTensorCompression_norm_le
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (ρ : Q →⋆ₐ[ℂ] (K →L[ℂ] K)) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range)
    (z : MinimalTensor Q B) :
    ‖standardTensorCompression ω hω hA q hq ρ π V hV η hc S hS z‖ ≤
      (4 * (‖V‖ * ‖V‖)) * ‖z‖ := by
  let Φ := intertwinerOppositeCP ρ π V hV η hc S hS
  let ψ := minimalMapAny (standardLeftFactor ρ S hS).toNonUnitalStarAlgHom
    (NonUnitalStarAlgHom.id ℂ S.M.toStarSubalgebraᵐᵒᵖ)
  let θ := nuclearQuotientStandardMultiplication ω hω hA q hq ρ S hS
  unfold standardTensorCompression
  simp only [ContinuousLinearMap.comp_apply, standard_starHomContinuousLinear_apply]
  change ‖θ (ψ (minimalRightCPMap Φ z))‖ ≤ _
  calc
    _ ≤ ‖minimalRightCPMap Φ z‖ :=
      (NonUnitalStarAlgHom.norm_apply_le θ _).trans
        (NonUnitalStarAlgHom.norm_apply_le ψ _)
    _ ≤ (4 * ‖Φ‖) * ‖z‖ :=
      minimalRightCPMap_norm_le Φ (intertwinerOppositeCP_cp ρ π V hV η hc S hS) z
    _ ≤ (4 * (‖V‖ * ‖V‖)) * ‖z‖ := by
      gcongr
      exact intertwinerOppositeCP_norm_le ρ π V hV η hc S hS

lemma standardTensorLegs_elementary
    (ρ : Q →⋆ₐ[ℂ] (K →L[ℂ] K)) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) (a : Q) (b : B) :
    minimalMapAny (standardLeftFactor ρ S hS).toNonUnitalStarAlgHom
      (NonUnitalStarAlgHom.id ℂ S.M.toStarSubalgebraᵐᵒᵖ)
      (minimalRightCPMap (intertwinerOppositeCP ρ π V hV η hc S hS)
        (minimalElementary a b)) =
    minimalElementary (standardLeftFactor ρ S hS a)
      (intertwinerOppositeCP ρ π V hV η hc S hS b) := by
  have h := congrArg (minimalMapAny (standardLeftFactor ρ S hS).toNonUnitalStarAlgHom
    (NonUnitalStarAlgHom.id ℂ S.M.toStarSubalgebraᵐᵒᵖ))
    (minimalRightCPMap_elementary (A := Q)
      (intertwinerOppositeCP ρ π V hV η hc S hS)
      (intertwinerOppositeCP_cp ρ π V hV η hc S hS) a b)
  exact h.trans (minimalMapAny_elementary
    (standardLeftFactor ρ S hS).toNonUnitalStarAlgHom
    (NonUnitalStarAlgHom.id ℂ S.M.toStarSubalgebraᵐᵒᵖ)
    a (intertwinerOppositeCP ρ π V hV η hc S hS b))

lemma standardLeftFactor_val (ρ : Q →⋆ₐ[ℂ] (K →L[ℂ] K))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) (a : Q) :
    (standardLeftFactor ρ S hS a).val = ρ a := by
  unfold standardLeftFactor
  rfl

lemma standardCommutantEquiv_val (S : StandardModularData K)
    (x : S.M.toStarSubalgebraᵐᵒᵖ) :
    antiunitaryConjugate S.J (star x.unop.val) = (standardCommutantEquiv S x).val := by
  unfold standardCommutantEquiv
  rfl

lemma standardTensorCompression_elementary
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (ρ : Q →⋆ₐ[ℂ] (K →L[ℂ] K)) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) (a : Q) (b : B) :
    standardTensorCompression ω hω hA q hq ρ π V hV η hc S hS (minimalElementary a b) =
      V.adjoint.comp (((π a) * (η b)).comp V) := by
  have h₁ := congrArg (nuclearQuotientStandardMultiplication ω hω hA q hq ρ S hS)
    (standardTensorLegs_elementary ρ π V hV η hc S hS a b)
  have h₂ := nuclearQuotientStandardMultiplication_elementary ω hω hA q hq ρ S hS
    (standardLeftFactor ρ S hS a) (intertwinerOppositeCP ρ π V hV η hc S hS b)
  have h₃ : (standardLeftFactor ρ S hS a).val *
      antiunitaryConjugate S.J
        (star (intertwinerOppositeCP ρ π V hV η hc S hS b).unop.val) =
      V.adjoint.comp (((π a) * (η b)).comp V) := by
    rw [standardLeftFactor_val, standardCommutantEquiv_val, intertwinerOppositeCP_evaluate]
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun T : H →L[ℂ] K => T (η b (V x)))
      (intertwiner_adjoint ρ π V hV a)
  exact h₁.trans (h₂.trans h₃)

lemma standardTensorCompression_algebraic
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (ρ : Q →⋆ₐ[ℂ] (K →L[ℂ] K)) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (V : K →L[ℂ] H) (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range)
    (z : Q ⊗[ℂ] B) :
    standardTensorCompression ω hω hA q hq ρ π V hV η hc S hS (minimalAlgebraicLinear z) =
      V.adjoint.comp ((Pureness.commutingStarTensorHom π η hc z).comp V) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => exact standardTensorCompression_elementary ω hω hA q hq ρ π V hV η hc S hS a b
  | add x y hx hy =>
    simp only [map_add, hx, hy, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

end WeakPureInfiniteness

end

end OAI
