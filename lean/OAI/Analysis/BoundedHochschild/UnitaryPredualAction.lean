import OAI.Analysis.BoundedHochschild.WeakPredual

namespace OAI

/-! The isometric unitary action on a von Neumann predual. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma unitaryPullback_one (F : StrongDual ℂ M) : unitaryPullback F 1 = F := by
  ext a
  simp only [unitaryPullback_apply, OneMemClass.coe_one, star_one, one_mul, mul_one]

lemma unitaryPullback_mul (F : StrongDual ℂ M) (u v : unitary M) :
    unitaryPullback (unitaryPullback F u) v = unitaryPullback F (u * v) := by
  ext a
  simp only [unitaryPullback_apply, Submonoid.coe_mul, star_mul, mul_assoc]

/-- Unitary conjugation acts isometrically on bounded scalar functionals. -/
def unitaryDualEquiv (u : unitary M) : StrongDual ℂ M ≃ₗᵢ[ℂ] StrongDual ℂ M where
  toFun F := unitaryPullback F u
  invFun F := unitaryPullback F (star u)
  left_inv F := by
    change unitaryPullback (unitaryPullback F u) (star u) = F
    rw [unitaryPullback_mul, Unitary.mul_star_self, unitaryPullback_one]
  right_inv F := by
    change unitaryPullback (unitaryPullback F (star u)) u = F
    rw [unitaryPullback_mul, Unitary.star_mul_self, unitaryPullback_one]
  map_add' F G := by ext a; rfl
  map_smul' c F := by ext a; rfl
  norm_map' F := by
    apply le_antisymm (unitaryPullback_norm_le F u)
    have h := unitaryPullback_norm_le (unitaryPullback F u) (star u)
    simpa only [unitaryPullback_mul, Unitary.mul_star_self, unitaryPullback_one] using h

variable [PartialOrder M] [StarOrderedRing M]

lemma unitaryPullback_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) (u : unitary M) :
    unitaryPullback F u ∈ normalDual e := by
  apply unitaryOrbitHull_normal e hF
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_range_self u))

/-- The same action restricted to normal functionals. -/
def normalUnitaryEquiv (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (u : unitary M) :
    normalDual e ≃ₗᵢ[ℂ] normalDual e where
  toFun F := ⟨unitaryPullback F.val u, unitaryPullback_normal e F.property u⟩
  invFun F := ⟨unitaryPullback F.val (star u), unitaryPullback_normal e F.property (star u)⟩
  left_inv F := Subtype.ext ((unitaryDualEquiv u).left_inv F.val)
  right_inv F := Subtype.ext ((unitaryDualEquiv u).right_inv F.val)
  map_add' F G := Subtype.ext (by ext a; rfl)
  map_smul' c F := Subtype.ext (by ext a; rfl)
  norm_map' F := (unitaryDualEquiv u).norm_map F.val

/-- Identification of the predual with the normal functionals. -/
def predualNormalEquiv (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) : X ≃ₗᵢ⋆[ℂ] normalDual e :=
  (predualEmbedding e).equivRange

omit [CompleteSpace X] [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma predualNormalEquiv_coe (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (x : X) :
    (predualNormalEquiv e x).val = predualEmbedding e x := rfl

/-- Pullback by the inverse unitary gives a left group action on the predual. -/
def unitaryPredualAction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (u : unitary M) : X ≃ₗᵢ[ℂ] X :=
  (predualNormalEquiv e).trans
    ((normalUnitaryEquiv e (star u)).trans (predualNormalEquiv e).symm)

lemma predualEmbedding_unitaryAction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (u : unitary M) (x : X) :
    predualEmbedding e (unitaryPredualAction e u x) =
      unitaryPullback (predualEmbedding e x) (star u) := by
  have h := congrArg Subtype.val ((predualNormalEquiv e).apply_symm_apply
    (normalUnitaryEquiv e (star u) (predualNormalEquiv e x)))
  exact h

lemma unitaryPredualAction_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (x : X) :
    unitaryPredualAction e 1 x = x := by
  apply (predualEmbedding e).injective
  rw [predualEmbedding_unitaryAction, star_one, unitaryPullback_one]

lemma unitaryPredualAction_mul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (u v : unitary M) (x : X) :
    unitaryPredualAction e (u * v) x = unitaryPredualAction e u (unitaryPredualAction e v x) := by
  apply (predualEmbedding e).injective
  simp only [predualEmbedding_unitaryAction, unitaryPullback_mul, star_mul]

end KadisonRingrose
end BoundedHochschild

end

end OAI
