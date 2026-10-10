import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCentralLayers
import Mathlib.LinearAlgebra.Pi

namespace OAI

/-! # A faithful rational action on the quotient by the nilpotent radical

The finitely many upper central layers give a direct-product vector space.
For a maximal nilpotent normal subgroup, the action kernel is exactly that
subgroup, by the proved central-filtration criterion.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative commutatorElement
variable {G : Type} [Group G] (F : Subgroup G) [F.Normal]

abbrev CentralLayersSpace (c : ℕ) :=
  (i : Fin c) → RationalAbelianSpace (CentralLayer F i)

def centralLayersAction (c : ℕ) :
    G →* (CentralLayersSpace F c ≃ₗ[ℚ] CentralLayersSpace F c) where
  toFun g := LinearEquiv.piCongrRight (fun i : Fin c => rationalUpperCentralAction F i g)
  map_one' := by
    ext v i
    change rationalUpperCentralAction F i 1 (v i) = v i
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v i
    change rationalUpperCentralAction F i (g * h) (v i) =
      rationalUpperCentralAction F i g (rationalUpperCentralAction F i h (v i))
    rw [map_mul]
    rfl

theorem centralLayersAction_ker_iff (c : ℕ) (g : G) :
    g ∈ (centralLayersAction F c).ker ↔
      ∀ i : Fin c, g ∈ (rationalUpperCentralAction F i).ker := by
  classical
  constructor
  · intro hg i
    change centralLayersAction F c g = 1 at hg
    change rationalUpperCentralAction F i g = 1
    apply LinearEquiv.ext
    intro v
    change rationalUpperCentralAction F i g v = v
    let w : CentralLayersSpace F c := Pi.single i v
    have he := congrArg
      (fun e : CentralLayersSpace F c ≃ₗ[ℚ] CentralLayersSpace F c => e w i) hg
    change rationalUpperCentralAction F i g (w i) = w i at he
    simpa only [w, Pi.single_eq_same] using he
  · intro hg
    change centralLayersAction F c g = 1
    ext v i
    change rationalUpperCentralAction F i g (v i) = v i
    rw [show rationalUpperCentralAction F i g = 1 from hg i]
    rfl

theorem subgroup_le_centralLayersAction_ker (c : ℕ) : F ≤ (centralLayersAction F c).ker := by
  intro g hg
  exact (centralLayersAction_ker_iff F c g).mpr
    (fun i => subgroup_le_rationalUpperCentralAction_ker F i hg)

theorem centralLayersAction_ker [Group.IsSolvable G] [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F)
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    (centralLayersAction F (Group.nilpotencyClass F)).ker = F := by
  let c := Group.nilpotencyClass F
  let K := (centralLayersAction F c).ker
  apply maximal_nilpotent_normal_of_trivial_central_action F hmax K
    (subgroup_le_centralLayersAction_ker F c)
  intro i
  by_cases hi : i < c
  · apply commutator_centralLayer_le_of_rational_kernel F hF i K
    intro g hg
    exact (centralLayersAction_ker_iff F c g).mp hg ⟨i, hi⟩
  · have he (j : ℕ) (hj : c ≤ j) : ambientUpperCentralSeries F j = F := by
      dsimp [ambientUpperCentralSeries]
      rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr hj]
      simp only [Subgroup.map_top, Subgroup.range_subtype]
    rw [he i (by omega), he (i + 1) (by omega)]
    exact Subgroup.commutator_le_right K F

omit [F.Normal] in
theorem centralLayersSpace_finite [Group.IsNilpotent F]
    (hF : HasFiniteIntegralCohomologicalDimension F) (c : ℕ) :
    Module.Finite ℚ (CentralLayersSpace F c) := by
  obtain ⟨d, hd⟩ := hF
  let := hd
  let (i : Fin c) : Module.Finite ℚ (RationalAbelianSpace (CentralLayer F i)) :=
    nilpotent_upperCentral_center_rational_finite d i
  infer_instance

def nilpotentQuotientRationalAction [Group.IsSolvable G] [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F)
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    G ⧸ F →* (CentralLayersSpace F (Group.nilpotencyClass F) ≃ₗ[ℚ]
      CentralLayersSpace F (Group.nilpotencyClass F)) :=
  QuotientGroup.lift F (centralLayersAction F (Group.nilpotencyClass F))
    (le_of_eq (centralLayersAction_ker F hF hmax).symm)

theorem nilpotentQuotientRationalAction_injective [Group.IsSolvable G] [Group.IsNilpotent F]
    (hF : HasNoNontrivialTorsion F)
    (hmax : ∀ N : Subgroup G, N.Normal → Group.IsNilpotent N → F ≤ N → N = F) :
    Function.Injective (nilpotentQuotientRationalAction F hF hmax) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (centralLayersAction_ker F hF hmax).symm

end PolycyclicRecognition

end

end OAI
