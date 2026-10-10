import OAI.Algebra.AuslanderReiten.Bar.TCasimirAugmentation
import OAI.Algebra.AuslanderReiten.Bar.TwistedBar
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleExt

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

def B (H : kˣ) (n : ℕ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) n →ₗ[AbsoluteBar.Enveloping k R]
      AbsoluteBar.moduleObject k R (n + 1) :=
  AbsoluteBar.casimirInsertionMap k R (TrivialExtension.twist H) (twistedCasimir q H)
    (twistedCasimir_equivariant q H) n

variable [CharP k 2]

theorem B_differential (H : kˣ) (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (B q H (n + 1)) +
      (B q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) n) = 0 :=
  AbsoluteBar.casimirInsertionMap_boundary k R (TrivialExtension.twist H) (twistedCasimir q H)
    (twistedCasimir_equivariant q H) (twistedCasimir_augmentation q H) n

theorem B_differential_zero (H : kˣ) :
    (AbsoluteBar.differential k R 1).comp (B q H 1) =
      (B q H 0).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0) :=
  AbsoluteBar.casimirInsertionMap_boundary_zero k R (TrivialExtension.twist H) (twistedCasimir q H)
    (twistedCasimir_equivariant q H) (twistedCasimir_augmentation q H)

omit [CharP k 2] in

def P (n : ℕ) : AbsoluteBar.moduleObject k R (n + 4) →ₗ[AbsoluteBar.Enveloping k R]
    AbsoluteBar.moduleObject k R (n + 1) :=
  AbsoluteBar.suffixComparisonMap k R (CocycleData.p q) n

theorem P_differential (n : ℕ) (x : AbsoluteBar.object k R (n + 4)) :
    AbsoluteBar.boundary k R n (AbsoluteBar.suffixComparison k R (CocycleData.p q) (n + 1) x) =
      AbsoluteBar.suffixComparison k R (CocycleData.p q) n (AbsoluteBar.boundary k R (n + 3) x) :=
  AbsoluteBar.suffixComparison_boundary k R (CocycleData.p q) (CocycleData.p_isCocycle3 q) n x

omit [CharP k 2] in
theorem P_augmentation : (AbsoluteBar.differential k R 0).comp (P q 0) =
    AbsoluteBar.cochain3 k R (CocycleData.p q) :=
  AbsoluteBar.suffixComparison_augmentation k R (CocycleData.p q)

end ArExplicit.T

end

end OAI
