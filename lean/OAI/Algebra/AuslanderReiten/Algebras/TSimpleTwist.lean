import OAI.Algebra.AuslanderReiten.Algebras.TSimple
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleTwist

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem twist_smul_simple (H : kˣ) (a : T k q) (s : Resolution.Simple q) :
    TrivialExtension.twist H a • s = a • s := rfl

theorem p_twist_simple (H : kˣ) (a b c : T k q) (s : Resolution.Simple q) :
    CocycleData.p q (TrivialExtension.twist H a) (TrivialExtension.twist H b)
      (TrivialExtension.twist H c) • s =
      (H : k) • (CocycleData.p q a b c • s) := by
  rw [CocycleData.p_twist, smul_assoc, twist_smul_simple]

theorem p_inverse_twist_simple (H : kˣ) (a b c : T k q) (s : Resolution.Simple q) :
    CocycleData.p q ((TrivialExtension.twist H).symm a) ((TrivialExtension.twist H).symm b)
      ((TrivialExtension.twist H).symm c) • s =
      ((H⁻¹ : kˣ) : k) • (CocycleData.p q a b c • s) := by
  have hi (x : T k q) : (TrivialExtension.twist H).symm x = TrivialExtension.twist H⁻¹ x := rfl
  rw [hi a, hi b, hi c]
  have hp := p_twist_simple q H⁻¹ a b c s
  convert! hp using 1

end ArExplicit.T

end

end OAI
