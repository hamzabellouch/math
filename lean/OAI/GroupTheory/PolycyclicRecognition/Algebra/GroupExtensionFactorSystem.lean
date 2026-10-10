import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExtensionSectionFactor
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NonabelianFactorSystem

namespace OAI

/-! # A group extension is its actual section factor system -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

namespace GroupExtensionSection
variable (S : GroupExtension N G Q) (σ : S.Section) (hσ : σ 1 = 1)

def factorSystem : NonabelianFactorSystem N Q where
  action q := S.conjAct (σ q)
  factor := factor S σ
  action_one := by rw [hσ, map_one]
  factor_one_left := factor_one_left S σ hσ
  factor_one_right := factor_one_right S σ hσ
  action_mul := section_action_mul S σ
  cocycle := factor_cocycle S σ

/-- The kernel coordinate of an element relative to the chosen section. -/
def coordinate (g : G) : N :=
  Function.invFun S.inl (g * (σ (S.rightHom g))⁻¹)

@[simp] theorem inl_coordinate (g : G) :
    S.inl (coordinate S σ g) = g * (σ (S.rightHom g))⁻¹ := by
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, σ.rightHom_section, mul_inv_cancel]

theorem coordinate_inl_mul (n : N) (q : Q) :
    coordinate S σ (S.inl n * σ q) = n := by
  apply S.inl_injective
  simp only [inl_coordinate, map_mul, S.rightHom_inl, σ.rightHom_section, one_mul,
    mul_inv_cancel_right]

/-- The underlying normal-form coordinates are bijective. -/
def normalFormEquiv : G ≃ FactorExtension (factorSystem S σ hσ) where
  toFun g := ⟨coordinate S σ g, S.rightHom g⟩
  invFun a := S.inl a.left * σ a.right
  left_inv g := by
    change S.inl (coordinate S σ g) * σ (S.rightHom g) = g
    rw [inl_coordinate, inv_mul_cancel_right]
  right_inv a := by
    apply FactorExtension.ext
    · exact coordinate_inl_mul S σ a.left a.right
    · simp only [map_mul, S.rightHom_inl, σ.rightHom_section, one_mul]

/-- Decoding the normal form respects the nonabelian multiplication. -/
def decode : FactorExtension (factorSystem S σ hσ) →* G where
  toFun a := S.inl a.left * σ a.right
  map_one' := by change S.inl 1 * σ 1 = 1; rw [map_one, hσ, one_mul]
  map_mul' a b := by
    change S.inl (a.left * S.conjAct (σ a.right) b.left * factor S σ a.right b.right) *
      σ (a.right * b.right) = _
    simp only [map_mul, S.inl_conjAct_comm, inl_factor]
    group

/-- No splitting is assumed: the section factor supplies the full group law. -/
def mulEquiv : G ≃* FactorExtension (factorSystem S σ hσ) :=
  (MulEquiv.ofBijective (decode S σ hσ) (normalFormEquiv S σ hσ).symm.bijective).symm

end GroupExtensionSection
end PolycyclicRecognition

end

end OAI
