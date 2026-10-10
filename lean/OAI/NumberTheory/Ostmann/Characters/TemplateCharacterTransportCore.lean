import OAI.NumberTheory.Ostmann.Characters.Basic
import OAI.NumberTheory.Ostmann.Characters.TransferRows

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template

section Row
variable {H Y G : Type*} [Fintype H] [Fintype Y] [DecidableEq H] [CommGroup G]

def oldCopiedRow (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (i:H) (t:Bool)
    (P:G) (z:((H×Bool)⊕Y)→G) : G :=
  P^b (some (.inl i)) none *
    (∏h:H,z (.inl (h,t))^b (some (.inl i)) (some (.inl h))) *
    (∏y:Y,z (.inr y)^b (some (.inl i)) (some (.inr y)))

theorem copied_row_transport (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (i:H) (t:Bool)
    (ν P u:G) (z:((H×Bool)⊕Y)→G)
    (hself:b (some (.inl i)) (some (.inl i))=0)
    (hP:P=u*∏h:H,z (.inl (h,!t))) :
    (ν*oldCopiedRow b i t P z)^copySign t =
      (ν^copySign t*u^(copySign t*b (some (.inl i)) none))*
        rowProduct (transferGraph b (.inl (i,t))) z := by
  rw [transferGraph_row b i t z hself]
  simp only [oldCopiedRow,hP,mul_zpow,←zpow_mul]
  simp only [mul_comm (b (some (.inl i)) none) (copySign t)]
  ac_rfl

theorem shared_row_transport (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (y:Y)
    (νL νR P:G) (z:((H×Bool)⊕Y)→G) :
    (νL*P^b (some (.inr y)) none*
        (∏h:H,z (.inl (h,true))^b (some (.inr y)) (some (.inl h)))*
        (∏r:Y,z (.inr r)^b (some (.inr y)) (some (.inr r)))) /
    (νR*P^b (some (.inr y)) none*
        (∏h:H,z (.inl (h,false))^b (some (.inr y)) (some (.inl h)))*
        (∏r:Y,z (.inr r)^b (some (.inr y)) (some (.inr r)))) =
      (νL/νR)*rowProduct (transferGraph b (.inr y)) z := by
  rw [transferGraph_shared_row]
  simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

theorem regular_unary_transport (κ f s δ:G) (ε t:ℤ) :
    (κ*f^(-ε))^t*(δ*f/s)^(t*ε) =
      (κ^t*δ^(t*ε))*s^(-(t*ε)) := by
  rw [mul_zpow,div_zpow,mul_zpow,←zpow_mul]
  have he : (-ε)*t= -(t*ε) := by ring
  rw [he]
  simp only [zpow_neg,div_eq_mul_inv]
  calc
    _ = (κ^t*δ^(t*ε))*(f^(t*ε)*(f^(t*ε))⁻¹)*(s^(t*ε))⁻¹ := by
      simp only [mul_assoc,mul_left_comm,mul_comm]
    _ = _ := by simp
end Row

theorem character_regular_unary_transport {F:Type*} [CommRing F]
    (χ:MulChar F ℂ) (κ:ℂˣ) (f s δ:Fˣ) (ε t:ℤ) :
    (κ*(χ.toUnitHom f)^(-ε))^t*(χ.toUnitHom (δ*f/s))^(t*ε) =
      (κ^t*(χ.toUnitHom δ)^(t*ε))*(χ.toUnitHom s)^(-(t*ε)) := by
  rw [map_div,map_mul]
  exact regular_unary_transport κ _ _ _ ε t

end Ostmann.Characters.Template

end

end OAI
