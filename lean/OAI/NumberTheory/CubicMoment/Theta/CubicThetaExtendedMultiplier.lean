import OAI.NumberTheory.CubicMoment.Theta.CubicThetaExtendedGroup

namespace OAI

/-! The cubic multiplier on Gamma_2. Its value is independent of the
principal/integer factorization, and it is trivial on SL(2,Z). -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaKubota_factorization_independent (n m : cubicThetaPrincipalGroup)
    (u v : SL(2,ℤ))
    (he : n.val*cubicThetaIntegerEmbedding u = m.val*cubicThetaIntegerEmbedding v) :
    cubicThetaKubotaValue n = cubicThetaKubotaValue m := by
  have hf : (m⁻¹*n).val = cubicThetaIntegerEmbedding (v*u⁻¹) := by
    have h := congrArg (fun w : SL(2,Eisenstein) =>
      m.val⁻¹*w*(cubicThetaIntegerEmbedding u)⁻¹) he
    simpa [mul_assoc] using h
  have hi := cubicThetaKubotaValue_integer (m⁻¹*n) (v*u⁻¹) hf
  have hm := cubicThetaKubotaValue_mul m (m⁻¹*n)
  simpa only [mul_inv_cancel_left,hi,mul_one] using hm

def cubicThetaExtendedValue (g : cubicThetaExtendedGroup) : ℂ :=
  cubicThetaKubotaValue (cubicThetaExtendedPrincipal g)

lemma cubicThetaExtendedValue_of_decomposition (g : cubicThetaExtendedGroup)
    (n : cubicThetaPrincipalGroup) (u : SL(2,ℤ))
    (he : g.val = n.val*cubicThetaIntegerEmbedding u) :
    cubicThetaExtendedValue g = cubicThetaKubotaValue n :=
  cubicThetaKubota_factorization_independent (cubicThetaExtendedPrincipal g) n
    (cubicThetaExtendedInteger g) u ((cubicThetaExtended_decomposition g).symm.trans he)

theorem cubicThetaExtendedValue_mul (g h : cubicThetaExtendedGroup) :
    cubicThetaExtendedValue (g*h) = cubicThetaExtendedValue g*cubicThetaExtendedValue h := by
  let n := cubicThetaExtendedPrincipal g
  let m := cubicThetaExtendedPrincipal h
  let u := cubicThetaExtendedInteger g
  let v := cubicThetaExtendedInteger h
  have hg : g.val = n.val*cubicThetaIntegerEmbedding u := cubicThetaExtended_decomposition g
  have hh : h.val = m.val*cubicThetaIntegerEmbedding v := cubicThetaExtended_decomposition h
  have he : (g*h).val = (n*cubicThetaKubotaConjugate (cubicThetaIntegerEmbedding u) m).val*
      cubicThetaIntegerEmbedding (u*v) := by
    change g.val*h.val = _
    rw [hg,hh]
    simp [cubicThetaKubotaConjugate,mul_assoc]
  rw [cubicThetaExtendedValue_of_decomposition _ _ _ he,cubicThetaKubotaValue_mul,
    cubicThetaKubotaValue_conjugate_integer]
  rfl

def cubicThetaExtendedCharacter : cubicThetaExtendedGroup →* ℂ where
  toFun := cubicThetaExtendedValue
  map_one' := by
    rw [cubicThetaExtendedValue_of_decomposition 1 1 1 (by simp)]
    exact cubicThetaKubotaCharacter.map_one
  map_mul' := cubicThetaExtendedValue_mul

theorem cubicThetaExtendedValue_principal (n : cubicThetaPrincipalGroup) :
    cubicThetaExtendedValue (cubicThetaPrincipalInclusion n) = cubicThetaKubotaValue n :=
  cubicThetaExtendedValue_of_decomposition _ n 1 (by simp [cubicThetaPrincipalInclusion])

theorem cubicThetaExtendedValue_integer (u : SL(2,ℤ)) :
    cubicThetaExtendedValue (cubicThetaIntegerInclusion u) = 1 := by
  rw [cubicThetaExtendedValue_of_decomposition _ 1 u (by simp [cubicThetaIntegerInclusion])]
  exact cubicThetaKubotaCharacter.map_one

lemma cubicThetaExtendedValue_norm (g : cubicThetaExtendedGroup) :
    ‖cubicThetaExtendedValue g‖ = 1 := cubicThetaKubotaValue_norm _

lemma cubicThetaExtendedCharacter_cube (g : cubicThetaExtendedGroup) :
    cubicThetaExtendedCharacter g^3 = 1 :=
  cubicThetaKubotaCharacter_cube (cubicThetaExtendedPrincipal g)

end CubicFirstMoment

end

end OAI
