import OAI.NumberTheory.DirichletL.Hecke.PrimeRow
import OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckePrimeNonprincipal
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem inverse_twist_elementCoeff (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n) (n : O) :
    elementCoeff ((χ.inverse.product θ).inverse) n =
      rowTwist (elementHom (η.product θ.inverse)) m f z n := by
  rw [elementCoeff_inverse,elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,hχ]
  change _ = elementCoeff (η.product θ.inverse) n * idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  change (elementCoeff θ n)⁻¹ *
    (elementCoeff η n * idealRowHom (m^6*f^4*z) (Ideal.span {n})) = _
  ring

theorem twisted_nonprincipal (η χ θ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime (((η.product θ.inverse).modulus*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c)) :
    (χ.inverse.product θ).residue≠1 := by
  have hn := HeckeRowNonprincipal.actual_row_nonprincipal (η.product θ.inverse)
    ((χ.inverse.product θ).inverse) m f z hmLam hm2 u a b r hr hpr hx P J hg hchar hJ
    hc hc6 hsplit hcop (inverse_twist_elementCoeff η χ θ m f z hχ)
  intro h
  apply hn
  change (χ.inverse.product θ).residue⁻¹=1
  rw [h,inv_one]

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem fixed_twist_modulus (θ : RayQuotient.Characters M H) :
    ((HeckeRayFamily.character M 1).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change M⊓M=M
  simp

theorem fixed_ray_twisted_nonprincipal (χ : Character) (m f z : O)
    (hχ : ∀ n, elementCoeff χ n=rowTwist (elementHom (HeckeRayFamily.character M 1)) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hx : f^4*z=(u : O)*λ₀^a*(2 : O)^b*r)
    (P J : Ideal O) [P.IsMaximal] (hg : λ₀∉P) (hchar : ringChar (O ⧸ P)≠2)
    (hJ : CanonicalQuadraticSieve.Supported J) {c : ℕ} (hc : 1≤c) (hc6 : ¬6∣c)
    (hsplit : Ideal.span {r}=P^c*J)
    (hcop : IsCoprime ((M*Ideal.span {m}*Ideal.span {(72 : O)})*J) (P^c))
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ.inverse θ).residue≠1 := by
  apply twisted_nonprincipal (HeckeRayFamily.character M 1) χ
    (HeckeRayQuotient.character M H hH θ) m f z hχ hmLam hm2 u a b r hr hpr hx
    P J hg hchar hJ hc hc6 hsplit
  rwa [fixed_twist_modulus M H hH θ]

end SevenEighths.HeckePrimeNonprincipal

end

end OAI
