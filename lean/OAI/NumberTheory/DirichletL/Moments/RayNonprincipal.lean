import OAI.NumberTheory.DirichletL.Moments.NonprincipalGate
import OAI.NumberTheory.DirichletL.Hecke.MaskDescent
import OAI.NumberTheory.DirichletL.Hecke.PrimeRay

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRayNonprincipal
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion HeckePrimeRay
local notation "O" => HeckeFamily.O

theorem product_principal_descent (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (θ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a:O := 1+q
  have ha:Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus) := by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hθa:Ideal.Quotient.mk θ.modulus a=1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  have hcχ:IsCoprime (Ideal.span {a}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcθ:IsCoprime (Ideal.span {a}) θ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcp:IsCoprime (Ideal.span {a}) (χ.product θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv:elementCoeff (χ.product θ) a=1 := by
    change (χ.product θ).residue _=1
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  rw [elementCoeff_product] at hv
  change χ.residue (Ideal.Quotient.mk χ.modulus a)*
    θ.residue (Ideal.Quotient.mk θ.modulus a)=1 at hv
  simpa only [ha,hθa,map_one,mul_one] using hv

theorem product_principal_inducing (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    ∃ψ:Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  HeckeMaskDescent.exists_primitive_above χ θ.modulus
    (product_principal_descent χ θ hp)

theorem actual_row_twist_nonprincipal (η χ θ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤θ.modulus) (hex:¬FixedInducingRow η Q m A z) :
    (χ.product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψ,hmod,hind⟩ := product_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,hψ,hind,hQ.trans hmod,hrow⟩

variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

theorem all_ray_twists_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤M) (hex:¬FixedInducingRow η Q m A z) :
    ∀θ:RayQuotient.Characters M H, (twistedFamily M H hH χ θ).residue≠1 := by
  intro θ
  exact actual_row_twist_nonprincipal η χ (HeckeRayQuotient.character M H hH θ)
    Q m A z hrow hQ hex

end SevenEighths.CenteredMomentRayNonprincipal

end

end OAI
