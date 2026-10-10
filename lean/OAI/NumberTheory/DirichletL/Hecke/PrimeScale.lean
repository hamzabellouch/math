import OAI.NumberTheory.DirichletL.Hecke.PrimeRow
import OAI.NumberTheory.DirichletL.ConductorBounds

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeScale
open HeckeFamily

theorem log_scale_eventually (dmin rmin K : ℝ) (hd : 0<dmin) (hr : 0<rmin) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r : ℝ, dmin≤d → rmin≤r →
      K≤Real.log ((Z^d)^r) := by
  have hlog : ∀ᶠ Z : ℝ in atTop, max 0 (K/(dmin*rmin))≤Real.log Z :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hlog,eventually_ge_atTop (1 : ℝ)] with Z hlog hZ
  intro d r hd' hr'
  have hZp : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.log_rpow (Real.rpow_pos_of_pos hZp _),Real.log_rpow hZp]
  have hp : 0<dmin*rmin := mul_pos hd hr
  have hk : K≤dmin*rmin*Real.log Z := by
    have hh := (div_le_iff₀ hp).mp ((le_max_right 0 _).trans hlog)
    nlinarith
  have hprod : dmin*rmin≤d*r := mul_le_mul hd' hr' hr.le (hd.trans_le hd').le
  have hl : 0≤Real.log Z := (le_max_left _ _).trans hlog
  nlinarith [mul_le_mul_of_nonneg_right hprod hl]

theorem product_modulus_bound (χ ψ : Character) :
    (χ.product ψ).modulus.absNorm≤χ.modulus.absNorm*ψ.modulus.absNorm := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) := Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  exact FiniteConductor.absNorm_inf_le_mul χ.modulus ψ.modulus

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem twisted_modulus_bound (χ : Character) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤χ.modulus.absNorm*M.absNorm :=
  product_modulus_bound χ (HeckeRayQuotient.character M H hH θ)

theorem twisted_row_modulus_bound (χ : Character) (m u : O)
    (hχ : χ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (HeckeRayFamily.character M 1) m 1 u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH χ θ).modulus.absNorm≤
      M.absNorm^2*(Ideal.span {m}).absNorm*(Ideal.span {(72 : O)}).absNorm*(Ideal.span {u}).absNorm := by
  apply (twisted_modulus_bound M H hH χ θ).trans
  have hn := Nat.mul_le_mul_right M.absNorm hχ
  simpa [HeckeRowClosure.rowConductorBound,HeckeRayFamily.character,
    Character.ofResidue,pow_two,mul_assoc,mul_left_comm,mul_comm] using hn

end SevenEighths.HeckePrimeScale

end

end OAI
