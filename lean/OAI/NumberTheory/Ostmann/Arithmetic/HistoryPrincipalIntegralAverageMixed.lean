import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPrincipalIntegralAverageBasic
import OAI.NumberTheory.Ostmann.Arithmetic.MixedCellGridReplacementBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
open MeasureTheory PrimeCellFreezing PrimeCellReplacement ResidueHaar
  MixedCellIntegralFreezing LogCellPartition
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedIntegral (loI hiI G : ℝ) (φ : ℝ→ℝ) (lo hi Z : ι→ℝ)
    (f : (Option ι→ℝ)→ℂ) : ℂ :=
  mixedLogIntegral 1 loI hiI G φ (fun i => (Z i)⁻¹) lo hi
    (fun x => f (optionCoordinates x))

omit [DecidableEq ι] in
theorem mixed_density_eq [_decidableEqIndex : DecidableEq ι]
    (M : ℕ) (G : ℝ) (φ : ℝ→ℝ) (Z : ι→ℝ)
    (t : ℝ×(ι→ℝ)) :
    mixedLogDensity M G φ (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹) t=
      ((M:ℝ)*(Nat.totient M:ℝ)^Fintype.card ι)⁻¹*
        mixedLogDensity 1 G φ (fun i => (Z i)⁻¹) t := by
  have hw : (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹)=
      (fun i => (Nat.totient M:ℝ)⁻¹*(Z i)⁻¹) := by funext i; exact mul_inv _ _
  rw [hw]
  simp only [mixedLogDensity,logCellDensity_scale,Nat.cast_one,
    div_eq_mul_inv,mul_inv,inv_pow]
  ring

theorem mixedPrincipalIntegral_eq (M : ℕ) (loI hiI G : ℝ) (φ : ℝ→ℝ)
    (lo hi Z : ι→ℝ) (f : (Option ι→ℝ)→ℂ) :
    mixedPrincipalIntegral M loI hiI G φ lo hi Z f=
      ((M:ℝ)*(Nat.totient M:ℝ)^Fintype.card ι)⁻¹ •
        mixedIntegral loI hiI G φ lo hi Z f := by
  unfold mixedPrincipalIntegral mixedIntegral mixedLogIntegral
  simp_rw [mixed_density_eq,mul_smul]
  exact integral_smul _ _

theorem mixedPrincipalIntegral_mul_sum (M : ℕ) [NeZero M]
    (loI hiI G : ℝ) (φ : ℝ→ℝ) (lo hi Z : ι→ℝ)
    (f : (Option ι→ℝ)→ℂ) (F : ZMod M→(ι→(ZMod M)ˣ)→ℂ) :
    mixedPrincipalIntegral M loI hiI G φ lo hi Z f*
        (∑r:ZMod M,∑u:ι→(ZMod M)ˣ,F r u)=
      mixedIntegral loI hiI G φ lo hi Z f*
        ResidueHaar.average (fun z : ZMod M×(ι→(ZMod M)ˣ) => F z.1 z.2) := by
  rw [mixedPrincipalIntegral_eq]
  simp only [ResidueHaar.average,Fintype.card_prod,Fintype.card_fun,ZMod.card,
    ZMod.card_units_eq_totient,Nat.cast_mul,Nat.cast_pow,Fintype.sum_prod_type,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

end Ostmann.Arithmetic.HistoryPrincipalIntegralAverage

end

end OAI
