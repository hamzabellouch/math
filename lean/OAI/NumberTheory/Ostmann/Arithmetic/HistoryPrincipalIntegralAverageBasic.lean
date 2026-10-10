import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellSmoothReplacement
import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryPrincipalIntegralAverage
open MeasureTheory PrimeCellFreezing PrimeCellReplacement ResidueHaar
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primeIntegral (lo hi Z : ι→ℝ) (f : (ι→ℝ)→ℂ) : ℂ :=
  logCellIntegral (fun i => (Z i)⁻¹) lo hi f

omit [DecidableEq ι] in
theorem logCellDensity_scale (a : ℝ) (w t : ι→ℝ) :
    logCellDensity (fun i => a*w i) t=a^Fintype.card ι*logCellDensity w t := by
  simp only [logCellDensity,mul_div_assoc,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ]

omit [DecidableEq ι] in
theorem logCellIntegral_scale (a : ℝ) (w lo hi : ι→ℝ) (f : (ι→ℝ)→ℂ) :
    logCellIntegral (fun i => a*w i) lo hi f=a^Fintype.card ι • logCellIntegral w lo hi f := by
  unfold logCellIntegral
  simp_rw [logCellDensity_scale,mul_smul]
  exact integral_smul _ _

omit [DecidableEq ι] in
theorem principalIntegral_eq (M : ℕ) (lo hi Z : ι→ℝ) (f : (ι→ℝ)→ℂ) :
    principalIntegral M lo hi Z f=
      ((Nat.totient M:ℝ)^Fintype.card ι)⁻¹ • primeIntegral lo hi Z f := by
  unfold principalIntegral primeIntegral
  have hw : (fun i => ((Nat.totient M:ℝ)*Z i)⁻¹)=
      (fun i => (Nat.totient M:ℝ)⁻¹*(Z i)⁻¹) := by funext i; exact mul_inv _ _
  rw [hw,logCellIntegral_scale,inv_pow]

theorem principalIntegral_mul_sum (M : ℕ) [NeZero M] (lo hi Z : ι→ℝ)
    (f : (ι→ℝ)→ℂ) (F : (ι→(ZMod M)ˣ)→ℂ) :
    principalIntegral M lo hi Z f*(∑u:ι→(ZMod M)ˣ,F u)=
      primeIntegral lo hi Z f*ResidueHaar.average F := by
  rw [principalIntegral_eq]
  simp only [ResidueHaar.average,Fintype.card_fun,ZMod.card_units_eq_totient,Nat.cast_pow,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_natCast]
  ring

end Ostmann.Arithmetic.HistoryPrincipalIntegralAverage

end

end OAI
