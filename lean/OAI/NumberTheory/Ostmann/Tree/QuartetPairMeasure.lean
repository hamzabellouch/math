import OAI.NumberTheory.Ostmann.Tree.QuartetAverage
import OAI.NumberTheory.Ostmann.Tree.SamePairMajorant

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.Quartet
open Density

theorem average_fintype_eq {A : Type*} (i j : Fintype A) (f : A → ℝ) :
    @average A i f = @average A j f := by
  congr
  exact Subsingleton.elim _ _

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem inverse_square_average_domination (K : Fˣ) (H : Fˣ → ℝ) (hH : ∀ x, 0≤H x) :
    average (fun z : Fˣ => H (K/z^2)) ≤ 2*average H := by
  have he := (Equiv.inv Fˣ).bijective.sum_comp (fun z : Fˣ => H (K*z^2))
  have hh : average (fun z : Fˣ => H (K/z^2)) = average (fun z : Fˣ => H (K*z^2)) := by
    unfold average
    congr 1
  rw [hh]
  have hs := square_average_domination K H hH
  simp only [average_fintype_eq _ (inferInstance : Fintype Fˣ)] at hs
  exact hs

end Ostmann.Tree.Quartet
namespace Ostmann.FiniteField
open Ostmann.Tree.Density Ostmann.Tree.Quartet
variable {p : ℕ} [Fact p.Prime]

theorem pairTest_square_mean (g : ZMod p → ℂ) (σ K : (ZMod p)ˣ)
    (d : ZMod p) (hg0 : g 0=0) :
    average (fun h : (ZMod p)ˣ => ‖pairTest g σ d (((K*h^2:(ZMod p)ˣ):ZMod p)*d)‖^2) ≤
      2*pairSecondMoment g σ d := by
  by_cases hd : d=0
  · subst d
    simp [pairTest_zero g σ hg0, pairSecondMoment_zero g σ hg0, average]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  have he (h : (ZMod p)ˣ) : (((K*h^2:(ZMod p)ˣ):ZMod p)*d) = (K*D*h^2:(ZMod p)ˣ) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, D, Units.val_mk0]
    ring
  simp_rw [he]
  have hs := square_average_domination (K*D) (fun t : (ZMod p)ˣ => ‖pairTest g σ d t‖^2)
    (fun _ => sq_nonneg _)
  simp only [average_fintype_eq _ (inferInstance : Fintype (ZMod p)ˣ)] at hs
  exact hs

theorem pairTest_inverse_square_bound (g : ZMod p → ℂ) (σ K : (ZMod p)ˣ)
    (d : ZMod p) (ρ : MulChar (ZMod p) ℂ) (hg0 : g 0=0) :
    ‖mellin (fun z : (ZMod p)ˣ => pairTest g σ d (((K/z^2:(ZMod p)ˣ):ZMod p)*d)) ρ‖^2 ≤
      2*pairSquareEnergy g σ ρ⁻¹ d := by
  classical
  by_cases hd : d=0
  · subst d
    simp [pairTest_zero g σ hg0, mellin, pairSquareEnergy, deletedPairEnergy]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  have he (z : (ZMod p)ˣ) : (((K/z^2:(ZMod p)ˣ):ZMod p)*d) = (K*D/z^2:(ZMod p)ˣ) := by
    simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, D, Units.val_mk0]
    ring
  simp_rw [he]
  have hb := mellin_inverse_square_pullback (fun t : (ZMod p)ˣ => pairTest g σ d t) (K*D) ρ
  have hm (χ : MulChar (ZMod p) ℂ) :
      mellin (fun t : (ZMod p)ˣ => pairTest g σ d t) χ = pairSpectrum g χ ((σ:ZMod p)*d) := by
    simpa only [Units.val_one, mul_one, map_one, one_mul] using pairTest_mellin_mul g σ 1 χ d hd hg0
  simp_rw [hm] at hb
  simpa only [pairSquareEnergy, deletedPairEnergy, hd, ↓reduceIte] using hb

theorem pairMobius_sum_real (y : (ZMod p)ˣ) (H : ZMod p → ℝ)
    (h0 : H 0=0) (hy : H y=0) :
    (∑ t : ZMod p,H (pairMobiusValue y t)) = ∑ d : ZMod p,H d := by
  have he := pairMobius_sum y (fun d => (H d:ℂ)) (by simp only [h0, Complex.ofReal_zero])
    (by simp only [hy, Complex.ofReal_zero])
  exact_mod_cast he

theorem mobius_inverse_square_mean (y K : (ZMod p)ˣ) (H : ZMod p → ℝ)
    (hH : ∀ d,0≤H d) (h0 : H 0=0) (hy : H y=0) :
    average (fun B : (ZMod p)ˣ => H (pairMobiusValue y (K/B^2 : (ZMod p)ˣ))) ≤
      2*((Fintype.card (ZMod p)ˣ:ℝ)⁻¹*∑ d : ZMod p,H d) := by
  have hs := inverse_square_average_domination K (fun r => H (pairMobiusValue y r))
    (fun r => hH _)
  have hz : H (pairMobiusValue y 0)=0 := by simpa only [pairMobiusValue,mul_zero,zero_div] using h0
  simpa only [average, sum_units_of_zero (fun t : ZMod p => H (pairMobiusValue y t)) hz, pairMobius_sum_real y H h0 hy] using hs

end Ostmann.FiniteField
end

end OAI
