import OAI.NumberTheory.Ostmann.Characters.Gauss
import OAI.NumberTheory.Ostmann.Tree.CharacterFourth
import OAI.NumberTheory.Ostmann.Tree.PairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem fourier_mulChar_gauss (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b,fourier f b=(w b:ℂ)) (α : MulChar (ZMod p) ℂ) (hα : α≠1) (a : ZMod p) :
    fourier (fun d => f d*α d) a =
      (p:ℂ)⁻¹*gaussSum α ZMod.stdAddChar*α⁻¹ (-1)*weightedCharacterSum w α⁻¹ a := by
  have hfin (d : ZMod p) : f d=∑ b,(w b:ℂ)*ZMod.stdAddChar (b*d) := by
    rw [fourier_inversion f d]
    simp only [hf]
  rw [fourier_apply]
  simp_rw [hfin, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hin (b : ZMod p) :
      (∑ d : ZMod p, (w b:ℂ)*ZMod.stdAddChar (b*d)*α d*ZMod.stdAddChar (-(a*d))) =
      (w b:ℂ)*α⁻¹ (-1)*α⁻¹ (a-b)*gaussSum α ZMod.stdAddChar := by
    calc
      _ = (w b:ℂ)*∑ d : ZMod p, α d*ZMod.stdAddChar ((b-a)*d) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [sub_mul,AddChar.map_sub_eq_div,AddChar.map_neg_eq_inv]
        ring
      _ = _ := by
        rw [Characters.gauss_transform α hα ZMod.stdAddChar (b-a),
          show b-a=(-1)*(a-b) from by ring, map_mul]
        ring
  simp_rw [hin]
  simp only [weightedCharacterSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem norm_fourier_mulChar_fourth (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ b,fourier f b=(w b:ℂ)) (α : MulChar (ZMod p) ℂ) (hα : α≠1) (a : ZMod p) :
    ‖fourier (fun d => f d*α d) a‖^4 =
      (p:ℝ)⁻¹^2*‖weightedCharacterSum w α⁻¹ a‖^4 := by
  rw [fourier_mulChar_gauss f w hf α hα a]
  have hunit : ‖α⁻¹ (-1:ZMod p)‖=1 := by
    simpa only [Units.val_neg,Units.val_one] using mulChar_norm_unit α⁻¹ (-1:(ZMod p)ˣ)
  simp only [norm_mul,norm_inv,Complex.norm_natCast,hunit,mul_one,
    Characters.norm_gaussSum α hα ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)]
  rw [ZMod.card]
  have hp : (p:ℝ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs : (Real.sqrt (p:ℝ))^2=p := Real.sq_sqrt (by positivity)
  calc
    _ = ((p:ℝ)⁻¹)^4*((Real.sqrt (p:ℝ))^2)^2*‖weightedCharacterSum w α⁻¹ a‖^4 := by ring
    _ = _ := by rw [hs]; field_simp

end
end Ostmann.FiniteField

end OAI
