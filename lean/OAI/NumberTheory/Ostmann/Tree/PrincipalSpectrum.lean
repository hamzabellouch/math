import OAI.NumberTheory.Ostmann.Tree.TwistedPairSpectrum

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem fourier_mul_principal (f : ZMod p → ℂ) (a : ZMod p) :
    fourier (fun d => f d*(1:MulChar (ZMod p) ℂ) d) a =
      fourier f a-(p:ℂ)⁻¹*f 0 := by
  classical
  have he (d : ZMod p) : f d*(1:MulChar (ZMod p) ℂ) d*ZMod.stdAddChar (-(a*d)) =
      f d*ZMod.stdAddChar (-(a*d))-(if d=0 then f 0 else 0) := by
    by_cases hd : d=0
    · simp [hd,MulChar.map_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hd)]
      simp [hd]
  simp only [fourier_apply,he,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

theorem twistedPairFourier_scale (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) :
    twistedPairFourier g σ χ α a = α (σ⁻¹:(ZMod p)ˣ) *
      fourier (fun d => pairSpectrum g χ d*α d) ((σ⁻¹:(ZMod p)ˣ)*a) := by
  have hunit : α (σ⁻¹:(ZMod p)ˣ)*α σ=1 := by rw [← map_mul,← Units.val_mul,inv_mul_cancel,Units.val_one,map_one]
  have he : (fun d => pairSpectrum g χ ((σ:ZMod p)*d)*α d) =
      (fun d => α (σ⁻¹:(ZMod p)ˣ)*((pairSpectrum g χ ((σ:ZMod p)*d))*α ((σ:ZMod p)*d))) := by
    funext d
    rw [map_mul]
    calc
      _ = (α (σ⁻¹:(ZMod p)ˣ)*α σ)*(pairSpectrum g χ ((σ:ZMod p)*d)*α d) := by rw [hunit,one_mul]
      _ = _ := by ring
  unfold twistedPairFourier
  rw [he,fourier_const_mul]
  congr 1
  exact fourier_unitMul (fun d => pairSpectrum g χ d*α d) σ a

theorem norm_twistedPairFourier_scale (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ α : MulChar (ZMod p) ℂ) (a : ZMod p) :
    ‖twistedPairFourier g σ χ α a‖ =
      ‖fourier (fun d => pairSpectrum g χ d*α d) ((σ⁻¹:(ZMod p)ˣ)*a)‖ := by
  rw [twistedPairFourier_scale,norm_mul,mulChar_norm_unit,one_mul]

theorem twistedPairFourier_principal (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) (hg0 : g 0=0) :
    twistedPairFourier g σ χ 1 a =
      ((pairWeight g χ ((σ⁻¹:(ZMod p)ˣ)*a)-
        (Fintype.card (ZMod p)ˣ:ℝ)⁻¹*l2Sq g : ℝ):ℂ) := by
  rw [twistedPairFourier_scale,MulChar.one_apply_coe,one_mul,fourier_mul_principal,
    fourier_pairSpectrum,pairSpectrum_zero g χ hg0]
  have hp : (p:ℂ)≠0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  push_cast
  field_simp

theorem norm_twistedPairFourier_principal_le (g : ZMod p → ℂ) (σ : (ZMod p)ˣ)
    (χ : MulChar (ZMod p) ℂ) (a : ZMod p) (hg0 : g 0=0) (hg : l2Sq g≤1) :
    ‖twistedPairFourier g σ χ 1 a‖ ≤
      ((p:ℝ)/(Fintype.card (ZMod p)ˣ:ℝ))*(correlationBound g:ℝ)^2+
        (Fintype.card (ZMod p)ˣ:ℝ)⁻¹ := by
  rw [twistedPairFourier_principal g σ χ a hg0,Complex.norm_real,Real.norm_eq_abs]
  have hw := pairWeight_nonneg g χ ((σ⁻¹:(ZMod p)ˣ)*a)
  have hz : 0≤(Fintype.card (ZMod p)ˣ:ℝ)⁻¹*l2Sq g := mul_nonneg (by positivity) (l2Sq_nonneg g)
  calc
    _ ≤ |pairWeight g χ ((σ⁻¹:(ZMod p)ˣ)*a)|+
        |(Fintype.card (ZMod p)ˣ:ℝ)⁻¹*l2Sq g| := abs_sub _ _
    _ = pairWeight g χ ((σ⁻¹:(ZMod p)ˣ)*a)+(Fintype.card (ZMod p)ˣ:ℝ)⁻¹*l2Sq g := by rw [abs_of_nonneg hw,abs_of_nonneg hz]
    _ ≤ _ := add_le_add (pairWeight_le g χ _)
      ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq (mul_one _))

end
end Ostmann.FiniteField

end OAI
