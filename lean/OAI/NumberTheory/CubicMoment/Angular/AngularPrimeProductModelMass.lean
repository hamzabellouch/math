import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductSharpMoments
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeProductCentered

namespace OAI

/-! The literal product model is bounded by the actual prime l¹ masses.
This preserves their density savings at the exceptional transition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullAngularPrimeProductModel_l1_bound (R : ℝ)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (u : ℝ) :
    ‖fullAngularPrimeProductModel ℓ R WA WB XA XB u‖ ≤
      (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1, ‖fullPrimeCoefficient R WA XA a‖)*
      (∑ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖fullPrimeCoefficient R WB XB b‖)*
      (cStar*((∏ i, XA i)*(∏ i, XB i))^(-1/6:ℝ)) := by
  let D := (∏ i, XA i)*(∏ i, XB i)
  have hD : 0 < D := mul_pos (Finset.prod_pos (fun i _ => hXA i))
    (Finset.prod_pos (fun i _ => hXB i))
  let F := fun a b : Eisenstein =>
    theta ℓ (a*b)*((cStar:ℂ)*(idealMoebius (a*b):ℂ)^2*((norm (a*b)^(-1/6:ℝ):ℝ):ℂ))*normTwist u (a*b)
  have hF (a : Eisenstein) (ha : a ∈ fullSquarefreePrimeSupport R WA XA 1)
      (b : Eisenstein) (hb : b ∈ fullSquarefreePrimeSupport R WB XB 1) :
      ‖F a b‖ ≤ cStar*D^(-1/6:ℝ) := by
    have hn : D ≤ norm (a*b) := by
      rw [norm_mul_eq]
      exact mul_le_mul (fullPrimeProduct_norm_bounds R WA XA hXA hAlo hAhi
        (Finset.mem_filter.mp ha).1).1
        (fullPrimeProduct_norm_bounds R WB XB hXB hBlo hBhi
          (Finset.mem_filter.mp hb).1).1
        (Finset.prod_nonneg (fun i _ => (hXB i).le)) (norm_nonneg a)
    have hm : ‖(idealMoebius (a*b):ℂ)^2‖ ≤ 1 := by
      rw [norm_pow]
      simpa only [one_pow] using pow_le_pow_left₀ (_root_.norm_nonneg _)
        (norm_idealMoebius_le_one (a*b)) 2
    have hab : a*b ≠ 0 := mul_ne_zero (primary_ne_zero (fullSquarefreePrimeSupport_primary R WA XA 1 ha).1)
      (primary_ne_zero (fullSquarefreePrimeSupport_primary R WB XB 1 hb).1)
    simp only [F,norm_mul,norm_theta hab,one_mul,norm_normTwist,mul_one,Complex.norm_real,
      Real.norm_of_nonneg cStar_pos.le,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg (a*b)) (-1/6:ℝ))]
    calc
      _ ≤ cStar*1*(norm (a*b))^(-1/6:ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm cStar_pos.le)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hD hn (by norm_num)) cStar_pos.le
  convert fullPrimeProduct_weighted_bound R WA WB XA XB F hF using 1
  simp only [F,fullAngularPrimeProductModel,mul_assoc]

theorem fullAngularPrimeProductModel_density_bound
    {R A B Z MA MB : ℝ} (hA : 0 < A) (hB : 0 < B) (hZ : 0 < Z)
    (hMA : 0 ≤ MA) (_hMB : 0 ≤ MB)
    (WA : κ → ℝ → ℂ) (WB : ι → ℝ → ℂ) (XA : κ → ℝ) (XB : ι → ℝ)
    (hXA : ∀ i, 0 < XA i) (hXB : ∀ i, 0 < XB i)
    (hprodA : (∏ i, XA i) = A) (hprodB : (∏ i, XB i) = B)
    (hAlo : ∀ i x, x < 1 → WA i x = 0) (hAhi : ∀ i x, R < x → WA i x = 0)
    (hBlo : ∀ i x, x < 1 → WB i x = 0) (hBhi : ∀ i x, R < x → WB i x = 0)
    (hmA : (∑ a ∈ fullSquarefreePrimeSupport R WA XA 1, ‖fullPrimeCoefficient R WA XA a‖) ≤ MA*A/Z^2)
    (hmB : (∑ b ∈ fullSquarefreePrimeSupport R WB XB 1, ‖fullPrimeCoefficient R WB XB b‖) ≤ MB*B/Z)
    (u : ℝ) :
    ‖fullAngularPrimeProductModel ℓ R WA WB XA XB u‖ ≤
      (MA*MB*cStar)*A^(5/6:ℝ)*B^(5/6:ℝ)/Z^3 := by
  have hc := cStar_pos
  have hh := fullAngularPrimeProductModel_l1_bound ℓ R WA WB XA XB hXA hXB hAlo hAhi hBlo hBhi u
  rw [hprodA,hprodB] at hh
  apply hh.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul hmA hmB
    (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _)) (by positivity)) (by positivity)).trans_eq
  have he : (A*B)*(A*B)^(-1/6:ℝ) = A^(5/6:ℝ)*B^(5/6:ℝ) := by
    nth_rw 1 [← Real.rpow_one (A*B)]
    rw [← Real.rpow_add (mul_pos hA hB)]
    norm_num
    exact Real.mul_rpow hA.le hB.le
  calc
    (MA*A/Z^2)*(MB*B/Z)*(cStar*(A*B)^(-1/6:ℝ)) =
      (MA*MB*cStar)*((A*B)*(A*B)^(-1/6:ℝ))/Z^3 := by ring
    _ = _ := by rw [he]; ring

end CubicFirstMoment

end

end OAI
