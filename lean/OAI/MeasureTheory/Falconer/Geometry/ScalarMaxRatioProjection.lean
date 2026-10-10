import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientMul
import OAI.MeasureTheory.Falconer.Estimates.ScalarDilationBound

namespace OAI

/-! Normalizing by an actual coefficient of magnitude at least one costs
only a fixed polynomial, even when the coefficient radius grows with scale. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_max_ratio_projection {δ K a b : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (X : Finset ℝ) (hX : X.Nonempty) (ha : |a| ≤ K) (hb : 1 ≤ |b|)
    (hd : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (hpa : ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤ K*(scalarCells δ X).card)
    (hpb : ((scalarCells δ (X+X.image (fun x => b*x))).card:ℝ) ≤ K*(scalarCells δ X).card) :
    ((scalarCells δ (X+X.image (fun x => (a/b)*x))).card:ℝ) ≤
      (68096*(5:ℝ)^8)*K^9*(scalarCells δ X).card := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hbpos : 0 < |b| := zero_lt_one.trans_le hb
  have hbne : b ≠ 0 := abs_pos.mp hbpos
  have hbinv : |b⁻¹| ≤ (1:ℝ) := by
    rw [abs_inv]
    exact (inv_le_one₀ hbpos).2 hb
  have hi := scalar_inverse_coefficient_cells hδ hbne X 1 (by simpa only [Nat.cast_one] using hbinv)
  have hiR : ((scalarCells δ (X+X.image (fun x => b⁻¹*x))).card:ℝ) ≤
      5*((scalarCells δ (X+X.image (fun x => b*x))).card:ℝ) := by exact_mod_cast hi
  have hib : ((scalarCells δ (X+X.image (fun x => b⁻¹*x))).card:ℝ) ≤
      (5*K)*(scalarCells δ X).card :=
    hiR.trans ((mul_le_mul_of_nonneg_left hpb (by norm_num)).trans_eq (by ring))
  let m := ⌈K⌉₊
  have hmlo : K ≤ (m:ℝ) := Nat.le_ceil K
  have hmhi : (m:ℝ) ≤ 2*K := by
    have hh := Nat.ceil_lt_add_one hK0
    change (m:ℝ) < K+1 at hh
    linarith
  have hK5 : K ≤ 5*K := by linarith
  have hm := scalar_coefficient_mul hδ (by positivity : 0 ≤ 5*K) X hX m (ha.trans hmlo)
    (hd.trans (mul_le_mul_of_nonneg_right hK5 (Nat.cast_nonneg _)))
    (hpa.trans (mul_le_mul_of_nonneg_right hK5 (Nat.cast_nonneg _))) hib
  have hf : 3584*(4*(m:ℝ)+11) ≤ 68096*K := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hf (show 0 ≤ (5*K)^8*(scalarCells δ X).card by positivity)
  calc
    _ ≤ (3584*(4*(m:ℝ)+11))*(5*K)^8*(scalarCells δ X).card := by
      simpa only [div_eq_mul_inv] using hm
    _ ≤ (68096*K)*((5*K)^8*(scalarCells δ X).card) := by nlinarith
    _ = _ := by ring

end Falconer

end OAI
