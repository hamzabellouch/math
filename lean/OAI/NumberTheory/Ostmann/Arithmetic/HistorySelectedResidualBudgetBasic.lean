import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedResidualBudget
open Filter

def residualBudget (G F B C D L : ℝ) : ℝ :=
  Real.exp (D*(L+1)^2) *
    (G*Real.exp (-Real.exp ((21/2000:ℝ)*L)) +
     F*Real.exp (-Real.exp ((3/2000:ℝ)*L)) +
     B*Real.exp (-Real.exp (ScaleBudget.bulk.target*L)) +
     C*Real.exp (-Real.exp ((1/500:ℝ)*L)))

theorem residualBudget_le (G F B C D : ℝ) (hG : 0 ≤ G) (hF : 0 ≤ F)
    (_hB : 0 ≤ B) (hC : 0 ≤ C) {L : ℝ} (hL : 0 ≤ L) :
    residualBudget G F B C D L ≤
      Real.exp ((G+F+B+C)+D*(L+1)^2-Real.exp (ScaleBudget.bulk.target*L)) := by
  have hmono (a : ℝ) (ha : ScaleBudget.bulk.target ≤ a) :
      Real.exp (-Real.exp (a*L)) ≤ Real.exp (-Real.exp (ScaleBudget.bulk.target*L)) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hL)))
  have hg := mul_le_mul_of_nonneg_left (hmono (21/2000) (by norm_num [ScaleBudget.bulk])) hG
  have hf := mul_le_mul_of_nonneg_left (hmono (3/2000) (by norm_num [ScaleBudget.bulk])) hF
  have hc := mul_le_mul_of_nonneg_left (hmono (1/500) (by norm_num [ScaleBudget.bulk])) hC
  have hsum : G*Real.exp (-Real.exp ((21/2000:ℝ)*L))+
      F*Real.exp (-Real.exp ((3/2000:ℝ)*L))+
      B*Real.exp (-Real.exp (ScaleBudget.bulk.target*L))+
      C*Real.exp (-Real.exp ((1/500:ℝ)*L)) ≤
      (G+F+B+C)*Real.exp (-Real.exp (ScaleBudget.bulk.target*L)) := by nlinarith
  have hK : G+F+B+C ≤ Real.exp (G+F+B+C) := by
    linarith [Real.add_one_le_exp (G+F+B+C)]
  unfold residualBudget
  calc
    _ ≤ Real.exp (D*(L+1)^2)*((G+F+B+C)*Real.exp (-Real.exp (ScaleBudget.bulk.target*L))) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ ≤ Real.exp (D*(L+1)^2)*(Real.exp (G+F+B+C)*Real.exp (-Real.exp (ScaleBudget.bulk.target*L))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add,←Real.exp_add]; congr 1; ring

theorem residualBudget_eventually (G F B C D R : ℝ)
    (hG : 0 ≤ G) (hF : 0 ≤ F) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hR : 0 ≤ R) :
    ∀ᶠ L : ℝ in atTop, residualBudget G F B C D L ≤ Real.exp (-R*L) := by
  have hab : (0:ℝ) < ScaleBudget.bulk.target := by norm_num [ScaleBudget.bulk]
  have hx := ScaleBudget.eventually_poly_exp_le (G+F+B+C+4*D+R) 2
    (a := 0) (b := ScaleBudget.bulk.target) (K := 1) hab (by norm_num)
  filter_upwards [hx,eventually_ge_atTop (1:ℝ)] with L he hL
  simp only [zero_mul,Real.exp_zero,mul_one,one_mul] at he
  have hsq : 1 ≤ L^2 := by nlinarith
  have hsquare : (L+1)^2 ≤ 4*L^2 := by nlinarith
  have hlinear : L ≤ L^2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ G+F+B+C)
  have h2 := mul_le_mul_of_nonneg_left hsquare hD
  have h3 := mul_le_mul_of_nonneg_left hlinear hR
  apply (residualBudget_le G F B C D hG hF hB hC (by linarith)).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end Ostmann.Arithmetic.HistorySelectedResidualBudget

end

end OAI
