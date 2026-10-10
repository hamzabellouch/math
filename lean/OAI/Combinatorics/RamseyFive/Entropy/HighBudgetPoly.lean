import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.HighMomentBudget

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open scoped BigOperators

noncomputable def highBudgetPoly (a p P : ℝ) : ℝ :=
  3+40*p^2+20*p^4*(200*p+2*P)^2+
    p^4*(P^200*a+400*(2*P)^200)+2*p^200*a+400

lemma highMomentBudget_normalized (Q a B b L : ℝ) (p R N₂ : ℕ)
    (hB : 0<B) (hb : 0<b) :
    highMomentBudget Q (a*B^2) (a*B) B b L p R N₂ =
      B*(2+1/B+(p:ℝ)^2*(Q/(B*b^8))+
        (p:ℝ)^4*((N₂:ℝ)*b/B)*(200*p+2*((R:ℝ)*L))^2+
        (p:ℝ)^4*(((R:ℝ)*L)^200*a+(Q/B^2)*(2*((R:ℝ)*L))^200)+
        2*(p:ℝ)^200*a+Q/B^2) := by
  unfold highMomentBudget highCertificateMajorant
  field_simp
  ring

lemma highMomentBudget_le_poly (Q a B b L : ℝ) (p R N₂ : ℕ)
    (hB : 1≤B) (hb : 0<b) (_ha : 0≤a) (_hL : 0≤L)
    (hroot : Q/(B*b^8)≤40) (hanchor : (N₂:ℝ)*b/B≤20) (hpair : Q/B^2≤400) :
    highMomentBudget Q (a*B^2) (a*B) B b L p R N₂ ≤
      B*highBudgetPoly a p ((R:ℝ)*L) := by
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  rw [highMomentBudget_normalized Q a B b L p R N₂ hB0 hb]
  unfold highBudgetPoly
  apply mul_le_mul_of_nonneg_left _ hB0.le
  have hBi : 1/B≤1 := (div_le_one hB0).mpr hB
  calc
    _ ≤ 2+1+(p:ℝ)^2*40+(p:ℝ)^4*20*(200*p+2*((R:ℝ)*L))^2+
        (p:ℝ)^4*(((R:ℝ)*L)^200*a+400*(2*((R:ℝ)*L))^200)+2*(p:ℝ)^200*a+400 := by
      gcongr
    _ = _ := by ring

end SharpRamseyFive.ScoreGeometry

end

end OAI
