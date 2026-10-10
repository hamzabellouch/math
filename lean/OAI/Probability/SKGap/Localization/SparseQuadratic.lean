import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
open Real
open scoped RealInnerProductSpace
namespace SKGap

lemma norm_product_le_sqrt {E : Type*} [SeminormedAddCommGroup E]
    (b c : E) {q η : ℝ} (hq : 0 ≤ q) (hη : 0 ≤ η)
    (hb : ‖b‖^2 ≤ q) (hc : ‖c‖^2 ≤ η*q) : ‖b‖*‖c‖ ≤ sqrt η*q := by
  have hs := sq_sqrt hη
  have hh := mul_le_mul hb hc (sq_nonneg ‖c‖) hq
  have hplus : 0 ≤ sqrt η*q := mul_nonneg (sqrt_nonneg η) hq
  have hnorm : 0 ≤ ‖b‖*‖c‖ := mul_nonneg (norm_nonneg b) (norm_nonneg c)
  apply (sq_le_sq₀ hnorm hplus).mp
  calc
    (‖b‖*‖c‖)^2=‖b‖^2*‖c‖^2 := by ring
    _ ≤ q*(η*q) := hh
    _ = (sqrt η*q)^2 := by rw [mul_pow,hs];ring

lemma sparse_quadratic_split {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E) (b c : E)
    {q η ε M : ℝ} (hq : 0 ≤ q) (hη : 0 ≤ η) (hM : 0 ≤ M)
    (hB : ‖B‖ ≤ M) (hb : ‖b‖^2 ≤ q) (hc : ‖c‖^2 ≤ η*q)
    (hs : |⟪b,B b⟫| ≤ ε*q) :
    |⟪b+c,B (b+c)⟫| ≤ (ε+M*(2*sqrt η+η))*q := by
  have hbound (u v : E) : |⟪u,B v⟫| ≤ M*‖u‖*‖v‖ := by
    calc
      _ ≤ ‖u‖*‖B v‖ := abs_real_inner_le_norm u (B v)
      _ ≤ ‖u‖*(‖B‖*‖v‖) := mul_le_mul_of_nonneg_left (B.le_opNorm v) (norm_nonneg u)
      _ ≤ ‖u‖*(M*‖v‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hB (norm_nonneg v)) (norm_nonneg u)
      _ = _ := by ring
  have hprod := norm_product_le_sqrt b c hq hη hb hc
  have hbc : |⟪b,B c⟫| ≤ M*(sqrt η*q) := by
    calc
      _ ≤ M*(‖b‖*‖c‖) := by simpa only [mul_assoc] using hbound b c
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod hM
  have hcb : |⟪c,B b⟫| ≤ M*(sqrt η*q) := by
    calc
      _ ≤ M*(‖b‖*‖c‖) := by simpa only [mul_comm,mul_left_comm,mul_assoc] using hbound c b
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod hM
  have hcc : |⟪c,B c⟫| ≤ M*(η*q) := by
    calc
      _ ≤ M*‖c‖^2 := by simpa only [sq,mul_assoc] using hbound c c
      _ ≤ _ := mul_le_mul_of_nonneg_left hc hM
  rw [map_add,inner_add_left,inner_add_right,inner_add_right]
  calc
    _ ≤ (|⟪b,B b⟫|+|⟪b,B c⟫|)+(|⟪c,B b⟫|+|⟪c,B c⟫|) :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ (ε*q+M*(sqrt η*q))+(M*(sqrt η*q)+M*(η*q)) :=
      add_le_add (add_le_add hs hbc) (add_le_add hcb hcc)
    _ = _ := by ring
end SKGap

end
end

end OAI
