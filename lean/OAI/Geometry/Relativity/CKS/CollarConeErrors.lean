import OAI.Geometry.Relativity.CKS.SmoothOuterDEC

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma radial_momentum_bound {r w B q q₀ : ℝ} (hr : 1 ≤ r) (hw : 0 ≤ w) (hB : 0 ≤ B)
    (hq : |q-q₀-2*w/r^2| ≤ B*w/r^3) : |q-q₀| ≤ (2+B)*w/r^2 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have ha : |q-q₀| ≤ |q-q₀-2*w/r^2|+|2*w/r^2| := by
    have := abs_add_le (q-q₀-2*w/r^2) (2*w/r^2)
    convert this using 1
    congr 1
    ring
  rw [abs_of_nonneg (by positivity : 0 ≤ 2*w/r^2)] at ha
  have he : B*w/r^3 ≤ B*w/r^2 := by gcongr; norm_num
  have hid : B*w/r^2+2*w/r^2 = (2+B)*w/r^2 := by ring
  linarith

lemma smallNull_to_CQ {r w S B D T Q a a₀ q q₀ x x₀ : ℝ}
    (hr : 1 ≤ r) (hw : 0 ≤ w) (hS : 0 ≤ S) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (hx : |x-x₀-2*w/(r^3*Real.sqrt r)| ≤ S*w/r^4)
    (hq : |q-q₀-2*w/r^2| ≤ B*w/r^3) (hq₀ : |q₀| ≤ Q/r^3)
    (ha : |a-1| ≤ D/r^2) (ha₀ : |a-a₀| ≤ T*w/r^3) :
    |((x+a*q)-(x₀+a₀*q₀))-(q-q₀)-2*w/(r^3*Real.sqrt r)| ≤
      (S+D*(2+B)+T*Q)*w/r^4 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdq := radial_momentum_bound hr hw hB hq
  have h₁ : |(a-1)*(q-q₀)| ≤ D*(2+B)*w/r^4 := by
    rw [abs_mul]
    calc
      _ ≤ (D/r^2)*((2+B)*w/r^2) := mul_le_mul ha hdq (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have h₂ : |(a-a₀)*q₀| ≤ T*Q*w/r^4 := by
    rw [abs_mul]
    calc
      _ ≤ (T*w/r^3)*(Q/r^3) := mul_le_mul ha₀ hq₀ (abs_nonneg _) (by positivity)
      _ = T*Q*w/r^6 := by ring
      _ ≤ _ := by gcongr; norm_num
  have he : ((x+a*q)-(x₀+a₀*q₀))-(q-q₀)-2*w/(r^3*Real.sqrt r) =
      (x-x₀-2*w/(r^3*Real.sqrt r))+(a-1)*(q-q₀)+(a-a₀)*q₀ := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have ht := abs_add_le (x-x₀-2*w/(r^3*Real.sqrt r)) ((a-1)*(q-q₀))
  have heq : |S| * w/r^4+D*(2+B)*w/r^4+T*Q*w/r^4 = (|S| + D*(2+B)+T*Q)*w/r^4 := by ring
  rw [← abs_of_nonneg hS] at hx ⊢
  linarith

end
end CKSAngularGeometry

end

end OAI
