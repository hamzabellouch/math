import Mathlib

namespace OAI

/-! Calabi Cutoff Algebra. -/

section

 

namespace CalabiEstimate
lemma cross_absorb {x y r : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hr : r^2 ≤ 8*x*y) : -(y/2+4*x) ≤ r := by
  have hab : |r| ≤ y/2+4*x := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (y/2-4*x)]
  exact (neg_le_neg hab).trans (neg_abs_le r)

lemma cutoff_max_bound {S Q η C δ LS LT Lη cross : ℝ}
    (hS : 0 ≤ S) (hQ : 0 ≤ Q) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hLS : Q-C*(1+S) ≤ LS) (hLT : δ*S-C ≤ LT)
    (hLη : -C ≤ Lη) (hcross : cross^2 ≤ 8*C*η*S*Q)
    (hmax : η*LS+S*Lη+cross+((6*C+1)/δ)*LT ≤ 0) :
    S ≤ C*(1+(6*C+1)/δ) := by
  let A := (6*C+1)/δ
  have hA : 0 ≤ A := div_nonneg (by positivity) hδ.le
  have hAd : A*δ = 6*C+1 := by dsimp [A]; field_simp
  have hx : -(η*Q/2+4*(C*S)) ≤ cross := by
    apply cross_absorb (mul_nonneg hC hS) (mul_nonneg hη hQ)
    nlinarith [hcross]
  have h1 := mul_le_mul_of_nonneg_left hLS hη
  have h2 := mul_le_mul_of_nonneg_left hLη hS
  have h3 := mul_le_mul_of_nonneg_left hLT hA
  have h4 := mul_le_mul_of_nonneg_right hη1 (mul_nonneg hC (by linarith : 0 ≤ 1+S))
  have h5 := mul_nonneg hη hQ
  have he : A*(δ*S-C) = (6*C+1)*S-A*C := by rw [mul_sub,← mul_assoc,hAd]
  rw [he] at h3
  change η*LS+S*Lη+cross+A*LT ≤ 0 at hmax
  change S ≤ C*(1+A)
  nlinarith
end CalabiEstimate

end

end OAI
