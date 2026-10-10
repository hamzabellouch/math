import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def dualWindowLower (M H T : ℝ) (e b : ℕ) : ℝ :=
  Real.sqrt ((e : ℝ)*H^2/(M*squarefreeDyadicBase b))/(2*T)
noncomputable def dualWindowUpper (M H T : ℝ) (e b : ℕ) : ℝ :=
  2*T*Real.sqrt ((e : ℝ)*H^2/(M*squarefreeDyadicBase b))

theorem dual_dyadic_window_parameters {M H T : ℝ} {e b n t : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hT : 1 ≤ T) (he : 0 < e) (hb : 0 < b)
    (hnlo : H ≤ (n : ℝ)) (hnhi : (n : ℝ) ≤ 2*H)
    (htlo : H ≤ (t : ℝ)) (hthi : (t : ℝ) ≤ 2*H) :
    0 < dualWindowLower M H T e b ∧
      dualWindowLower M H T e b ≤ Real.sqrt ((e : ℝ)*(n*t)/(M*b)) ∧
      Real.sqrt ((e : ℝ)*(n*t)/(M*b)) ≤ dualWindowUpper M H T e b ∧
      0 < T ∧ T ≤ min (Real.sqrt ((e : ℝ)*(n*t)/(M*b))/dualWindowLower M H T e b)
        (dualWindowUpper M H T e b/Real.sqrt ((e : ℝ)*(n*t)/(M*b))) ∧
      (dualWindowUpper M H T e b/Real.sqrt ((e : ℝ)*(n*t)/(M*b)))^2 ≤ 16*T^2 := by
  obtain ⟨hB,hblo,hbhi⟩ := squarefreeDyadicBase_bounds hb
  have hBr : (0 : ℝ) < squarefreeDyadicBase b := by exact_mod_cast hB
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hql : H^2 ≤ (n : ℝ)*t := by
    have h := mul_le_mul hnlo htlo hH.le (Nat.cast_nonneg n)
    simpa only [pow_two] using h
  have hqu : (n : ℝ)*t ≤ 4*H^2 := by
    have h := mul_le_mul hnhi hthi (Nat.cast_nonneg t) (by positivity)
    nlinarith
  obtain ⟨h1,h2⟩ := dual_square_scale_window (b := (b : ℝ)) her hM hBr hH
    (by exact_mod_cast hblo) (by exact_mod_cast hbhi.le) hql hqu
  exact poisson_window_parameters (Real.sqrt_pos.mpr (by positivity)) hT h1 h2

theorem dual_second_scalar_eq {M e q b : ℝ} (hM : 0 < M) (he : 0 < e)
    (hq : 0 < q) (hb : 0 < b) :
    (M/(e*q))*Real.sqrt q*Real.sqrt (e*q/(M*b)) = Real.sqrt (M/(e*b)) := by
  have hs : ((M/(e*q))*Real.sqrt q*Real.sqrt (e*q/(M*b)))^2 = M/(e*b) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt hq.le,Real.sq_sqrt (by positivity)]
    field_simp
  have hn : 0 ≤ (M/(e*q))*Real.sqrt q*Real.sqrt (e*q/(M*b)) := by positivity
  nlinarith [Real.sq_sqrt (show 0 ≤ M/(e*b) by positivity),Real.sqrt_nonneg (M/(e*b))]

theorem dual_second_scalar_le {M e q b : ℝ} (hM : 0 < M) (he : 1 ≤ e)
    (hq : 0 < q) (hb : 1 ≤ b) :
    (M/(e*q))*Real.sqrt q*Real.sqrt (e*q/(M*b)) ≤ Real.sqrt M := by
  rw [dual_second_scalar_eq hM (by linarith) hq (by linarith)]
  apply Real.sqrt_le_sqrt
  exact div_le_self hM.le (one_le_mul_of_one_le_of_one_le he hb)

end Ostmann.QuadraticSieve

end OAI
