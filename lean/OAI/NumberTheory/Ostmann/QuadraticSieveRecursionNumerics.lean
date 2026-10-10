import OAI.NumberTheory.Ostmann.QuadraticSieveRecursionNumericsBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem recursion_min_coefficients {M N r P : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hr : 0 < r) (hP : 1 ≤ P) :
    let m := min 1 (r*N/(M*P))
    let t := (M/N)*Real.sqrt P*m
    t^2 ≤ r^2 ∧ t^2*N ≤ r*M ∧ t^2*N^2 ≤ M^2*P := by
  let m := min 1 (r*N/(M*P))
  let t := (M/N)*Real.sqrt P*m
  have hPp : 0 < P := by linarith
  have hs : 0 < Real.sqrt P := Real.sqrt_pos.mpr hPp
  have hs1 : 1 ≤ Real.sqrt P := (Real.one_le_sqrt).mpr hP
  have hs2 := Real.sq_sqrt hPp.le
  have hm0 : 0 ≤ m := le_min (by norm_num) (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmR : m ≤ r*N/(M*P) := min_le_right _ _
  have hm2 : m^2 ≤ 1 := by nlinarith
  have hm2R : m^2 ≤ r*N/(M*P) := by nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t ≤ r := by
    calc
      t ≤ (M/N)*Real.sqrt P*(r*N/(M*P)) :=
        mul_le_mul_of_nonneg_left hmR (by positivity)
      _ = r/Real.sqrt P := by
        field_simp
        nlinarith
      _ ≤ r := div_le_self hr.le hs1
  have ht2 : t^2 = M^2/N^2*P*m^2 := by
    dsimp [t]
    rw [mul_pow,mul_pow,div_pow,hs2]
  refine ⟨by nlinarith,?_,?_⟩
  · rw [ht2]
    calc
      M^2/N^2*P*m^2*N = (M^2/N*P)*m^2 := by field_simp
      _ ≤ (M^2/N*P)*(r*N/(M*P)) := mul_le_mul_of_nonneg_left hm2R (by positivity)
      _ = _ := by field_simp
  · rw [ht2]
    calc
      M^2/N^2*P*m^2*N^2 = (M^2*P)*m^2 := by field_simp
      _ ≤ (M^2*P)*1 := mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = _ := mul_one _

theorem recursion_E3 {M N B x d₁ d₂ : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hB : 0 < B) (hx : 0 ≤ x)
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) :
    (M/N)*Real.sqrt (d₁*d₂)*min 1 (N/(Real.sqrt (M*B)*(d₁*d₂))) *
      Real.sqrt ((x+N/d₁)*(x+N/d₂)) ≤
        M+Real.sqrt (M/B)*x := by
  let r := Real.sqrt (M/B)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hroot : r*Real.sqrt (M*B) = M := by
    dsimp [r]
    rw [← Real.sqrt_mul (by positivity : 0 ≤ M/B)]
    rw [show M/B*(M*B) = M^2 by field_simp,
      Real.sqrt_sq hM.le]
  have hP : 1 ≤ d₁*d₂ := one_le_mul_of_one_le_of_one_le hd₁ hd₂
  have hPp : 0 < d₁*d₂ := by linarith
  have hs : 0 < Real.sqrt (M*B) := Real.sqrt_pos.mpr (by positivity)
  have hratio : r*N/(M*(d₁*d₂)) = N/(Real.sqrt (M*B)*(d₁*d₂)) := by
    apply (div_eq_div_iff (by positivity) (by positivity)).mpr
    calc
      r*N*(Real.sqrt (M*B)*(d₁*d₂)) = (r*Real.sqrt (M*B))*N*(d₁*d₂) := by ring
      _ = _ := by rw [hroot]; ring
  have hcoeff := recursion_min_coefficients hM hN hr hP
  dsimp only at hcoeff
  rw [hratio] at hcoeff
  have hh := recursion_geometric_mean_bound hx hN.le hd₁ hd₂ hr.le hM.le
    hcoeff.1 hcoeff.2.1 hcoeff.2.2
  simpa only [r,add_comm] using hh

end Ostmann.QuadraticSieve

end

end OAI
