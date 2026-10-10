import OAI.NumberTheory.JointDickman.Counting.CountingErrorRate

namespace OAI

/-! # Collecting the arithmetic errors into a summable singular-factor profile -/
namespace JointDickman

theorem countingError_bound
    {T j η R r Kr Kc Kp er ec ep ef pa g G δ q s Sj x : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hlag : η*T ≤ j)
    (hr : 0 ≤ r) (hrR : r ≤ R) (hKr : 0 ≤ Kr) (hKc : 0 ≤ Kc) (hKp : 0 ≤ Kp)
    (her : 0 ≤ er) (hec : 0 ≤ ec) (hG : 0 ≤ G) (hq0 : 0 ≤ q) (hq : q ≤ 1)
    (hδ : 0 ≤ δ) (hs : 1 ≤ s) (hSj : 0 ≤ Sj) (hSjs : Sj ≤ s)
    (hg : T*g ≤ G) (hp : T*pa ≤ ep+Kp*(T/j)*Sj)
    (hx : T*x ≤ r*(T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj)) :
    T*x ≤ (R*(Kr*(er+1)*|ep|+G+Kc*ec+|ef|+(Kr*Kp/η)*er)+
      R*(Kr*Kp/η+Kc)*q+R*δ/η)*s := by
  have hj : 0 < j := (mul_pos hη hT).trans_le hlag
  have hR : 0 ≤ R := hr.trans hrR
  have hratio : T/j ≤ 1/η := (div_le_div_iff₀ hj hη).mpr (by nlinarith only [hlag])
  have hSJ : (T/j)*Sj ≤ s/η :=
    (mul_le_mul hratio hSjs hSj (by positivity)).trans_eq (by ring)
  have hpa : T*pa ≤ |ep|+(Kp/η)*s := by
    have he := mul_le_mul_of_nonneg_left hSJ hKp
    calc
      _ ≤ ep+Kp*((T/j)*Sj) := by simpa only [mul_assoc] using hp
      _ ≤ |ep|+Kp*(s/η) := add_le_add (le_abs_self _) he
      _ = _ := by ring
  let V := Kr*(er+q)*(|ep|+(Kp/η)*s)+G+Kc*s*(ec+q)+|ef|+(δ/η)*s
  have hraw : T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj ≤ V := by
    have he : T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj =
        Kr*(er+q)*(T*pa)+T*g+Kc*s*(ec+q)+ef+δ*((T/j)*Sj) := by
      field_simp
    rw [he]
    dsimp only [V]
    have hδS := mul_le_mul_of_nonneg_left hSJ hδ
    calc
      _ ≤ Kr*(er+q)*(|ep|+(Kp/η)*s)+G+Kc*s*(ec+q)+|ef|+δ*(s/η) := by
        exact add_le_add
          (add_le_add (add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hpa (mul_nonneg hKr (add_nonneg her hq0))) hg)
            le_rfl) (le_abs_self ef)) hδS
      _ = _ := by ring
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  calc
    T*x ≤ r*(T*(Kr*(er+q)*pa+g+Kc/T*s*(ec+q))+ef+δ*(T/j)*Sj) := hx
    _ ≤ r*V := mul_le_mul_of_nonneg_left hraw hr
    _ ≤ R*V := mul_le_mul_of_nonneg_right hrR hV
    _ ≤ _ := countingErrorProfile_bound hR hKr her (abs_nonneg _) (abs_nonneg _) hG hq hs

end JointDickman

end OAI
