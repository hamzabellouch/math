import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.RadialOffException
import OAI.Combinatorics.RamseyFive.Geometry.DyadCount

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

lemma geometryScale_oriented_lower {q : ℕ} {σ n : ℝ}
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n) (hnhi : n≤10*Real.exp (5*σ/2)) :
    Real.exp (3*σ/2)/10≤geometryScale q n := by
  unfold geometryScale
  apply (le_div_iff₀ hn).mpr
  calc
    _ ≤ (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2)) :=
      mul_le_mul_of_nonneg_left hnhi (by positivity)
    _ = Real.exp (4*σ) := by
      rw [show (Real.exp (3*σ/2)/10)*(10*Real.exp (5*σ/2))=
        Real.exp (3*σ/2)*Real.exp (5*σ/2) by ring,←Real.exp_add]
      congr 1
      ring
    _ = (q:ℝ)^4 := by rw [hq,←Real.exp_nat_mul]; norm_num

lemma high_strong_scale {q : ℕ} {σ n P p : ℝ} (hσ : 20000000≤σ)
    (hq : (q:ℝ)=Real.exp σ) (hn : 0<n) (hnhi : n≤10*Real.exp (5*σ/2))
    (hP : P≤σ/10) (hp : 0<p) (hp2 : p^2≤Real.exp (P/10)) :
    2≤geometryScale q n*Real.exp (-P) ∧
    16*((q:ℝ)+1)≤(geometryScale q n*Real.exp (-P))*(1/(100*p))^2 := by
  have hσ0 : 0≤σ := by linarith
  have hBlo := geometryScale_oriented_lower hq hn hnhi
  have hB : Real.exp (3*σ/2-P)/10≤geometryScale q n*Real.exp (-P) := by
    calc
      _ = (Real.exp (3*σ/2)/10)*Real.exp (-P) := by rw [Real.exp_sub,Real.exp_neg]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBlo (Real.exp_nonneg _)
  have hlarge : (3200000:ℝ)≤Real.exp (σ/4) := by
    linarith [Real.add_one_le_exp (σ/4)]
  have hq1 : 1≤(q:ℝ) := by rw [hq]; exact Real.one_le_exp_iff.mpr hσ0
  constructor
  · apply le_trans _ hB
    have he := Real.add_one_le_exp (3*σ/2-P)
    linarith
  · rw [div_pow,one_pow,mul_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0<100*p))).mpr
    apply le_trans _ hB
    calc
      _ ≤ 320000*(q:ℝ)*p^2 := by nlinarith [sq_nonneg p]
      _ ≤ 320000*Real.exp σ*Real.exp (P/10) := by rw [hq]; gcongr
      _ = 320000*Real.exp (σ+P/10) := by simp only [Real.exp_add]; ring
      _ ≤ (Real.exp (σ/4)/10)*Real.exp (σ+P/10) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = Real.exp (σ/4+σ+P/10)/10 := by simp only [Real.exp_add]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

open Filter ParameterHierarchy
open scoped Topology

noncomputable def globalTruncConstant : ℝ := 4*2^(5000:ℕ)+32*333024*8^(4998:ℕ)

lemma globalTruncConstant_pos : 0<globalTruncConstant := by
  unfold globalTruncConstant
  exact add_pos (mul_pos (by norm_num) (pow_pos (by norm_num) _))
    (mul_pos (by norm_num) (pow_pos (by norm_num) _))

lemma global_radial_numeric {σ g N M A θ : ℝ} {m : ℕ}
    (hσ : 1≤σ) (_hN0 : 0≤N) (hM0 : 0≤M) (hA0 : 0≤A) (hθ0 : 0≤θ)
    (hN : N≤4*Real.exp (8*σ)) (hM : M≤8*Real.exp (-g))
    (hA : A≤333024*Real.exp (2*σ))
    (hθ : θ≤2*Real.exp (-(g+σ/2)/20)) (hm : (m:ℝ)≤Real.exp (3*σ)) :
    N*θ^5000+M^4998*(4*((Nat.clog 2 m:ℝ)+1)*A) ≤
      globalTruncConstant*Real.exp (8*σ-250*(g+σ/2))+
      globalTruncConstant*σ*Real.exp (2*σ-4998*g) := by
  have hc1 : 4*(2:ℝ)^5000≤globalTruncConstant := by
    exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hc2 : 32*333024*(8:ℝ)^4998≤globalTruncConstant := by
    exact le_add_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hdy := dyad_count_le hσ hm
  apply add_le_add
  · calc
      _ ≤ (4*Real.exp (8*σ))*(2*Real.exp (-(g+σ/2)/20))^5000 :=
        mul_le_mul hN (pow_le_pow_left₀ hθ0 hθ _) (pow_nonneg hθ0 _) (by positivity)
      _ = (4*2^(5000:ℕ))*Real.exp (8*σ-250*(g+σ/2)) := by
        rw [mul_pow,←Real.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show 4*Real.exp (8*σ)*(2^(5000:ℕ)*Real.exp (5000*(-(g+σ/2)/20))) =
          (4*2^(5000:ℕ))*(Real.exp (8*σ)*Real.exp (5000*(-(g+σ/2)/20))) by ac_rfl]
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc1 (Real.exp_nonneg _)
  · calc
      _ ≤ (8*Real.exp (-g))^4998*(4*(8*σ)*(333024*Real.exp (2*σ))) := by
        apply mul_le_mul (pow_le_pow_left₀ hM0 hM _) _ (by positivity) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hdy (by norm_num)) hA hA0 (by positivity)
      _ = (32*333024*8^(4998:ℕ))*σ*Real.exp (2*σ-4998*g) := by
        rw [mul_pow,←Real.exp_nat_mul]
        simp only [Nat.cast_ofNat]
        rw [show 8^(4998:ℕ)*Real.exp (4998*(-g))*(4*(8*σ)*(333024*Real.exp (2*σ))) =
          (32*333024*8^(4998:ℕ))*σ*(Real.exp (2*σ)*Real.exp (4998*(-g))) by
            rw [show (32:ℝ)=4*8 by norm_num]
            ac_rfl]
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (by linarith)) (Real.exp_nonneg _)

theorem eventually_global_radial_paid {η : ℝ} (hη : 0<η) (hη' : η<1/10) :
    ∀ᶠ σ : ℝ in atTop,∀ D R g N M A θ : ℝ,∀ m : ℕ,
      Range η σ D R → P η σ D R/10000≤g →
      0≤N → 0≤M → 0≤A → 0≤θ →
      N≤4*Real.exp (8*σ) → M≤8*Real.exp (-g) → A≤333024*Real.exp (2*σ) →
      θ≤2*Real.exp (-(g+σ/2)/20) → (m:ℝ)≤Real.exp (3*σ) →
      (P η σ D R)^5000*(N*θ^5000+M^4998*(4*((Nat.clog 2 m:ℝ)+1)*A))≤Real.exp (2*σ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_global_trunc_scalar hη hη' globalTruncConstant globalTruncConstant_pos] with σ hσ hs
  intro D R g N M A θ m hr hg hN0 hM0 hA0 hθ0 hN hM hA hθ hm
  have ht := global_radial_numeric hσ hN0 hM0 hA0 hθ0 hN hM hA hθ hm
  apply (mul_le_mul_of_nonneg_left ht (by positivity : 0≤(P η σ D R)^5000)).trans
  calc
    _ = globalTruncConstant*(P η σ D R)^5000*Real.exp (8*σ-250*(g+σ/2))+
        globalTruncConstant*(P η σ D R)^5000*σ*Real.exp (2*σ-4998*g) := by
      rw [mul_add]
      ac_rfl
    _ ≤ _ := hs D R g hr hg

end SharpRamseyFive.ScoreGeometry

end

end OAI
