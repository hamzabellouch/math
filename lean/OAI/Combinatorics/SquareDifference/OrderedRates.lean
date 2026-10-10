import OAI.Combinatorics.SquareDifference.OrderedGlobal

namespace OAI

section

open Finset Filter

open scoped Topology

namespace SquareDifference

lemma source_d_loss (d : ℕ) : (d:ℝ)*sourceLoss d≤ sourceGamma*sourceTau d/100 := by
  unfold sourceLoss
  have hd : 0<(d:ℝ)+1 := by positivity
  have hf : (d:ℝ)/((d:ℝ)+1)≤1 := (div_le_one hd).mpr (by linarith)
  calc
    _ = sourceGamma*sourceTau d/100*((d:ℝ)/((d:ℝ)+1)) := by field_simp
    _ ≤ _ := mul_le_of_le_one_right (by have := sourceGamma_pos; have := sourceTau_pos d; positivity) hf

lemma ordered_exponent_gaps (d : ℕ) :
    2*(d:ℝ)*sourceLoss d-sourceTau d/2≤ -sourceSigma d ∧
    (d:ℝ)*sourceLoss d-sourceGamma*sourceTau d/2≤ -sourceSigma d ∧
    (3*(d:ℝ)+2)*sourceTau d-sourceBeta/9≤ -sourceSigma d ∧
    3*(d:ℝ)*sourceTau d-sourceBeta/9+2*sourceLoss d≤ -sourceSigma d := by
  have hl := source_d_loss d
  have hd := source_d_tau d
  have ht := sourceTau_le d
  have hpos := (sourceTau_pos d).le
  have he : sourceLoss d≤ sourceGamma*sourceTau d/100 := by
    unfold sourceLoss
    apply div_le_div_of_nonneg_left (mul_nonneg sourceGamma_pos.le hpos) (by norm_num)
    have := Nat.cast_nonneg (α:=ℝ) d
    linarith
  unfold sourceSigma
  norm_num [sourceBeta,sourceGamma] at *
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma cutoff_pow_upper (N K d : ℕ) (t : ℝ) (hN : 0<N) (hK : (K:ℝ)≤(N:ℝ)^t) :
    (K:ℝ)^d≤(N:ℝ)^((d:ℝ)*t) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  calc
    _ ≤ ((N:ℝ)^t)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hK d
    _ = _ := by rw [←Real.rpow_mul_natCast hn.le]; congr 1; ring

lemma cutoff_negative_upper (N K : ℕ) (t b : ℝ) (hN : 0<N) (hb : b≤0)
    (hK : (N:ℝ)^t≤K) : (K:ℝ)^b≤(N:ℝ)^(t*b) := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  exact (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn _) hK hb).trans_eq (Real.rpow_mul hn.le _ _).symm

noncomputable def orderedError (d M N K H : ℕ) (C : ℝ) : ℝ :=
  (K:ℝ)⁻¹*(2*(C*(N:ℝ)^(sourceLoss d))^(2*d))+
    (d:ℝ)*(K:ℝ)^(-sourceGamma)*(C*(N:ℝ)^(sourceLoss d))^d+
    orderedLowError d M K H (C*(N:ℝ)^(sourceLoss d))

noncomputable def orderedErrorConstant (d M : ℕ) (C : ℝ) : ℝ :=
  2*C^(2*d)+(d:ℝ)*C^d+(M:ℝ)^(d+1)*kernelAbsoluteConstant+(M:ℝ)^d*C^2

lemma orderedError_bound (d M N K H : ℕ) (C : ℝ) (hC : 0≤C) (hN : 1≤N)
    (hKu : (K:ℝ)≤(N:ℝ)^(sourceTau d))
    (hKl : (N:ℝ)^(sourceTau d/2)≤K) (hHl : (N:ℝ)^(sourceBeta/3)≤H) :
    orderedError d M N K H C≤orderedErrorConstant d M C*(N:ℝ)^(-sourceSigma d) := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hg := ordered_exponent_gaps d
  have hk := cutoff_negative_upper N K (sourceTau d/2) (-1) (by omega) (by norm_num) hKl
  have hkg := cutoff_negative_upper N K (sourceTau d/2) (-sourceGamma) (by omega) (neg_nonpos.mpr sourceGamma_pos.le) hKl
  have hh := cutoff_negative_upper N H (sourceBeta/3) (-(1:ℝ)/3) (by omega) (by norm_num) hHl
  have hk3 := cutoff_pow_upper N K (3*d) (sourceTau d) (by omega) hKu
  have hk32 := cutoff_pow_upper N K (3*d+2) (sourceTau d) (by omega) hKu
  have hbad : (K:ℝ)⁻¹*(2*(C*(N:ℝ)^(sourceLoss d))^(2*d))≤
      2*C^(2*d)*(N:ℝ)^(-sourceSigma d) := by
    rw [Real.rpow_neg_one] at hk
    calc
      _ ≤ (N:ℝ)^((sourceTau d/2)*(-1))*(2*(C*(N:ℝ)^(sourceLoss d))^(2*d)) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ = 2*C^(2*d)*(N:ℝ)^(2*(d:ℝ)*sourceLoss d-sourceTau d/2) := by
        rw [mul_pow,←Real.rpow_mul_natCast hn.le]
        rw [show 2*(d:ℝ)*sourceLoss d-sourceTau d/2=(sourceTau d/2)*(-1)+sourceLoss d*(2*d:ℕ) by push_cast; ring,Real.rpow_add hn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.1) (by positivity)
  have htr : (d:ℝ)*(K:ℝ)^(-sourceGamma)*(C*(N:ℝ)^(sourceLoss d))^d≤
      (d:ℝ)*C^d*(N:ℝ)^(-sourceSigma d) := by
    calc
      _ ≤ (d:ℝ)*(N:ℝ)^((sourceTau d/2)*(-sourceGamma))*(C*(N:ℝ)^(sourceLoss d))^d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkg (Nat.cast_nonneg _)) (by positivity)
      _ = (d:ℝ)*C^d*(N:ℝ)^((d:ℝ)*sourceLoss d-sourceGamma*sourceTau d/2) := by
        rw [mul_pow,←Real.rpow_mul_natCast hn.le]
        rw [show (d:ℝ)*sourceLoss d-sourceGamma*sourceTau d/2=(sourceTau d/2)*(-sourceGamma)+sourceLoss d*d by ring,Real.rpow_add hn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.2.1) (by positivity)
  have hlo1 : (M:ℝ)^(d+1)*(K:ℝ)^(3*d+2)*(H:ℝ)^(-(1:ℝ)/3)*kernelAbsoluteConstant≤
      (M:ℝ)^(d+1)*kernelAbsoluteConstant*(N:ℝ)^(-sourceSigma d) := by
    calc
      _ ≤ (M:ℝ)^(d+1)*(N:ℝ)^((3*d+2:ℕ)*sourceTau d)*(N:ℝ)^((sourceBeta/3)*(-(1:ℝ)/3))*kernelAbsoluteConstant := by
        apply mul_le_mul_of_nonneg_right _ kernelAbsoluteConstant_nonneg
        exact mul_le_mul (mul_le_mul_of_nonneg_left hk32 (by positivity)) hh (by positivity) (by positivity)
      _ = (M:ℝ)^(d+1)*kernelAbsoluteConstant*(N:ℝ)^((3*(d:ℝ)+2)*sourceTau d-sourceBeta/9) := by
        rw [show (3*(d:ℝ)+2)*sourceTau d-sourceBeta/9=((3*d+2:ℕ):ℝ)*sourceTau d+(sourceBeta/3)*(-(1:ℝ)/3) by push_cast; ring,Real.rpow_add hn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.2.2.1)
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) kernelAbsoluteConstant_nonneg)
  have hlo2 : (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*(C*(N:ℝ)^(sourceLoss d))^2≤
      (M:ℝ)^d*C^2*(N:ℝ)^(-sourceSigma d) := by
    calc
      _ ≤ (M:ℝ)^d*(N:ℝ)^((3*d:ℕ)*sourceTau d)*(N:ℝ)^((sourceBeta/3)*(-(1:ℝ)/3))*(C*(N:ℝ)^(sourceLoss d))^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hk3 (by positivity)) hh (by positivity) (by positivity)
      _ = (M:ℝ)^d*C^2*(N:ℝ)^(3*(d:ℝ)*sourceTau d-sourceBeta/9+2*sourceLoss d) := by
        rw [mul_pow,←Real.rpow_mul_natCast hn.le]
        rw [show 3*(d:ℝ)*sourceTau d-sourceBeta/9+2*sourceLoss d=((3*d:ℕ):ℝ)*sourceTau d+(sourceBeta/3)*(-(1:ℝ)/3)+sourceLoss d*2 by push_cast; ring,
          Real.rpow_add hn,Real.rpow_add hn]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hg.2.2.2) (by positivity)
  unfold orderedError orderedErrorConstant orderedLowError
  have halg : (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*((K:ℝ)^2*M*kernelAbsoluteConstant+(C*(N:ℝ)^(sourceLoss d))^2)=
      (M:ℝ)^(d+1)*(K:ℝ)^(3*d+2)*(H:ℝ)^(-(1:ℝ)/3)*kernelAbsoluteConstant+
      (M:ℝ)^d*(K:ℝ)^(3*d)*(H:ℝ)^(-(1:ℝ)/3)*(C*(N:ℝ)^(sourceLoss d))^2 := by
    rw [pow_succ,pow_add]
    ring
  rw [halg]
  nlinarith

end SquareDifference

end

end OAI
