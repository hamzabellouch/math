import Mathlib
import OAI.Probability.SKGap.Stability.TapFieldE
import OAI.Probability.SKGap.Localization.SmoothSelection

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static Matrix
variable {n : ℕ}

lemma primary_onsager_tap (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    SKGap.onsager j (fld j J h k x)=j*onsager j J h (k+1) x := by
  have hnR : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  simp only [SKGap.onsager,SKGap.overlap,SKGap.magnetization,onsager,siteMean,mag_succ,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,sub_div,div_self hnR]

lemma primary_tap_residual (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    SKGap.tapField j J h (fld j J h (k+1) x)=
      J.mulVec (Primary.residual j J h (k+1) x)-
      (fun i=>j*onsager j J h (k+1) x*(Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))+
      (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i) := by
  ext i
  simp only [SKGap.tapField,primary_onsager_tap hn,SKGap.magnetization,←mag_succ,
    Pi.add_apply,Pi.sub_apply,Matrix.mulVec,dotProduct]
  rw [fld_eq]
  simp only [Nat.add_sub_cancel,Primary.residual,mul_sub,Finset.sum_sub_distrib]
  ring

lemma onsager_residual_difference (hn : 0<n) (j : ℝ) (J : Interaction n)
    (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |onsager j J h (k+1) x-onsager j J h k x| *Real.sqrt (n:ℝ) ≤
      2*vectorNorm (Primary.residual j J h k x) := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hd : onsager j J h (k+1) x-onsager j J h k x=
      (∑i,Primary.residual j J h k x i*(mag j J h k x i+mag j J h (k+1) x i))/(n:ℝ) := by
    simp only [onsager,siteMean,←sub_div,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl; intro i _; dsimp [Primary.residual]; ring
  have hv : vectorNorm (fun i=>mag j J h k x i+mag j J h (k+1) x i)≤2*Real.sqrt (n:ℝ) := by
    exact (SKGap.vectorNorm_add_le _ _).trans
      ((add_le_add (mag_vectorNorm j J h k x) (mag_vectorNorm j J h (k+1) x)).trans_eq (by ring))
  have hp := (SKGap.vector_dot_abs_le (Primary.residual j J h k x)
    (fun i=>mag j J h k x i+mag j J h (k+1) x i)).trans
      (mul_le_mul_of_nonneg_left hv (vectorNorm_nonneg _))
  rw [hd,abs_div,abs_of_pos hnR]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  convert mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (n:ℝ)) using 1
  simp only [SKGap.vectorNorm,vectorNorm]
  ring_nf
  rw [Real.sq_sqrt hnR.le]

lemma primary_tap_norm (hn : 0<n) {j K : ℝ} (hj : 0≤j) (hK : 0≤K)
    (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v) :
    vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x)) ≤
      j*vectorNorm (Primary.residual j J h k x)+(K+3*j)*vectorNorm (Primary.residual j J h (k+1) x) := by
  have hb:=onsager_bounds j J h (k+1) x
  have hJ : SKGap.opNorm J≤K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro value
    exact hop (WithLp.ofLp value)
  have hterm : vectorNorm (fun i=>j*onsager j J h (k+1) x*
      (Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))≤
      j*(vectorNorm (Primary.residual j J h k x)+vectorNorm (Primary.residual j J h (k+1) x)) := by
    rw [show vectorNorm (fun i=>j*onsager j J h (k+1) x*
      (Primary.residual j J h k x i+Primary.residual j J h (k+1) x i))=
      |j*onsager j J h (k+1) x| *vectorNorm (Primary.residual j J h k x+Primary.residual j J h (k+1) x) from SKGap.vectorNorm_smul ..,
      abs_of_nonneg (mul_nonneg hj hb.1)]
    exact mul_le_mul (mul_le_of_le_one_right hj hb.2) (SKGap.vectorNorm_add_le _ _) (vectorNorm_nonneg _) hj
  have hlast : vectorNorm (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i)≤
      2*j*vectorNorm (Primary.residual j J h (k+1) x) := by
    rw [show vectorNorm (fun i=>j*(onsager j J h (k+2) x-onsager j J h (k+1) x)*mag j J h (k+2) x i)=
      |j*(onsager j J h (k+2) x-onsager j J h (k+1) x)| *vectorNorm (mag j J h (k+2) x) from SKGap.vectorNorm_smul ..,
      abs_mul,abs_of_nonneg hj]
    calc
      _ ≤ j*|onsager j J h (k+2) x-onsager j J h (k+1) x| *Real.sqrt (n:ℝ) :=
        mul_le_mul_of_nonneg_left (mag_vectorNorm j J h (k+2) x) (by positivity)
      _ ≤ j*(2*vectorNorm (Primary.residual j J h (k+1) x)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (onsager_residual_difference hn j J h (k+1) x) hj
      _ = _ := by ring
  rw [primary_tap_residual hn]
  exact (SKGap.vectorNorm_add_le _ _).trans ((add_le_add
    ((SKGap.vectorNorm_sub_le _ _).trans (add_le_add
      ((vectorNorm_matrix_mul _ _).trans (mul_le_mul_of_nonneg_right hJ (vectorNorm_nonneg _)))
      hterm)) hlast).trans_eq (by ring))

lemma magnetization_vector_lipschitz (y r : Fin n→ℝ) :
    vectorNorm (SKGap.magnetization y-SKGap.magnetization r)≤vectorNorm (y-r) := by
  apply (sq_le_sq₀ (vectorNorm_nonneg _) (vectorNorm_nonneg _)).mp
  simp only [vectorNorm_sq,Pi.sub_apply,SKGap.magnetization]
  exact Finset.sum_le_sum fun i _=>by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (tanh_lipschitz (r i) (y i)) 2

theorem selected_tap_root (hn : 0<n) {j K c r₀ ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hc : 0<c) (hr₀ : 0<r₀) (hρ : 0<ρ)
    (hbuffer : (K+4*j)*ρ<r₀)
    (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v)
    (hH : ∀y,vectorNorm (SKGap.tapField j J h y)≤r₀*Real.sqrt (n:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v) :
    ∃r : Fin n→ℝ,SKGap.tapField j J h r=0 ∧
      (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀k x,residualCutoff ρ j J h k x≠0→
        vectorNorm (mag j J h (k+2) x-SKGap.magnetization r)≤
        ((1+(K+3*j)/c)*(K+4*j))*ρ*Real.sqrt (n:ℝ) := by
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  obtain ⟨r,hr,hu,hd⟩:=SKGap.tap_root_and_distance hn hj hK hc (mul_pos hr₀ hs) hJ h hop hH
  refine ⟨r,hr,hu,fun k x hcut=>?_⟩
  obtain ⟨h0,h1⟩:=residualCutoff_support hn hρ J h k x hcut
  have hnorm : vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x))≤
      (K+4*j)*ρ*Real.sqrt (n:ℝ) := by
    exact (primary_tap_norm hn hj hK J h k x hop).trans
      ((add_le_add (mul_le_mul_of_nonneg_left h0 hj)
        (mul_le_mul_of_nonneg_left h1 (by positivity))).trans_eq (by ring))
  have hnear : vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x))<r₀*Real.sqrt (n:ℝ) :=
    hnorm.trans_lt (mul_lt_mul_of_pos_right hbuffer hs)
  have hh:=hd _ hnear
  have ht : SKGap.magnetization (fld j J h (k+1) x)=mag j J h (k+2) x := rfl
  calc
    _ = vectorNorm (SKGap.magnetization (fld j J h (k+1) x)-SKGap.magnetization r) := by rw [ht]
    _ ≤ vectorNorm (fld j J h (k+1) x-r) := magnetization_vector_lipschitz _ _
    _ ≤ (1+(K+3*j)/c)*vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x)) := hh
    _ ≤ (1+(K+3*j)/c)*((K+4*j)*ρ*Real.sqrt (n:ℝ)) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

end SKGapCutoff.Recipe

end
end

end OAI
