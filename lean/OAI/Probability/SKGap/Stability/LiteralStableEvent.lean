import Mathlib
import OAI.Probability.SKGap.Stability.StableRootInverse
import OAI.Probability.SKGap.Entropy.WeightedMean
import OAI.Probability.SKGap.Localization.PhiHessianBridge
import OAI.Probability.SKGap.Stability.LiteralStableControl

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap SKGap.Stein Primary SKGap.ImplicitSystem Matrix SKGap.ObservationBridge
variable {n : ℕ}

lemma phi_hessian_stable (hn : 0<n) {j A ε c r₀ R ρ : ℝ}
    (hρ : 0≤ρ) (_ : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hsmall : (3*Real.exp (R/2)+2)*ρ≤ε)
    (J : Interaction n) (h z r : Fin n→ℝ) (a : ℝ)
    (hbad : ¬rootBad j A ε c r₀ J h)
    (htap : vectorNorm (SKGap.tapField j J h z)≤r₀*Real.sqrt (n:ℝ))
    (ha : |a|≤R) (haρ : |a|≤ρ)
    (hz : vectorNorm (z-r)≤ρ*Real.sqrt (n:ℝ)) :
    ∀v : Euclid n,c*‖v‖^2≤ inner ℝ v
      (stableMatrix j ((∑i,scalarVariance (z i))/(n:ℝ)) (n:ℝ)⁻¹
        (phiSqrt z r a) (toEuclideanCLM (𝕜:=ℝ) J)
        (WithLp.toLp 2 (fun i=>Real.tanh (z i))) v) := by
  obtain ⟨hb,hvar,hrest⟩:=implicit_coefficient_bounds z r a hn hρ ha haρ hz
  have hdiag : (∑i,(phi (z i) (r i) a-SKGap.spinVariance z i)^2)≤ε^2*(n:ℝ) := by
    have hv : vectorNorm (fun i=>phi (z i) (r i) a-SKGap.spinVariance z i)≤ε*Real.sqrt (n:ℝ) := by
      apply (show vectorNorm (fun i=>phi (z i) (r i) a-SKGap.spinVariance z i)≤
          (3*Real.exp (R/2)+2)*ρ*Real.sqrt (n:ℝ) by
        change SKGapCutoff.Recipe.vectorNorm ((fun i=>phi (z i) (r i) a)-(fun i=>scalarVariance (z i))) ≤ _ at hvar
        exact hvar).trans
      exact mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg _)
    have hs:=pow_le_pow_left₀ (vectorNorm_nonneg _) hv 2
    simpa only [vectorNorm_sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hs
  have H:=stable_hessian_coercive hbad htap
    (fun i=>⟨(hb i).1.le,(hb i).2.trans hAR⟩) hdiag
  intro v
  rw [literal_stableMatrix_quadratic hn]
  have hvnorm : SKGap.vectorSqNorm v.ofLp=‖v‖^2 := by
    simpa only [SKGap.vectorNorm,WithLp.toLp_ofLp] using (SKGap.vectorNorm_sq v.ofLp).symm
  simpa only [hvnorm] using H v.ofLp

lemma literalStableAt_of_stableField (hn : 0<n) {j A ε c r₀ R ρ : ℝ}
    (hρ : 0≤ρ) (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hsmall : (3*Real.exp (R/2)+2)*ρ≤ε)
    (J : Interaction n) (h r : Fin n→ℝ) (z m : VectorFields n) (a : Spin n→ℝ)
    (x : Spin n) (hbad : ¬rootBad j A ε c r₀ J h)
    (htap : vectorNorm (SKGap.tapField j J h (z x))≤r₀*Real.sqrt (n:ℝ))
    (ha : |a x|≤R) (haρ : |a x|≤ρ)
    (hz : vectorNorm (z x-r)≤ρ*Real.sqrt (n:ℝ))
    (hm : vectorNorm (m x-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt (n:ℝ))
    (hmb : ∀i,|m x i|≤1) :
    LiteralStableAt J j z m a r R ρ c x :=
  ⟨ha,haρ,hz,hm,hmb,phi_hessian_stable hn hρ hε hAR hsmall J h (z x) r (a x)
    hbad htap ha haρ hz⟩

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix
namespace SKGapCutoff.Recipe
open SKGap Primary Static SKGap.ObservationBridge SKGap.Stein
variable {n : ℕ}

lemma square_average_difference (hn : 0<n) (v t : Fin n→ℝ)
    (hv : vectorNorm v≤Real.sqrt (n:ℝ)) (ht : vectorNorm t≤Real.sqrt (n:ℝ)) :
    |(∑i,(v i)^2)/(n:ℝ)-(∑i,(t i)^2)/(n:ℝ)| *Real.sqrt (n:ℝ)≤
      2*vectorNorm (v-t) := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : (∑i,(v i)^2)-(∑i,(t i)^2)=∑i,(v i-t i)*(v i+t i) := by
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl;intros;ring
  have hp:=(SKGap.vector_dot_abs_le (v-t) (v+t)).trans
    (mul_le_mul_of_nonneg_left ((SKGap.vectorNorm_add_le v t).trans
      ((add_le_add hv ht).trans_eq (show Real.sqrt (n:ℝ)+Real.sqrt (n:ℝ)=2*Real.sqrt (n:ℝ) by ring))) (vectorNorm_nonneg _))
  rw [←sub_div,hd,abs_div,abs_of_pos hnR,div_mul_eq_mul_div]
  apply (div_le_iff₀ hnR).mpr
  have H:=mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (n:ℝ))
  have he : (SKGap.vectorNorm (v-t)*(2*Real.sqrt (n:ℝ)))*Real.sqrt (n:ℝ)=2*SKGap.vectorNorm (v-t)*(n:ℝ) := by
    calc
      _ = 2*SKGap.vectorNorm (v-t)*(Real.sqrt (n:ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  simpa only [Pi.add_apply,Pi.sub_apply,SKGap.vectorNorm,vectorNorm] using H.trans_eq he

lemma primary_auxiliary_small (hn : 0<n) {j D ρ : ℝ} (hj : 0≤j)
    (J : Interaction n) (h r : Fin n→ℝ) (k : ℕ) (x : Spin n)
    (hnear : vectorNorm (mag j J h k x-SKGap.magnetization r)≤D*ρ*Real.sqrt (n:ℝ)) :
    |j*(1-onsager j J h k x-SKGap.overlap r)|≤2*j*D*ρ := by
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hv : vectorNorm (SKGap.magnetization r)≤Real.sqrt (n:ℝ) := by
    exact magnetization_norm r
  have havg : 1-onsager j J h k x-SKGap.overlap r=
      (∑i,(mag j J h k x i)^2)/(n:ℝ)-(∑i,(SKGap.magnetization r i)^2)/(n:ℝ) := by
    have hn0 : (n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
    simp only [Primary.onsager,siteMean,SKGap.overlap,Finset.sum_sub_distrib,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      sub_div,div_self hn0]
    ring
  have H:=(square_average_difference hn (mag j J h k x) (SKGap.magnetization r)
    (mag_vectorNorm j J h k x) hv).trans (mul_le_mul_of_nonneg_left hnear (by norm_num))
  rw [abs_mul,abs_of_nonneg hj,havg]
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    _ = j*(|((∑i,(mag j J h k x i)^2)/(n:ℝ))-(∑i,(SKGap.magnetization r i)^2)/(n:ℝ)| *Real.sqrt (n:ℝ)) := by ring
    _ ≤ j*(2*(D*ρ*Real.sqrt (n:ℝ))) := mul_le_mul_of_nonneg_left H hj
    _ = _ := by ring

theorem stable_primary_buffer (hn : 0<n) {j K A ε c r₀ R ρ : ℝ}
    (hj : 0≤j) (hK : 0≤K) (hA : 1≤A) (hc : 0<c) (hr₀ : 0<r₀) (hρ : 0≤ρ)
    (hε : 0≤ε) (hAR : Real.exp (R/2)≤A)
    (hbuffer : (K+4*j)*ρ<r₀)
    (hR : (1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ≤R)
    (hsmall : (3*Real.exp (R/2)+2)*((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ)≤ε)
    (J : Interaction n) (hJ : J.IsSymm) (h : Fin n→ℝ)
    (hop : ∀v,vectorNorm (J.mulVec v)≤K*vectorNorm v)
    (hbad : ¬rootBad j A ε c r₀ J h) :
    ∃r:Fin n→ℝ,SKGap.tapField j J h r=0 ∧ (∀y,SKGap.tapField j J h y=0→y=r) ∧
      ∀k x,
      vectorNorm (Primary.residual j J h k x)≤ρ*Real.sqrt (n:ℝ)→
      vectorNorm (Primary.residual j J h (k+1) x)≤ρ*Real.sqrt (n:ℝ)→
      LiteralStableAt J j (fld j J h (k+1)) (mag j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r R
        ((1+2*j)*(1+(1+(K+3*j)/c)*(K+4*j))*ρ) c x := by
  let C:=(1+(K+3*j)/c)*(K+4*j)
  let D:=(1+2*j)*(1+C)
  have hC : 0≤C:=by dsimp [C];positivity
  have hD : 0≤D:=by dsimp [D];positivity
  have hCD : C≤D:=by dsimp [D];nlinarith
  have h1CD : 1+C≤D:=by dsimp [D];nlinarith
  have h2CD : 2*j*(1+C)≤D:=by dsimp [D];nlinarith
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hH : ∀y,vectorNorm (SKGap.tapField j J h y)≤r₀*Real.sqrt (n:ℝ)→∀v,
      c*SKGap.vectorSqNorm v≤SKGap.quadraticForm (SKGap.fieldHessian j J y (SKGap.spinVariance y)) v := by
    intro y hy
    apply stable_hessian_coercive hbad hy
    · intro i
      exact ⟨(SKGap.spinVariance_pos y i).le,(SKGap.spinVariance_le_one y i).trans hA⟩
    · simp only [sub_self,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
      positivity
  obtain ⟨r,hr,hu,hd⟩:=SKGap.tap_root_and_distance hn hj hK hc (mul_pos hr₀ hs) hJ h hop hH
  refine ⟨r,hr,hu,?_⟩
  intro k x h0 h1
  have htap : vectorNorm (SKGap.tapField j J h (fld j J h (k+1) x))≤(K+4*j)*ρ*Real.sqrt (n:ℝ) :=
    (primary_tap_norm hn hj hK J h k x hop).trans
      ((add_le_add (mul_le_mul_of_nonneg_left h0 hj)
        (mul_le_mul_of_nonneg_left h1 (by positivity))).trans_eq (by ring))
  have htap' := htap.trans_lt (mul_lt_mul_of_pos_right hbuffer hs)
  have hz : vectorNorm (fld j J h (k+1) x-r)≤C*ρ*Real.sqrt (n:ℝ) :=
    (hd _ htap').trans ((mul_le_mul_of_nonneg_left htap (by positivity)).trans_eq (by dsimp [C];ring))
  have ht : vectorNorm (mag j J h (k+2) x-SKGap.magnetization r)≤C*ρ*Real.sqrt (n:ℝ) :=
    (magnetization_vector_lipschitz (fld j J h (k+1) x) r).trans hz
  have hm : vectorNorm (mag j J h (k+1) x-SKGap.magnetization r)≤(1+C)*ρ*Real.sqrt (n:ℝ) := by
    have he : mag j J h (k+1) x-SKGap.magnetization r=
        Primary.residual j J h (k+1) x+(mag j J h (k+2) x-SKGap.magnetization r) := by
      ext i;simp only [Primary.residual,Pi.sub_apply,Pi.add_apply];ring
    rw [he]
    exact (SKGap.vectorNorm_add_le _ _).trans ((add_le_add h1 ht).trans_eq (by ring))
  have ha := (primary_auxiliary_small hn hj J h r (k+1) x hm).trans
    (mul_le_mul_of_nonneg_right h2CD hρ)
  apply literalStableAt_of_stableField hn (mul_nonneg hD hρ) hε hAR hsmall J h r _ _ _ x hbad
    htap'.le (ha.trans hR) ha
  · exact hz.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD hρ) hs.le)
  · exact hm.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1CD hρ) hs.le)
  · intro i
    exact primaryState_mag_bounded j J h (k+1) x i

end SKGapCutoff.Recipe

end
end

end OAI
