import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.OuterVelocityFactorNonneg
import OAI.Analysis.BiholderTransport.CostGeometry.ExactTemplateCurvature
import OAI.Analysis.BiholderTransport.Calculus.ModifiedScalarDerivatives

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace WeakMTWTransport

lemma modifiedScalar_slope_bounds {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B)
    {C D b:ℝ} (hC:0 ≤ C) (hD:0 < D) (hb:0 ≤ b) (hbd:b/D*C ≤ 1/2)
    (hder:∀s,|deriv B s|≤C) (a s:ℝ) :
    (1:ℝ)/2 ≤ deriv (fun x=>modifiedScalar a D B (b,x)) s ∧
    deriv (fun x=>modifiedScalar a D B (b,x)) s ≤ 3/2 := by
  rw [modifiedScalar_deriv hB]
  have H:=abs_le.mp (hder ((s-a)/D))
  have p:=mul_le_mul_of_nonneg_left H.1 (div_nonneg hb hD.le)
  have q:=mul_le_mul H.2 le_rfl (div_nonneg hb hD.le) hC
  constructor <;> nlinarith only [p,q,hbd]

lemma modifiedScalar_strictMono {B:ℝ → ℝ} (hB:ContDiff ℝ ∞ B)
    {C D b:ℝ} (hC:0 ≤ C) (hD:0 < D) (hb:0 ≤ b) (hbd:b/D*C ≤ 1/2)
    (hder:∀s,|deriv B s|≤C) (a:ℝ) :
    StrictMono (fun x=>modifiedScalar a D B (b,x)) := by
  apply strictMono_of_deriv_pos
  intro s
  exact lt_of_lt_of_le (by norm_num) (modifiedScalar_slope_bounds hB hC hD hb hbd hder a s).1

lemma exact_center_slope_curvature {a D b s:ℝ} (hD:0 < D) (hb:0 < b)
    (hsmall:b/D*centerGamma ≤ 1) (hs:0 < centerTemplate ((s-a)/D)) :
    let l:=deriv (fun x=>modifiedScalar a D centerTemplate (b,x)) s
    let k:=iteratedDeriv 2 (fun x=>modifiedScalar a D centerTemplate (b,x)) s
    (1:ℝ)/2 ≤ l ∧ l<1 ∧ k<0 ∧
      -k/l^2 ≤ 2*centerGamma^2*b/D^2 ∧
      -k/l^2 ≤ 4*centerGamma*(1-l)/D := by
  dsimp only
  rw [modifiedScalar_deriv centerTemplate_smooth,modifiedScalar_second centerTemplate_smooth]
  let u:=deriv centerTemplate ((s-a)/D)
  let v:=iteratedDeriv 2 centerTemplate ((s-a)/D)
  have hu:=centerTemplate_deriv_neg ((s-a)/D)
  obtain ⟨hv,hv1,hv2⟩:=centerTemplate_curvature hs
  have hu2:=(centerTemplate_deriv_bound ((s-a)/D)).2
  have hp:0 < b/D:=div_pos hb hD
  have hp2:0 < b/D^2:=div_pos hb (sq_pos_of_pos hD)
  have hl:(1:ℝ)/2 ≤ 1+b/D*u:=by
    have H:=mul_le_mul_of_nonneg_left hu2 hp.le
    dsimp only [u]
    nlinarith only [H,hsmall]
  have hl2:1/4 ≤ (1+b/D*u)^2:=by nlinarith only [hl,sq_nonneg (1+b/D*u-1/2)]
  have hl0:0 < (1+b/D*u)^2:=lt_of_lt_of_le (by norm_num) hl2
  have hk0:0 ≤ -(b/D^2*v):=by dsimp [v]; exact neg_nonneg.mpr (mul_neg_of_pos_of_neg hp2 hv).le
  refine ⟨hl,?_,mul_neg_of_pos_of_neg hp2 hv,?_,?_⟩
  · have H:=mul_neg_of_pos_of_neg hp hu
    dsimp only [u] at hl ⊢
    linarith only [H]
  · apply (div_le_iff₀ hl0).mpr
    have H:=mul_le_mul_of_nonneg_left hv2 hp2.le
    have Q:=mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 2*centerGamma^2*b/D^2 by positivity)
    have he : 2*centerGamma^2*b/D^2*(1/4)=b/D^2*(centerGamma^2/2) := by ring
    rw [he] at Q
    dsimp only [u] at Q ⊢
    linarith only [H,Q]
  · apply (div_le_iff₀ hl0).mpr
    have H:=mul_le_mul_of_nonneg_left hv1 hp2.le
    have Q:=mul_le_mul_of_nonneg_left hl2
      (show 0 ≤ 4*centerGamma*(1-(1+b/D*u))/D by
        have ht:0 ≤ 1-(1+b/D*u):=by
          have H:=mul_neg_of_pos_of_neg hp hu
          dsimp only [u]
          linarith only [H]
        exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) centerGamma_pos.le) ht) hD.le)
    have he:4*centerGamma*(1-(1+b/D*u))/D*(1/4)=b/D^2*(centerGamma*(-u)):=by
      field_simp
      ring
    rw [he] at Q
    dsimp only [u] at Q ⊢
    linarith only [H,Q]

lemma exact_outer_slope_curvature {M K eta a D b s C:ℝ}
    (hM:2 ≤ M) (hK:1 ≤ K) (heta:0 < eta) (hD:0 < D) (hb:0 < b)
    (hC:0 ≤ C) (hder:∀t,|deriv (outerTemplate M K eta) t|≤C) (hsmall:b/D*C ≤ 1/2)
    (hs:-2*eta ≤ (s-a)/D) (hs':(s-a)/D ≤ 1-eta)
    (hcap:outerTemplate M K eta ((s-a)/D) ≤ M) :
    let l:=deriv (fun x=>modifiedScalar a D (outerTemplate M K eta) (b,x)) s
    let k:=iteratedDeriv 2 (fun x=>modifiedScalar a D (outerTemplate M K eta) (b,x)) s
    1 < l ∧ l ≤ 2 ∧ k < 0 ∧ K*b/(4*D^2) ≤ -k/l^2 := by
  dsimp only
  have hupper:=(modifiedScalar_slope_bounds (outerTemplate_smooth M K eta) hC hD hb.le hsmall hder a s).2
  rw [modifiedScalar_deriv (outerTemplate_smooth M K eta)] at hupper ⊢
  rw [modifiedScalar_second (outerTemplate_smooth M K eta)]
  obtain ⟨hd,hdd⟩:=exact_outer_curvature hK hM heta hs hs' hcap
  let l:=1+b/D*deriv (outerTemplate M K eta) ((s-a)/D)
  have hlo:1<l:=by
    have H:=mul_pos (div_pos hb hD) hd
    dsimp only [l]
    linarith only [H]
  have hl2:l ^ 2 ≤ 4:=by dsimp only [l]; nlinarith only [hupper,hlo]
  have hkk:iteratedDeriv 2 (outerTemplate M K eta) ((s-a)/D)<0:=by linarith only [hdd,hK]
  refine ⟨hlo,by linarith only [hupper],mul_neg_of_pos_of_neg (by positivity) hkk,?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos (zero_lt_one.trans hlo))).mpr
  have H:=mul_le_mul_of_nonneg_left hdd (show 0 ≤ b/D^2 by positivity)
  have Q:=mul_le_mul_of_nonneg_left hl2 (show 0 ≤ K*b/(4*D^2) by positivity)
  have he:(K*b/(4*D^2))*4=(b/D^2)*K:=by ring
  rw [he] at Q
  dsimp only [l] at Q
  nlinarith only [H,Q]

lemma scalar_determinant_gain {n:ℕ} {mu m K gamma b D cc co V W:ℝ}
    (hmu:0 < mu) (hm:mu ≤ m) (hK:0 < K) (hgamma:0 < gamma)
    (hb:0 < b) (hD:0 < D) (hV:0 ≤ V) (hW:0 ≤ W)
    (hc:cc ≤ 2*gamma^2*b/D^2) (ho:K*b/(4*D^2) ≤ co)
    (hdet:co*m^(n-1)*V ≤ cc*W) :
    (mu^(n-1)*K/(8*gamma^2))*V ≤ W := by
  have hp:=pow_le_pow_left₀ hmu.le hm (n-1)
  have hmul:mu^(n-1)*V ≤ m^(n-1)*V:=mul_le_mul_of_nonneg_right hp hV
  have h0:0 ≤ K*b/(4*D^2):=by positivity
  have h1:=mul_le_mul_of_nonneg_left hmul h0
  have h2:=mul_le_mul_of_nonneg_right ho (show 0 ≤ m^(n-1)*V from mul_nonneg (pow_nonneg (hmu.le.trans hm) _) hV)
  have h3:=mul_le_mul_of_nonneg_right hc hW
  have hh:K*b/(4*D^2)*(mu^(n-1)*V) ≤ (2*gamma^2*b/D^2)*W:=by
    calc
      _ ≤ K*b/(4*D^2)*(m^(n-1)*V) := h1
      _ ≤ co*(m^(n-1)*V) := h2
      _ = co*m^(n-1)*V := by ring
      _ ≤ cc*W := hdet
      _ ≤ _ := h3
  have he:K*b/(4*D^2)*(mu^(n-1)*V) = (2*gamma^2*b/D^2)*((mu^(n-1)*K/(8*gamma^2))*V):=by
    field_simp
    ring
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ (show 0 < 2*gamma^2*b/D^2 by positivity)).mp hh

end WeakMTWTransport

end

end OAI
