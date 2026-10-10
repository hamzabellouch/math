import Mathlib
import OAI.Geometry.CubicTorus.Profiles.NodalTorusScalar

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_elliptic_weight_identity {A : Plane → Plane →L[ℝ] Plane}
    {f c : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hfc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) :
    (∫ y,sibling_planeElliptic A f y*(c y*f y))=
      -(∫ y,c y*⟪gradient f y,A y (gradient f y)⟫)+
        (1/2)*(∫ y,sibling_planeElliptic A c y*(f y)^2) := by
  have hp := plane_gradient_contDiff hf
  have hq := hA.clm_apply hp
  have hr := plane_gradient_contDiff hc
  have hpc := plane_gradient_compact hfc
  have hi : Integrable (fun y ↦ c y*⟪gradient f y,A y (gradient f y)⟫) :=
    (hc.continuous.mul (hp.continuous.inner hq.continuous)).integrable_of_hasCompactSupport
      (compact_inner_left hpc).mul_left
  have hj : Integrable (fun y ↦ f y*⟪gradient c y,A y (gradient f y)⟫) :=
    (hf.continuous.mul (hr.continuous.inner hq.continuous)).integrable_of_hasCompactSupport
      hfc.mul_right
  have he (y : Plane) : ⟪gradient (fun z ↦ c z*f z) y,A y (gradient f y)⟫=
      c y*⟪gradient f y,A y (gradient f y)⟫+
        f y*⟪gradient c y,A y (gradient f y)⟫ := by
    rw [plane_gradient_mul (hc.differentiable (by simp) y)
      (hf.differentiable (by simp) y),inner_add_left,real_inner_smul_left,real_inner_smul_left]
  have h1 := planeElliptic_ibp hA hf (hc.mul hf) hfc.mul_left
  simp_rw [he] at h1
  rw [integral_add hi hj] at h1
  have hf2 : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ (f y)^2) := hf.pow 2
  have he2 (y : Plane) : ⟪gradient (fun z ↦ (f z)^2) y,A y (gradient c y)⟫=
      2*(f y*⟪gradient c y,A y (gradient f y)⟫) := by
    simp only [pow_two]
    rw [plane_gradient_mul (hf.differentiable (by simp) y)
      (hf.differentiable (by simp) y),inner_add_left,real_inner_smul_left,
      hAs y (gradient f y) (gradient c y)]
    ring
  have h2 := planeElliptic_ibp hA hc hf2 (hfc.comp_left (g := fun r : ℝ ↦ r^2) (by simp))
  simp_rw [he2] at h2
  rw [integral_const_mul] at h2
  linarith

lemma plane_elliptic_transport_identity {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} {b : Plane → Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hfc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) :
    (∫ y,sibling_planeElliptic A f y*⟪b y,gradient f y⟫)=
      -(∫ y,⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫)+
      (1/2)*(∫ y,⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫)+
      (1/2)*(∫ y,planeDivergence b y*⟪gradient f y,A y (gradient f y)⟫) := by
  have hp := plane_gradient_contDiff hf
  have hq := hA.clm_apply hp
  have hpc := plane_gradient_compact hfc
  have hqc := compact_clm_apply hpc (A := A)
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdp : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (gradient f)) := hp.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  have hi : Integrable (fun y ↦ ⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫) :=
    (hp.continuous.inner (hdb.clm_apply hq).continuous).integrable_of_hasCompactSupport
      (compact_inner_left hpc)
  have hj : Integrable (fun y ↦ ⟪A y (gradient f y),fderiv ℝ (gradient f) y (b y)⟫) :=
    (hq.continuous.inner (hdp.clm_apply hb).continuous).integrable_of_hasCompactSupport
      (compact_inner_left hqc)
  have hk : Integrable (fun y ↦ ⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫) :=
    (hp.continuous.inner ((hdA.clm_apply hb).clm_apply hp).continuous).integrable_of_hasCompactSupport
      (compact_inner_left hpc)
  have h1 := planeElliptic_ibp hA hf (hb.inner ℝ hp) (compact_inner_right hpc)
  simp_rw [plane_transport_gradient hb hf] at h1
  rw [integral_add hi hj] at h1
  have he := plane_divergence_integration_by_parts (hb.of_le (by simp))
    ((hp.inner ℝ hq).of_le (by simp)) (compact_inner_left hpc)
  simp_rw [plane_energy_fderiv hA hf hAs] at he
  rw [integral_add (hj.const_mul 2) hk,integral_const_mul] at he
  linarith

theorem plane_rellich_identity {A : Plane → Plane →L[ℝ] Plane}
    {f : Plane → ℝ} {b : Plane → Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hfc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) :
    (∫ y,sibling_planeElliptic A f y*planeTransport b f y)=
      -2*(∫ y,⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫)+
      (∫ y,⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫)+
      (1/2)*(∫ y,sibling_planeElliptic A (planeDivergence b) y*(f y)^2) := by
  have hL := sibling_planeElliptic_contDiff hA hf
  have hi : Integrable (fun y ↦ sibling_planeElliptic A f y*⟪b y,gradient f y⟫) :=
    (hL.continuous.mul (hb.inner ℝ (plane_gradient_contDiff hf)).continuous).integrable_of_hasCompactSupport
      (compact_inner_right (plane_gradient_compact hfc)).mul_left
  have hj : Integrable (fun y ↦ sibling_planeElliptic A f y*(planeDivergence b y*f y)) :=
    (hL.continuous.mul ((sibling_planeDivergence_contDiff hb).mul hf).continuous).integrable_of_hasCompactSupport
      hfc.mul_left.mul_left
  have he (y : Plane) : sibling_planeElliptic A f y*planeTransport b f y=
      2*(sibling_planeElliptic A f y*⟪b y,gradient f y⟫)+
        sibling_planeElliptic A f y*(planeDivergence b y*f y) := by
    dsimp [planeTransport]; ring
  simp_rw [he]
  rw [integral_add (hi.const_mul 2) hj,integral_const_mul]
  rw [plane_elliptic_transport_identity hA hf hb hfc hAs,
    plane_elliptic_weight_identity hA hf (sibling_planeDivergence_contDiff hb) hfc hAs]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def sibling_planeCarlemanS (A : Plane → Plane →L[ℝ] Plane) (a : Plane → ℝ)
    (τ : ℝ) (f : Plane → ℝ) (y : Plane) : ℝ :=
  sibling_planeElliptic A f y+τ^2*a y*f y

def sibling_planeCarlemanP (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (a : Plane → ℝ) (τ : ℝ) (f : Plane → ℝ) (y : Plane) : ℝ :=
  sibling_planeCarlemanS A a τ f y-τ*planeTransport b f y

lemma planeCarlemanS_contDiff {A : Plane → Plane →L[ℝ] Plane} {a f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sibling_planeCarlemanS A a τ f) :=
  (sibling_planeElliptic_contDiff hA hf).add ((contDiff_const.mul ha).mul hf)

lemma planeCarlemanS_compact {A : Plane → Plane →L[ℝ] Plane} {a f : Plane → ℝ}
    (hc : HasCompactSupport f) (τ : ℝ) : HasCompactSupport (sibling_planeCarlemanS A a τ f) :=
  (sibling_planeElliptic_compact hc).add hc.mul_left

lemma sibling_planeCarlemanP_contDiff {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (sibling_planeCarlemanP A b a τ f) :=
  (planeCarlemanS_contDiff hA ha hf τ).sub (contDiff_const.mul (planeTransport_contDiff hb hf))

lemma sibling_planeCarlemanP_compact {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane} (hc : HasCompactSupport f) (τ : ℝ) :
    HasCompactSupport (sibling_planeCarlemanP A b a τ f) :=
  (planeCarlemanS_compact hc τ).sub (planeTransport_compact hc).mul_left

lemma plane_transport_weight_identity {a f : Plane → ℝ} {b : Plane → Plane}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : HasCompactSupport f) :
    (∫ y,a y*f y*planeTransport b f y)=
      -(∫ y,⟪gradient a y,b y⟫*(f y)^2) := by
  have hp := plane_gradient_contDiff hf
  have hq := plane_gradient_contDiff ha
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by simp)
  have hi : Integrable (fun y ↦ a y*f y*⟪b y,gradient f y⟫) :=
    ((ha.mul hf).continuous.mul (hb.inner ℝ hp).continuous).integrable_of_hasCompactSupport
      hc.mul_left.mul_right
  have hj : Integrable (fun y ↦ planeDivergence b y*(a y*(f y)^2)) :=
    ((sibling_planeDivergence_contDiff hb).continuous.mul (ha.mul (hf.pow 2)).continuous).integrable_of_hasCompactSupport
      hc2.mul_left.mul_left
  have hk : Integrable (fun y ↦ ⟪gradient a y,b y⟫*(f y)^2) :=
    ((hq.inner ℝ hb).continuous.mul (hf.pow 2).continuous).integrable_of_hasCompactSupport
      hc2.mul_left
  have htest := ha.mul (hf.pow 2)
  have heb (y : Plane) : fderiv ℝ (fun z ↦ a z*(f z)^2) y (b y)=
      2*(a y*f y*⟪b y,gradient f y⟫)+⟪gradient a y,b y⟫*(f y)^2 := by
    rw [← inner_gradient_left,plane_gradient_mul (ha.differentiable (by simp) y)
      ((hf.pow 2).differentiable (by simp) y)]
    simp only [pow_two]
    rw [plane_gradient_mul (hf.differentiable (by simp) y)
      (hf.differentiable (by simp) y)]
    simp only [inner_add_left,real_inner_smul_left]
    rw [real_inner_comm (gradient f y)]
    ring
  have he := plane_divergence_integration_by_parts (hb.of_le (by simp))
    (htest.of_le (by simp)) hc2.mul_left
  simp_rw [heb] at he
  rw [integral_add (hi.const_mul 2) hk, integral_const_mul] at he
  have he' (y : Plane) : a y*f y*planeTransport b f y=
      2*(a y*f y*⟪b y,gradient f y⟫)+planeDivergence b y*(a y*(f y)^2) := by
    dsimp [planeTransport]; ring
  simp_rw [he']
  rw [integral_add (hi.const_mul 2) hj,integral_const_mul]
  linarith

theorem plane_carleman_identity {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) :
    (∫ y,(sibling_planeCarlemanP A b a τ f y)^2)=
      (∫ y,(sibling_planeCarlemanS A a τ f y)^2)+τ^2*(∫ y,(planeTransport b f y)^2)+
      4*τ*(∫ y,⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫)-
      2*τ*(∫ y,⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫)-
      τ*(∫ y,sibling_planeElliptic A (planeDivergence b) y*(f y)^2)+
      2*τ^3*(∫ y,⟪gradient a y,b y⟫*(f y)^2) := by
  have hS := planeCarlemanS_contDiff hA ha hf τ
  have hT := planeTransport_contDiff hb hf
  have hL := sibling_planeElliptic_contDiff hA hf
  have hcS := planeCarlemanS_compact (A := A) (a := a) hc τ
  have hcT := planeTransport_compact (b := b) hc
  have hSS : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2) :=
    (hS.pow 2).continuous.integrable_of_hasCompactSupport
      (hcS.comp_left (g := fun t : ℝ ↦ t^2) (by simp))
  have hTT : Integrable (fun y ↦ (planeTransport b f y)^2) :=
    (hT.pow 2).continuous.integrable_of_hasCompactSupport
      (hcT.comp_left (g := fun t : ℝ ↦ t^2) (by simp))
  have hLT : Integrable (fun y ↦ sibling_planeElliptic A f y*planeTransport b f y) :=
    (hL.mul hT).continuous.integrable_of_hasCompactSupport hcT.mul_left
  have haT : Integrable (fun y ↦ a y*f y*planeTransport b f y) :=
    ((ha.mul hf).mul hT).continuous.integrable_of_hasCompactSupport hcT.mul_left
  have he (y : Plane) : (sibling_planeCarlemanP A b a τ f y)^2=
      (sibling_planeCarlemanS A a τ f y)^2+τ^2*(planeTransport b f y)^2-
      2*τ*(sibling_planeElliptic A f y*planeTransport b f y)-
      2*τ^3*(a y*f y*planeTransport b f y) := by
    dsimp [sibling_planeCarlemanP,sibling_planeCarlemanS]; ring
  simp_rw [he]
  have hi1 : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2+τ^2*(planeTransport b f y)^2) :=
    hSS.add (hTT.const_mul (τ^2))
  have hi2 : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2+τ^2*(planeTransport b f y)^2-
      2*τ*(sibling_planeElliptic A f y*planeTransport b f y)) := hi1.sub (hLT.const_mul (2*τ))
  rw [integral_sub hi2 (haT.const_mul (2*τ^3)),
    integral_sub hi1 (hLT.const_mul (2*τ)),
    integral_add hSS (hTT.const_mul (τ^2))]
  simp only [integral_const_mul]
  rw [plane_rellich_identity hA hf hb hc hAs,plane_transport_weight_identity ha hf hb hc]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_scaled_exp {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (t : ℝ) (y : Plane) :
    gradient (fun z ↦ Real.exp (t*φ z)) y=(t*Real.exp (t*φ y)) • gradient φ y := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left]
  rw [(((hφ.differentiable (by simp) y).hasFDerivAt.const_mul t).exp).fderiv]
  simp only [smul_apply,smul_eq_mul]
  ring

lemma planeElliptic_product {A : Plane → Plane →L[ℝ] Plane} {f g : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (y : Plane) : sibling_planeElliptic A (fun z ↦ f z*g z) y=
      f y*sibling_planeElliptic A g y+g y*sibling_planeElliptic A f y+
        2*⟪gradient f y,A y (gradient g y)⟫ := by
  have hp := hA.clm_apply (plane_gradient_contDiff hf)
  have hq := hA.clm_apply (plane_gradient_contDiff hg)
  have he : (fun z ↦ A z (gradient (fun x ↦ f x*g x) z))=
      (fun z ↦ f z • A z (gradient g z)+g z • A z (gradient f z)) := by
    funext z
    rw [plane_gradient_mul (hf.differentiable (by simp) z) (hg.differentiable (by simp) z),
      map_add,map_smul,map_smul]
  have hs1 : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ f z • A z (gradient g z)) := hf.smul hq
  have hs2 : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ g z • A z (gradient f z)) := hg.smul hp
  unfold sibling_planeElliptic
  rw [he,planeDivergence_add (hs1.differentiable (by simp) y)
    (hs2.differentiable (by simp) y),
    planeDivergence_smul (hf.differentiable (by simp) y) (hq.differentiable (by simp) y),
    planeDivergence_smul (hg.differentiable (by simp) y) (hp.differentiable (by simp) y),
    hAs y (gradient g y) (gradient f y)]
  ring

lemma planeElliptic_scaled_exp {A : Plane → Plane →L[ℝ] Plane} {φ : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (t : ℝ) (y : Plane) :
    sibling_planeElliptic A (fun z ↦ Real.exp (t*φ z)) y=
      Real.exp (t*φ y)*(t*sibling_planeElliptic A φ y+t^2*⟪gradient φ y,A y (gradient φ y)⟫) := by
  have hq := hA.clm_apply (plane_gradient_contDiff hφ)
  have hh : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ t*Real.exp (t*φ z)) :=
    contDiff_const.mul (contDiff_const.mul hφ).exp
  have he : (fun z ↦ A z (gradient (fun x ↦ Real.exp (t*φ x)) z))=
      (fun z ↦ (t*Real.exp (t*φ z)) • A z (gradient φ z)) := by
    funext z
    rw [plane_gradient_scaled_exp hφ,map_smul]
  unfold sibling_planeElliptic
  rw [he,planeDivergence_smul (hh.differentiable (by simp) y) (hq.differentiable (by simp) y)]
  have hg : gradient (fun z ↦ t*Real.exp (t*φ z)) y=
      (t^2*Real.exp (t*φ y)) • gradient φ y := by
    rw [plane_gradient_mul (differentiableAt_const _)
      (((contDiff_const.mul hφ).exp).differentiable (by simp) y),
      gradient_fun_const,smul_zero,add_zero,plane_gradient_scaled_exp hφ,smul_smul]
    congr 1
    ring
  rw [hg,real_inner_smul_left]
  ring

theorem plane_elliptic_conjugation {A : Plane → Plane →L[ℝ] Plane} {φ f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (τ : ℝ) (y : Plane) :
    sibling_planeCarlemanP A (fun z ↦ A z (gradient φ z))
      (fun z ↦ ⟪gradient φ z,A z (gradient φ z)⟫) τ f y=
      Real.exp (τ*φ y)*sibling_planeElliptic A (fun z ↦ Real.exp (-τ*φ z)*f z) y := by
  rw [planeElliptic_product hA ((contDiff_const.mul hφ).exp) hf hAs,
    planeElliptic_scaled_exp hA hφ,plane_gradient_scaled_exp hφ,real_inner_smul_left]
  have hcomm : ⟪gradient φ y,A y (gradient f y)⟫=⟪A y (gradient φ y),gradient f y⟫ := by
    rw [hAs,real_inner_comm]
  have he : Real.exp (τ*φ y)*Real.exp (-τ*φ y)=1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  rw [hcomm]
  dsimp [sibling_planeCarlemanP,sibling_planeCarlemanS,planeTransport,sibling_planeElliptic]
  linear_combination -(planeDivergence (fun z ↦ A z (gradient f z)) y+
    τ^2*⟪gradient φ y,A y (gradient φ y)⟫*f y-
    τ*(2*⟪A y (gradient φ y),gradient f y⟫+
      planeDivergence (fun z ↦ A z (gradient φ z)) y*f y))*he

theorem plane_elliptic_conjugation_forward {A : Plane → Plane →L[ℝ] Plane}
    {φ u : Plane → ℝ} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) (y : Plane) :
    sibling_planeCarlemanP A (fun z ↦ A z (gradient φ z))
      (fun z ↦ ⟪gradient φ z,A z (gradient φ z)⟫) τ
      (fun z ↦ Real.exp (τ*φ z)*u z) y=
      Real.exp (τ*φ y)*sibling_planeElliptic A u y := by
  rw [plane_elliptic_conjugation hA hφ ((contDiff_const.mul hφ).exp.mul hu) hAs]
  congr 2
  funext z
  rw [← mul_assoc,← Real.exp_add]
  have he : -τ*φ z+τ*φ z=0 := by ring
  rw [he,Real.exp_zero,one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeBentHessian (n : Plane) (ℓ M : ℝ) : Plane →L[ℝ] Plane :=
  ℓ • (innerSL ℝ n).smulRight n-M • ContinuousLinearMap.id ℝ Plane

lemma planeBentHessian_apply (n : Plane) (ℓ M : ℝ) (v : Plane) :
    planeBentHessian n ℓ M v=(ℓ*⟪n,v⟫) • n-M • v := by
  simp [planeBentHessian,smul_smul]

lemma planeBentHessian_symm (n : Plane) (ℓ M : ℝ) (v w : Plane) :
    ⟪v,planeBentHessian n ℓ M w⟫=⟪w,planeBentHessian n ℓ M v⟫ := by
  simp only [planeBentHessian_apply,inner_sub_right,real_inner_smul_right]
  rw [real_inner_comm v n,real_inner_comm w n,real_inner_comm v w]
  ring

lemma planeBentHessian_quadratic (n : Plane) (ℓ M : ℝ) (v : Plane) :
    ⟪v,planeBentHessian n ℓ M v⟫=ℓ*⟪n,v⟫^2-M*‖v‖^2 := by
  rw [planeBentHessian_apply,inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_comm v n,real_inner_self_eq_norm_sq]
  ring

def planeBentWeight (x n : Plane) (ℓ M : ℝ) (y : Plane) : ℝ :=
  -⟪n,y-x⟫+(1/2)*⟪y-x,planeBentHessian n ℓ M (y-x)⟫

lemma planeBentWeight_formula (x n : Plane) (ℓ M : ℝ) (y : Plane) :
    planeBentWeight x n ℓ M y= -⟪n,y-x⟫+(ℓ/2)*⟪n,y-x⟫^2-(M/2)*‖y-x‖^2 := by
  rw [planeBentWeight,planeBentHessian_quadratic]
  ring

lemma planeBentWeight_contDiff (x n : Plane) (ℓ M : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeBentWeight x n ℓ M) := by
  have hz : ContDiff ℝ (⊤ : ℕ∞) (fun y : Plane ↦ y-x) := contDiff_id.sub contDiff_const
  exact (contDiff_const.inner ℝ hz).neg.add
    (contDiff_const.mul (hz.inner ℝ ((planeBentHessian n ℓ M).contDiff.comp hz)))

lemma planeBentWeight_gradient (x n : Plane) (ℓ M : ℝ) (y : Plane) :
    gradient (planeBentWeight x n ℓ M) y= -n+planeBentHessian n ℓ M (y-x) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hz : HasFDerivAt (fun z : Plane ↦ z-x) (ContinuousLinearMap.id ℝ Plane) y :=
    (hasFDerivAt_id y).sub_const x
  have hlin := (hasFDerivAt_const n y).inner ℝ hz
  have hquad := hz.inner ℝ ((planeBentHessian n ℓ M).hasFDerivAt.comp y hz)
  have hh := (hlin.neg.add (hquad.const_mul (1/2))).fderiv
  change fderiv ℝ (planeBentWeight x n ℓ M) y=_ at hh
  rw [hh]
  simp only [add_apply,neg_apply,smul_apply,ContinuousLinearMap.comp_apply,fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply,zero_apply,ContinuousLinearMap.id_apply,
    inner_zero_left,add_zero,smul_eq_mul,inner_add_left,inner_neg_left,Function.comp_apply]
  rw [planeBentHessian_symm n ℓ M (y-x) v,
    real_inner_comm (planeBentHessian n ℓ M (y-x)) v]
  ring

lemma planeBentWeight_gradient_fderiv (x n : Plane) (ℓ M : ℝ) (y : Plane) :
    fderiv ℝ (gradient (planeBentWeight x n ℓ M)) y=planeBentHessian n ℓ M := by
  have he : gradient (planeBentWeight x n ℓ M)=
      (fun z ↦ -n+planeBentHessian n ℓ M (z-x)) := funext (planeBentWeight_gradient x n ℓ M)
  rw [he]
  have hz : HasFDerivAt (fun z : Plane ↦ z-x) (ContinuousLinearMap.id ℝ Plane) y :=
    (hasFDerivAt_id y).sub_const x
  have hcn : HasFDerivAt (fun _ : Plane ↦ -n) (0 : Plane →L[ℝ] Plane) y :=
    hasFDerivAt_const _ _
  have hh : HasFDerivAt (fun z : Plane ↦ -n+planeBentHessian n ℓ M (z-x))
      (0+(planeBentHessian n ℓ M).comp (ContinuousLinearMap.id ℝ Plane)) y :=
    hcn.add ((planeBentHessian n ℓ M).hasFDerivAt.comp y hz)
  simpa only [zero_add,ContinuousLinearMap.comp_id] using hh.fderiv

lemma planeBentWeight_gradient_center (x n : Plane) (ℓ M : ℝ) :
    gradient (planeBentWeight x n ℓ M) x= -n := by
  simp [planeBentWeight_gradient]

lemma planeBentWeight_center (x n : Plane) (ℓ M : ℝ) : planeBentWeight x n ℓ M x=0 := by
  simp [planeBentWeight]

lemma plane_inner_clm_abs (L : Plane →L[ℝ] Plane) (p : Plane) :
    |⟪p,L p⟫|≤‖L‖*‖p‖^2 := by
  have hh := mul_le_mul_of_nonneg_left (L.le_opNorm p) (norm_nonneg p)
  have hi := abs_real_inner_le_norm p (L p)
  nlinarith

lemma plane_quadratic_coercive_near {R : Plane → Plane →L[ℝ] Plane} {x : Plane}
    (hR : ContinuousAt R x) (h0 : ∀ p : Plane,‖p‖^2≤⟪p,R x p⟫) :
    ∀ᶠ y in 𝓝 x, ∀ p : Plane,0≤⟪p,R y p⟫ := by
  have he : ∀ᶠ y in 𝓝 x,‖R y-R x‖<1 := by
    have hh : ContinuousAt (fun y ↦ R y-R x) x := hR.sub continuousAt_const
    exact (hh.norm.eventually (gt_mem_nhds (show ‖R x-R x‖<1 by simp)))
  filter_upwards [he] with y hy p
  have hdiff := neg_le_of_abs_le (plane_inner_clm_abs (R y-R x) p)
  have hb := mul_le_mul_of_nonneg_right hy.le (sq_nonneg ‖p‖)
  simp only [sub_apply,inner_sub_right] at hdiff
  nlinarith [h0 p]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_bilinear_bound (D : Plane →L[ℝ] (Plane →L[ℝ] Plane))
    (u v w : Plane) : |⟪v,(D u) w⟫|≤‖v‖*(‖D‖*‖u‖*‖w‖) := by
  calc
    _≤‖v‖*‖(D u) w‖ := abs_real_inner_le_norm _ _
    _≤‖v‖*(‖D u‖*‖w‖) := mul_le_mul_of_nonneg_left ((D u).le_opNorm w) (norm_nonneg v)
    _≤_ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (D.le_opNorm u) (norm_nonneg w)) (norm_nonneg v)

lemma plane_weight_center_gradient_bound {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) (ℓ M : ℝ) (hℓ : 0≤ℓ) (hM : 0≤M) (p : Plane) :
    -(6*‖fderiv ℝ A x‖*‖A x‖+4*M*‖A x‖^2)*‖p‖^2≤
      4*⟪p,fderiv ℝ (fun y ↦ A y (gradient (planeBentWeight x n ℓ M) y)) x (A x p)⟫-
      2*⟪p,(fderiv ℝ A x (A x (gradient (planeBentWeight x n ℓ M) x))) p⟫ := by
  have hφ := planeBentWeight_contDiff x n ℓ M
  rw [plane_clm_fderiv (hA.differentiable (by simp) x)
    ((plane_gradient_contDiff hφ).differentiable (by simp) x),
    planeBentWeight_gradient_center,planeBentWeight_gradient_fderiv,inner_add_right]
  have hi := plane_inner_bilinear_bound (fderiv ℝ A x) (A x p) p (-n)
  simp only [norm_neg,hn,mul_one] at hi
  have hi' : |⟪p,(fderiv ℝ A x (A x p)) (-n)⟫|≤
      ‖fderiv ℝ A x‖*‖A x‖*‖p‖^2 := by
    calc
      _≤‖p‖*(‖fderiv ℝ A x‖*‖A x p‖) := hi
      _≤‖p‖*(‖fderiv ℝ A x‖*(‖A x‖*‖p‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((A x).le_opNorm p)
          (norm_nonneg (fderiv ℝ A x))) (norm_nonneg p)
      _=_ := by ring
  have hj := plane_inner_bilinear_bound (fderiv ℝ A x) (A x (-n)) p p
  have haN : ‖A x (-n)‖≤‖A x‖ := by simpa [hn] using (A x).le_opNorm (-n)
  have hj' : |⟪p,(fderiv ℝ A x (A x (-n))) p⟫|≤
      ‖fderiv ℝ A x‖*‖A x‖*‖p‖^2 := by
    calc
      _≤‖p‖*(‖fderiv ℝ A x‖*‖A x (-n)‖*‖p‖) := hj
      _≤‖p‖*(‖fderiv ℝ A x‖*‖A x‖*‖p‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haN (norm_nonneg (fderiv ℝ A x))) (norm_nonneg p)) (norm_nonneg p)
      _=_ := by ring
  have hsym : ⟪p,A x (planeBentHessian n ℓ M (A x p))⟫=
      ℓ*⟪n,A x p⟫^2-M*‖A x p‖^2 := by
    rw [hAs,real_inner_comm,planeBentHessian_quadratic]
  have hnorm : ‖A x p‖^2≤‖A x‖^2*‖p‖^2 := by
    calc
      _≤(‖A x‖*‖p‖)^2 := by gcongr; exact (A x).le_opNorm p
      _=_ := mul_pow _ _ _
  have hMnorm := mul_le_mul_of_nonneg_left hnorm hM
  rw [hsym]
  have hpos := mul_nonneg hℓ (sq_nonneg ⟪n,A x p⟫)
  have hi0 := neg_le_of_abs_le hi'
  have hj0 := le_of_abs_le hj'
  nlinarith

lemma plane_weight_center_mass {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (ℓ M : ℝ) :
    ⟪gradient (fun y ↦ ⟪gradient (planeBentWeight x n ℓ M) y,
        A y (gradient (planeBentWeight x n ℓ M) y)⟫) x,
      A x (gradient (planeBentWeight x n ℓ M) x)⟫=
      2*ℓ*⟪n,A x n⟫^2-2*M*‖A x n‖^2+
        ⟪-n,(fderiv ℝ A x (A x (-n))) (-n)⟫ := by
  rw [inner_gradient_left,plane_energy_fderiv hA (planeBentWeight_contDiff x n ℓ M) hAs,
    planeBentWeight_gradient_center,planeBentWeight_gradient_fderiv]
  rw [planeBentHessian_quadratic]
  simp only [map_neg,inner_neg_right,norm_neg,neg_sq]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_weight_positive_center {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) {m : ℝ} (hm : 0 < m)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ℓ k : ℝ,0 < ℓ ∧
      let φ := planeBentWeight x n ℓ M
      let b : Plane → Plane := fun y ↦ A y (gradient φ y)
      let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
      (∀ p : Plane,‖p‖^2 ≤ 4*⟪p,fderiv ℝ b x (A x p)⟫-
        2*⟪p,(fderiv ℝ A x (b x)) p⟫+k*⟪p,A x p⟫) ∧
      3 < 2*⟪gradient a x,b x⟫-k*a x := by
  let K : ℝ := 6*‖fderiv ℝ A x‖*‖A x‖+4*M*‖A x‖^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let k : ℝ := (K+1)/m
  have hk : 0 < k := div_pos (by linarith) hm
  have hkm : k*m=K+1 := by dsimp [k]; field_simp
  let a0 : ℝ := ⟪n,A x n⟫
  have ha0 : 0 < a0 := by
    have hh := hco n
    rw [hn,one_pow,mul_one] at hh
    exact lt_of_lt_of_le hm hh
  let D : ℝ := ⟪-n,(fderiv ℝ A x (A x (-n))) (-n)⟫
  let ℓ : ℝ := (4*M*‖A x n‖^2+2*|D|+k*a0+4)/(4*a0^2)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hℓeq : 4*ℓ*a0^2=4*M*‖A x n‖^2+2*|D|+k*a0+4 := by
    dsimp [ℓ]
    field_simp
  let φ := planeBentWeight x n ℓ M
  let b : Plane → Plane := fun y ↦ A y (gradient φ y)
  let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
  refine ⟨ℓ,k,hℓ,?_,?_⟩
  · intro p
    have hh := plane_weight_center_gradient_bound hA hAs x n hn ℓ M hℓ.le hM p
    change -K*‖p‖^2 ≤ 4*⟪p,fderiv ℝ b x (A x p)⟫-
      2*⟪p,(fderiv ℝ A x (b x)) p⟫ at hh
    have hhc := mul_le_mul_of_nonneg_left (hco p) hk.le
    have hprod : k*(m*‖p‖^2)=(K+1)*‖p‖^2 := by rw [← mul_assoc,hkm]
    rw [hprod] at hhc
    change ‖p‖^2 ≤ 4*⟪p,fderiv ℝ b x (A x p)⟫-
      2*⟪p,(fderiv ℝ A x (b x)) p⟫+k*⟪p,A x p⟫
    nlinarith only [hh,hhc]
  · have haeq : a x=a0 := by
      change ⟪gradient (planeBentWeight x n ℓ M) x,
        A x (gradient (planeBentWeight x n ℓ M) x)⟫=⟪n,A x n⟫
      rw [planeBentWeight_gradient_center]
      simp only [map_neg,inner_neg_left,inner_neg_right,neg_neg]
    have hh := plane_weight_center_mass hA hAs x n ℓ M
    change ⟪gradient a x,b x⟫=2*ℓ*a0^2-2*M*‖A x n‖^2+D at hh
    change 3 < 2*⟪gradient a x,b x⟫-k*a x
    rw [haeq]
    have hD : -|D| ≤ D := neg_abs_le D
    nlinarith only [hh,hD,hℓeq]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_local_carleman_weight {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) {m : ℝ} (hm : 0 < m)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ℓ : ℝ,0 < ℓ ∧ ∃ k C r : ℝ,0 ≤ C ∧ 0 < r ∧
      let φ := planeBentWeight x n ℓ M
      let b : Plane → Plane := fun y ↦ A y (gradient φ y)
      let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
      (∀ y∈Metric.ball x r,∀ p : Plane,-k*⟪p,A y p⟫ ≤
        4*⟪p,fderiv ℝ b y (A y p)⟫-2*⟪p,(fderiv ℝ A y (b y)) p⟫) ∧
      (∀ y∈Metric.ball x r,2 ≤ 2*⟪gradient a y,b y⟫-k*a y) ∧
      (∀ y∈Metric.ball x r,sibling_planeElliptic A (planeDivergence b) y ≤ C) := by
  obtain ⟨ℓ,k,hℓ,hcenter,hmass0⟩ :=
    plane_weight_positive_center hA hAs x n hn hm hco M hM
  let φ := planeBentWeight x n ℓ M
  let b : Plane → Plane := fun y ↦ A y (gradient φ y)
  let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := planeBentWeight_contDiff x n ℓ M
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := (plane_gradient_contDiff hφ).inner ℝ hb
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  let R : Plane → Plane →L[ℝ] Plane := fun y ↦
    (4 : ℝ) • ((fderiv ℝ b y).comp (A y))-(2 : ℝ) • (fderiv ℝ A y (b y))+k • A y
  have hcomp : Continuous (fun y : Plane ↦ (fderiv ℝ b y).comp (A y)) :=
    hdb.continuous.clm_comp hA.continuous
  have happ : Continuous (fun y : Plane ↦ fderiv ℝ A y (b y)) :=
    hdA.continuous.clm_apply hb.continuous
  have hs4 : Continuous (fun y : Plane ↦ (4 : ℝ) • ((fderiv ℝ b y).comp (A y))) :=
    hcomp.const_smul (4 : ℝ)
  have hs2 : Continuous (fun y : Plane ↦ (2 : ℝ) • fderiv ℝ A y (b y)) :=
    happ.const_smul (2 : ℝ)
  have hsk : Continuous (fun y : Plane ↦ k • A y) := hA.continuous.const_smul k
  have hR : Continuous R := (hs4.sub hs2).add hsk
  have hReq (y p : Plane) : ⟪p,R y p⟫=
      4*⟪p,fderiv ℝ b y (A y p)⟫-2*⟪p,(fderiv ℝ A y (b y)) p⟫+k*⟪p,A y p⟫ := by
    simp [R,inner_add_right,inner_sub_right,real_inner_smul_right]
  have hR0 (p : Plane) : ‖p‖^2 ≤ ⟪p,R x p⟫ := by
    rw [hReq]
    exact hcenter p
  have hRnear := plane_quadratic_coercive_near hR.continuousAt hR0
  have hmasscont : Continuous (fun y ↦ 2*⟪gradient a y,b y⟫-k*a y) :=
    (continuous_const.mul ((plane_gradient_contDiff ha).continuous.inner hb.continuous)).sub
      (continuous_const.mul ha.continuous)
  have hmassnear : ∀ᶠ y in 𝓝 x,2 ≤ 2*⟪gradient a y,b y⟫-k*a y :=
    (hmasscont.continuousAt.eventually (lt_mem_nhds (by linarith :
      2 < 2*⟪gradient a x,b x⟫-k*a x))).mono (fun _ hh ↦ hh.le)
  let c := sibling_planeElliptic A (planeDivergence b)
  have hc : Continuous c := (sibling_planeElliptic_contDiff hA (sibling_planeDivergence_contDiff hb)).continuous
  let C : ℝ := |c x|+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcnear : ∀ᶠ y in 𝓝 x,c y ≤ C :=
    (hc.continuousAt.eventually (gt_mem_nhds (by dsimp [C]; linarith [le_abs_self (c x)]))).mono
      (fun _ hh ↦ hh.le)
  have hall : ∀ᶠ y in 𝓝 x,
      (∀ p : Plane,0 ≤ ⟪p,R y p⟫) ∧ (2 ≤ 2*⟪gradient a y,b y⟫-k*a y) ∧ c y ≤ C := by
    filter_upwards [hRnear,hmassnear,hcnear] with y h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨r,hr,he⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ℓ,hℓ,k,C,r,hC,hr,?_,?_,?_⟩
  · intro y hy p
    have hh := (he (Metric.mem_ball.mp hy)).1 p
    rw [hReq] at hh
    linarith
  · intro y hy
    exact (he (Metric.mem_ball.mp hy)).2.1
  · intro y hy
    exact (he (Metric.mem_ball.mp hy)).2.2

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeCarlemanG (A : Plane → Plane →L[ℝ] Plane) (b : Plane → Plane)
    (f : Plane → ℝ) (y : Plane) : ℝ :=
  4*⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫-
  2*⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫

lemma planeCarlemanG_contDiff {A : Plane → Plane →L[ℝ] Plane}
    {b : Plane → Plane} {f : Plane → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (planeCarlemanG A b f) := by
  have hp := plane_gradient_contDiff hf
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  exact (contDiff_const.mul (hp.inner ℝ (hdb.clm_apply (hA.clm_apply hp)))).sub
    (contDiff_const.mul (hp.inner ℝ ((hdA.clm_apply hb).clm_apply hp)))

lemma planeCarlemanG_compact {A : Plane → Plane →L[ℝ] Plane}
    {b : Plane → Plane} {f : Plane → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (planeCarlemanG A b f) :=
  (compact_inner_left (plane_gradient_compact hc)).mul_left.sub
    (compact_inner_left (plane_gradient_compact hc)).mul_left

lemma plane_gradient_eq_zero_of_not_mem_tsupport {f : Plane → ℝ} {y : Plane}
    (hy : y∉tsupport f) : gradient f y=0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun hh ↦ hy (plane_gradient_support hh)

lemma plane_carleman_integrated_identity {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫) (τ : ℝ) :
    (∫ y,(sibling_planeCarlemanP A b a τ f y)^2)=
      (∫ y,(sibling_planeCarlemanS A a τ f y)^2)+τ^2*(∫ y,(planeTransport b f y)^2)+
      τ*(∫ y,planeCarlemanG A b f y)+
      τ*(∫ y,(2*τ^2*⟪gradient a y,b y⟫-sibling_planeElliptic A (planeDivergence b) y)*(f y)^2) := by
  have hp := plane_gradient_contDiff hf
  have hdb : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ b) := hb.fderiv_right (by simp)
  have hdA : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ A) := hA.fderiv_right (by simp)
  have hi : Integrable (fun y ↦ ⟪gradient f y,fderiv ℝ b y (A y (gradient f y))⟫) :=
    (hp.inner ℝ (hdb.clm_apply (hA.clm_apply hp))).continuous.integrable_of_hasCompactSupport
      (compact_inner_left (plane_gradient_compact hc))
  have hj : Integrable (fun y ↦ ⟪gradient f y,(fderiv ℝ A y (b y)) (gradient f y)⟫) :=
    (hp.inner ℝ ((hdA.clm_apply hb).clm_apply hp)).continuous.integrable_of_hasCompactSupport
      (compact_inner_left (plane_gradient_compact hc))
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by simp)
  have hk : Integrable (fun y ↦ sibling_planeElliptic A (planeDivergence b) y*(f y)^2) :=
    ((sibling_planeElliptic_contDiff hA (sibling_planeDivergence_contDiff hb)).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  have hl : Integrable (fun y ↦ ⟪gradient a y,b y⟫*(f y)^2) :=
    (((plane_gradient_contDiff ha).inner ℝ hb).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  rw [plane_carleman_identity hA ha hb hf hc hAs τ]
  simp only [planeCarlemanG,sub_mul,mul_assoc]
  rw [integral_sub (hi.const_mul 4) (hj.const_mul 2),integral_sub ((hl.const_mul (τ^2)).const_mul 2) hk]
  simp only [integral_const_mul]
  ring

theorem plane_carleman_estimate {A : Plane → Plane →L[ℝ] Plane}
    {a f : Plane → ℝ} {b : Plane → Plane} {U : Set Plane} {k C τ : ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (hs : tsupport f⊆U)
    (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (hg : ∀ y∈U, ∀ p : Plane, -k*⟪p,A y p⟫≤
      4*⟪p,fderiv ℝ b y (A y p)⟫-2*⟪p,(fderiv ℝ A y (b y)) p⟫)
    (hm : ∀ y∈U,2≤2*⟪gradient a y,b y⟫-k*a y)
    (hC : 0≤C) (hbound : ∀ y∈U,sibling_planeElliptic A (planeDivergence b) y≤C)
    (hτ : 1≤τ) (hbig : C+k^2≤τ) :
    τ^3*(∫ y,(f y)^2)≤∫ y,(sibling_planeCarlemanP A b a τ f y)^2 := by
  have ht : 0≤τ := le_trans (by norm_num) hτ
  have hp := plane_gradient_contDiff hf
  have hE := hp.inner ℝ (hA.clm_apply hp)
  have hiE : Integrable (fun y ↦ ⟪gradient f y,A y (gradient f y)⟫) :=
    hE.continuous.integrable_of_hasCompactSupport (compact_inner_left (plane_gradient_compact hc))
  have hiG : Integrable (planeCarlemanG A b f) := (planeCarlemanG_contDiff hA hb hf).continuous.integrable_of_hasCompactSupport
    (planeCarlemanG_compact (A := A) (b := b) hc)
  have hge : -k*(∫ y,⟪gradient f y,A y (gradient f y)⟫)≤∫ y,planeCarlemanG A b f y := by
    rw [← integral_const_mul]
    apply integral_mono (hiE.const_mul (-k)) hiG
    intro y
    by_cases hy : y∈tsupport f
    · exact hg y (hs hy) (gradient f y)
    · simp [planeCarlemanG,plane_gradient_eq_zero_of_not_mem_tsupport hy]
  have hc2 : HasCompactSupport (fun y ↦ (f y)^2) :=
    hc.comp_left (g := fun t : ℝ ↦ t^2) (by simp)
  have hiF : Integrable (fun y ↦ (f y)^2) := (hf.pow 2).continuous.integrable_of_hasCompactSupport hc2
  have hiAF : Integrable (fun y ↦ a y*(f y)^2) :=
    (ha.mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  have hS := planeCarlemanS_contDiff hA ha hf τ
  have hcS := planeCarlemanS_compact (A := A) (a := a) hc τ
  have hiSF : Integrable (fun y ↦ sibling_planeCarlemanS A a τ f y*f y) :=
    (hS.mul hf).continuous.integrable_of_hasCompactSupport hc.mul_left
  have hiSS : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2) :=
    (hS.pow 2).continuous.integrable_of_hasCompactSupport
      (hcS.comp_left (g := fun t : ℝ ↦ t^2) (by simp))
  have he : (∫ y,⟪gradient f y,A y (gradient f y)⟫)=
      -(∫ y,sibling_planeCarlemanS A a τ f y*f y)+τ^2*(∫ y,a y*(f y)^2) := by
    have hL := planeElliptic_ibp hA hf hf hc
    have hiL : Integrable (fun y ↦ sibling_planeElliptic A f y*f y) :=
      ((sibling_planeElliptic_contDiff hA hf).mul hf).continuous.integrable_of_hasCompactSupport hc.mul_left
    have hh (y : Plane) : sibling_planeCarlemanS A a τ f y*f y=
        sibling_planeElliptic A f y*f y+τ^2*(a y*(f y)^2) := by dsimp [sibling_planeCarlemanS]; ring
    simp_rw [hh]
    rw [integral_add hiL (hiAF.const_mul (τ^2)),integral_const_mul,hL]
    ring
  let M : Plane → ℝ := fun y ↦ (2*τ^2*⟪gradient a y,b y⟫-
    sibling_planeElliptic A (planeDivergence b) y)*(f y)^2
  have hiM : Integrable M :=
    (((contDiff_const.mul ((plane_gradient_contDiff ha).inner ℝ hb)).sub
      (sibling_planeElliptic_contDiff hA (sibling_planeDivergence_contDiff hb))).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hc2.mul_left
  have hme : (2*τ^2-C)*(∫ y,(f y)^2)+k*τ^2*(∫ y,a y*(f y)^2)≤∫ y,M y := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add (hiF.const_mul _) (hiAF.const_mul _)]
    apply integral_mono ((hiF.const_mul _).add (hiAF.const_mul _)) hiM
    intro y
    by_cases hy : y∈tsupport f
    · have hmy := mul_le_mul_of_nonneg_right (hm y (hs hy)) (sq_nonneg τ)
      have hby := hbound y (hs hy)
      have hcoeff : (2*τ^2-C)+k*τ^2*a y≤2*τ^2*⟪gradient a y,b y⟫-
          sibling_planeElliptic A (planeDivergence b) y := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (f y))
      dsimp [M]
      nlinarith
    · simp [M,image_eq_zero_of_notMem_tsupport hy]
  have hh : 0≤(∫ y,(sibling_planeCarlemanS A a τ f y)^2)+
      k*τ*(∫ y,sibling_planeCarlemanS A a τ f y*f y)+(k^2*τ^2/4)*(∫ y,(f y)^2) := by
    have hnon : 0≤∫ y,(sibling_planeCarlemanS A a τ f y+(k*τ/2)*f y)^2 := integral_nonneg (fun y ↦ sq_nonneg _)
    have hsplit (y : Plane) : (sibling_planeCarlemanS A a τ f y+(k*τ/2)*f y)^2=
        (sibling_planeCarlemanS A a τ f y)^2+k*τ*(sibling_planeCarlemanS A a τ f y*f y)+
        (k^2*τ^2/4)*(f y)^2 := by ring
    simp_rw [hsplit] at hnon
    have hisum : Integrable (fun y ↦ (sibling_planeCarlemanS A a τ f y)^2+
        k*τ*(sibling_planeCarlemanS A a τ f y*f y)) := hiSS.add (hiSF.const_mul (k*τ))
    rw [integral_add hisum (hiF.const_mul (k^2*τ^2/4)),
      integral_add hiSS (hiSF.const_mul (k*τ))] at hnon
    simpa only [integral_const_mul] using hnon
  have hF0 : 0≤∫ y,(f y)^2 := integral_nonneg (fun y ↦ sq_nonneg _)
  have hTT : 0≤τ^2*(∫ y,(planeTransport b f y)^2) :=
    mul_nonneg (sq_nonneg τ) (integral_nonneg (fun y ↦ sq_nonneg _))
  have hcoeff : C*τ+k^2*τ^2/4≤τ^3 := by
    have hh1 := mul_le_mul_of_nonneg_left hτ hC
    have hh2 := mul_le_mul_of_nonneg_right hbig ht
    have hh3 := mul_le_mul_of_nonneg_right hh2 ht
    have hh4 := mul_nonneg (sq_nonneg k) (sq_nonneg τ)
    nlinarith
  have hcf := mul_le_mul_of_nonneg_right hcoeff hF0
  have hgτ := mul_le_mul_of_nonneg_left hge ht
  have hmτ := mul_le_mul_of_nonneg_left hme ht
  rw [he] at hgτ
  rw [plane_carleman_integrated_identity hA ha hb hf hc hAs τ]
  change _≤_+_+τ*(∫ y,M y)
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem plane_weighted_carleman_near {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hAs : ∀ x v w,⟪v,A x w⟫=⟪w,A x v⟫)
    (x n : Plane) (hn : ‖n‖=1) {m : ℝ} (hm : 0 < m)
    (hco : ∀ p : Plane,m*‖p‖^2 ≤ ⟪p,A x p⟫) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ℓ : ℝ,0 < ℓ ∧ ∃ T r : ℝ,0 < r ∧
      ∀ (u : Plane → ℝ),ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      tsupport u⊆Metric.ball x r → ∀ τ : ℝ,T ≤ τ →
      τ^3*(∫ y,(Real.exp (τ*planeBentWeight x n ℓ M y)*u y)^2) ≤
        ∫ y,(Real.exp (τ*planeBentWeight x n ℓ M y)*sibling_planeElliptic A u y)^2 := by
  obtain ⟨ℓ,hℓ,k,C,r,hC,hr,hg,hmass,hbd⟩ :=
    plane_local_carleman_weight hA hAs x n hn hm hco M hM
  let φ := planeBentWeight x n ℓ M
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := planeBentWeight_contDiff x n ℓ M
  let b : Plane → Plane := fun y ↦ A y (gradient φ y)
  let a : Plane → ℝ := fun y ↦ ⟪gradient φ y,b y⟫
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := hA.clm_apply (plane_gradient_contDiff hφ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := (plane_gradient_contDiff hφ).inner ℝ hb
  refine ⟨ℓ,hℓ,max 1 (C+k^2),r,hr,?_⟩
  intro u hu hc hs τ hτ
  let f : Plane → ℝ := fun y ↦ Real.exp (τ*φ y)*u y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_const.mul hφ).exp.mul hu
  have hfc : HasCompactSupport f := hc.mul_left
  have hfs : tsupport f⊆Metric.ball x r := tsupport_mul_subset_right.trans hs
  have hh := plane_carleman_estimate hA ha hb hf hfc hfs hAs hg hmass hC hbd
    ((le_max_left _ _).trans hτ) ((le_max_right _ _).trans hτ)
  convert hh using 1
  apply integral_congr_ae
  filter_upwards [] with y
  rw [plane_elliptic_conjugation_forward hA hφ hu hAs]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
