import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.RealClip
import OAI.Geometry.WeakHessian.LocalBounds.BoundedMulLp

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile133
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

lemma clipSquare_lipschitz (n : ℕ) :
    LipschitzWith (2*n) (fun r : ℝ => (realClip n r)^2) := by
  have H := lipschitz_mul_bounded (realClip_lipschitz n) (realClip_lipschitz n)
    (realClip_abs_le n) (realClip_abs_le n)
  convert! H using 1
  · ext; simp; ring
  · funext r; ring

def clipSquareLp (n : ℕ) (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (clipSquare_lipschitz n).compLp (by simp [realClip_zero]) u

lemma clipSquareLp_ae (n : ℕ) (u : Lp ℝ 2 m) :
    clipSquareLp n u =ᵐ[m] fun x => (realClip n (u x))^2 :=
  (clipSquare_lipschitz n).coeFn_compLp (by simp [realClip_zero]) u

lemma clipSquareLp_eq_square {n : ℕ} {u : Lp ℝ 2 m}
    (hu : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) :
    clipSquareLp n u =ᵐ[m] fun x => (u x)^2 := by
  filter_upwards [clipSquareLp_ae n u,hu] with x hx hb
  rw [hx,realClip,min_eq_left (abs_le.mp hb).2,max_eq_right (abs_le.mp hb).1]

lemma continuous_clipSquareLp (n : ℕ) : Continuous (clipSquareLp (m := m) n) :=
  (clipSquare_lipschitz n).lipschitzWith_compLp (by simp [realClip_zero]) |>.continuous

lemma hasDerivAt_integral_square_mul {u v : ℝ → Lp ℝ 2 m} {u' v' : Lp ℝ 2 m}
    {a : ℝ} (hu : HasDerivAt u u' a) (hv : HasDerivAt v v' a)
    (n : ℕ) (hub : ∀ᶠ t in 𝓝 a,∀ᵐ x ∂m,|u t x| ≤ (n:ℝ))
    {B : ℝ} (hvb : ∀ᵐ x ∂m,|v a x| ≤ B) :
    HasDerivAt (fun t => ∫ x,(u t x)^2*v t x ∂m)
      (2*(∫ x,u a x*u' x*v a x ∂m)+(∫ x,(u a x)^2*v' x ∂m)) a := by
  let M := boundedMulLp (Lp.aestronglyMeasurable (v a)) hvb
  let q := fun t => clipSquareLp n (u t)
  have hq : ContinuousAt q a := (continuous_clipSquareLp n).continuousAt.comp hu.continuousAt
  have hd1 := hu.inner ℝ (M.hasFDerivAt.comp_hasDerivAt a hu)
  have hd2 : HasDerivAt (fun t => ⟪q t,v t-v a⟫_ℝ) ⟪q a,v'⟫_ℝ a := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have HH := (hq.tendsto.mono_left nhdsWithin_le_nhds).inner (𝕜 := ℝ) hv.tendsto_slope
    convert! HH using 1
    ext t
    simp only [slope_def_module, inner_sub_right, sub_self, sub_zero,
      real_inner_smul_right, smul_eq_mul]
  have hd := hd1.add hd2
  have huba := mem_of_mem_nhds hub
  have heq : (fun t => ∫ x,(u t x)^2*v t x ∂m) =ᶠ[𝓝 a]
      (fun t => ⟪u t,M (u t)⟫_ℝ+⟪q t,v t-v a⟫_ℝ) := by
    filter_upwards [hub] with t ht
    rw [L2.inner_def,L2.inner_def,← integral_add]
    · apply integral_congr_ae
      filter_upwards [boundedMulLp_ae (Lp.aestronglyMeasurable (v a)) hvb (u t),
        clipSquareLp_eq_square ht,Lp.coeFn_sub (v t) (v a)] with x hM hq hv
      simp only [RCLike.inner_apply,conj_trivial]
      dsimp only [M,q] at *
      rw [hM,hq,hv]
      simp only [Pi.sub_apply]
      ring
    · exact L2.integrable_inner (u t) (M (u t))
    · exact L2.integrable_inner (q t) (v t-v a)
  have hresult := hd.congr_of_eventuallyEq heq
  convert! hresult using 1
  rw [L2.inner_def,L2.inner_def,L2.inner_def]
  have h1 : (∫ x,⟪u' x,M (u a) x⟫_ℝ ∂m) = ∫ x,u a x*u' x*v a x ∂m := by
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae (Lp.aestronglyMeasurable (v a)) hvb (u a)] with x hx
    simp only [RCLike.inner_apply,conj_trivial]
    dsimp only [M] at *
    rw [hx]; ring
  have h2 : (∫ x,⟪u a x,M u' x⟫_ℝ ∂m) = ∫ x,u a x*u' x*v a x ∂m := by
    apply integral_congr_ae
    filter_upwards [boundedMulLp_ae (Lp.aestronglyMeasurable (v a)) hvb u'] with x hx
    simp only [RCLike.inner_apply,conj_trivial]
    dsimp only [M] at *
    rw [hx]; ring
  have h3 : (∫ x,⟪q a x,v' x⟫_ℝ ∂m) = ∫ x,(u a x)^2*v' x ∂m := by
    apply integral_congr_ae
    filter_upwards [clipSquareLp_eq_square huba] with x hx
    simp only [RCLike.inner_apply,conj_trivial]
    dsimp only [q] at *
    rw [hx]; ring
  dsimp only [Function.comp_def]
  rw [h1,h2,h3]
  ring
end WeakHessian

end
end InlinedFile133

end OAI
