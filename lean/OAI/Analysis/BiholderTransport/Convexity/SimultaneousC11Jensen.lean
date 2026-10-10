import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Taylor
import OAI.Analysis.BiholderTransport.Convexity.JensenMaximum
import OAI.Analysis.BiholderTransport.Volume.JensenNullPullback
import OAI.Analysis.BiholderTransport.Convexity.ModifiedEnvelopeRegularity

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma simultaneous_C11_jensen {f k : E → ℝ} {Y Z : E → E}
    {S : Set E} (hS : IsOpen S) {x0 : E} {r eta : ℝ}
    (hr : 0<r) (heta : 0<eta) (hsub : closedBall x0 r⊆S)
    (hf : ∀ x∈S,DifferentiableAt ℝ f x)
    (hk : ∀ x∈S,DifferentiableAt ℝ k x)
    {Lf Lk LY LZ : ℝ≥0}
    (hfl : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hkl : LipschitzOnWith Lk (fderiv ℝ k) S)
    (hY : LipschitzOnWith LY Y S) (hZ : LipschitzOnWith LZ Z S)
    (hmax : ∀ x∈closedBall x0 r,f x+k x≤f x0+k x0)
    {N : Set E} (hN : μ N=0) {P : E → Prop}
    (hP : ∀ᵐ z ∂μ,z∈S → P z) :
    ∃ z∈ball x0 r,P z ∧
      HasFDerivAt Y (fderiv ℝ Y z) z ∧ HasFDerivAt Z (fderiv ℝ Z z) z ∧
      ((fderiv ℝ Y z).det≠0 → Y z∉N) ∧
      HasSecondTaylor (fun h => f (z+h)) (fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) z) ∧
      HasSecondTaylor (fun h => k (z+h)) (fderiv ℝ k z) (fderiv ℝ (fderiv ℝ k) z) ∧
      ‖fderiv ℝ f z+fderiv ℝ k z‖≤2*eta*r ∧
      ∀ e:E,fderiv ℝ (fderiv ℝ f) z e e+fderiv ℝ (fderiv ℝ k) z e e≤eta*‖e‖^2 := by
  let g : E → E := fun x => (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ f x+fderiv ℝ k x)
  have hlip : LipschitzOnWith (Lf+Lk) g (closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist ((InnerProductSpace.toDual ℝ E).symm _)
      ((InnerProductSpace.toDual ℝ E).symm _)≤_
    rw [(InnerProductSpace.toDual ℝ E).symm.isometry.dist_eq]
    exact ((hfl.add hkl).mono hsub).dist_le_mul x hx y hy
  have hd : ∀ x∈ball x0 r,
      HasFDerivAt (fun x => f x+k x) ((innerSL ℝ) (g x)) x := by
    intro x hx
    have HH := (hf x (hsub (ball_subset_closedBall hx))).hasFDerivAt.add
      (hk x (hsub (ball_subset_closedBall hx))).hasFDerivAt
    have hg : (innerSL ℝ) (g x)=fderiv ℝ f x+fderiv ℝ k x :=
      (InnerProductSpace.toDual ℝ E).apply_symm_apply _
    rwa [hg]
  have hc : ContinuousOn (fun x => f x+k x) (closedBall x0 r) :=
    fun x hx => ((hf x (hsub hx)).continuousAt.add (hk x (hsub hx)).continuousAt).continuousWithinAt
  have H : ∀ᵐ z ∂μ,z∈ball x0 r → P z ∧
      HasFDerivAt Y (fderiv ℝ Y z) z ∧ HasFDerivAt Z (fderiv ℝ Z z) z ∧
      ((fderiv ℝ Y z).det≠0 → Y z∉N) ∧
      HasSecondTaylor (fun h => f (z+h)) (fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) z) ∧
      HasSecondTaylor (fun h => k (z+h)) (fderiv ℝ k z) (fderiv ℝ (fderiv ℝ k) z) := by
    filter_upwards [hP,ae_secondTaylor_of_C11 μ hS hf hfl,
      ae_secondTaylor_of_C11 μ hS hk hkl,
      hY.ae_differentiableWithinAt_of_mem (μ := μ),
      hZ.ae_differentiableWithinAt_of_mem (μ := μ),
      ae_nonsingular_map_avoids_null (D := fderiv ℝ Y) μ hN]
      with z hzP hzf hzk hzY hzZ hzN hzb
    have hzS := hsub (ball_subset_closedBall hzb)
    have hyD := ((hzY hzS).differentiableAt (hS.mem_nhds hzS)).hasFDerivAt
    exact ⟨hzP hzS,hyD,((hzZ hzS).differentiableAt (hS.mem_nhds hzS)).hasFDerivAt,
      hzN hyD,(hzf hzS).2,(hzk hzS).2⟩
  obtain ⟨z,hz,hby,hgz,hu⟩ := jensen_C11_select hr heta hc hmax hd hlip μ H
  obtain ⟨hzP,hzY,hzZ,hzN,hzf,hzk⟩ := hby hz
  refine ⟨z,hz,hzP,hzY,hzZ,hzN,hzf,hzk,?_,?_⟩
  · simpa only [g,(InnerProductSpace.toDual ℝ E).symm.norm_map] using hgz
  · have hA := (hzf.add hzk).hasQuadraticExpansion
    have hzn : ‖z-x0‖<r := by simpa only [mem_ball,dist_eq_norm] using hz
    have HA := hA.hessian_le_of_upper_support (sub_pos.mpr hzn) (by
      intro h hh
      have hdist : z+h∈closedBall x0 r := by
        rw [mem_closedBall,dist_eq_norm]
        have heq : z+h-x0=(z-x0)+h := by abel
        rw [heq]
        exact (norm_add_le _ _).trans (by linarith)
      simpa only [add_zero,add_sub_cancel_left,g] using hu (z+h) hdist)
    simpa only [bilinearOperator_inner,add_apply] using HA

lemma simultaneous_C11_jensen_near {f k : E → ℝ} {Y Z : E → E}
    {S : Set E} (hS : IsOpen S) {x0 : E} (hx : x0∈S)
    (hf : ∀ x∈S,DifferentiableAt ℝ f x)
    (hk : ∀ x∈S,DifferentiableAt ℝ k x)
    {Lf Lk LY LZ : ℝ≥0}
    (hfl : LipschitzOnWith Lf (fderiv ℝ f) S)
    (hkl : LipschitzOnWith Lk (fderiv ℝ k) S)
    (hY : LipschitzOnWith LY Y S) (hZ : LipschitzOnWith LZ Z S)
    (hmax : ∀ᶠ x in 𝓝 x0,f x+k x≤f x0+k x0)
    {N : Set E} (hN : μ N=0) {P : E → Prop}
    (hP : ∀ᵐ z ∂μ,z∈S → P z) {rho eta : ℝ} (hrho : 0<rho) (heta : 0<eta) :
    ∃ z∈ball x0 rho,P z ∧
      HasFDerivAt Y (fderiv ℝ Y z) z ∧ HasFDerivAt Z (fderiv ℝ Z z) z ∧
      ((fderiv ℝ Y z).det≠0 → Y z∉N) ∧
      HasSecondTaylor (fun h => f (z+h)) (fderiv ℝ f z) (fderiv ℝ (fderiv ℝ f) z) ∧
      HasSecondTaylor (fun h => k (z+h)) (fderiv ℝ k z) (fderiv ℝ (fderiv ℝ k) z) ∧
      ‖fderiv ℝ f z+fderiv ℝ k z‖≤eta ∧
      ∀ e:E,fderiv ℝ (fderiv ℝ f) z e e+fderiv ℝ (fderiv ℝ k) z e e≤eta*‖e‖^2 := by
  obtain ⟨R,hR,HR⟩ := Metric.eventually_nhds_iff.mp
    (hmax.and (hS.mem_nhds hx))
  let r := min (R/2) (min rho (1/2))
  have hr : 0<r := lt_min (by positivity) (lt_min hrho (by norm_num))
  have hrR : r<R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrrho : r≤rho := (min_le_right _ _).trans (min_le_left _ _)
  have hrhalf : r≤1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hlocal : ∀ z∈closedBall x0 r,f z+k z≤f x0+k x0 ∧ z∈S := by
    intro z hz
    exact HR (lt_of_le_of_lt (mem_closedBall.mp hz) hrR)
  obtain ⟨z,hz,hp,hy,hzD,hn,htf,htk,hg,hh⟩ := simultaneous_C11_jensen μ hS
    hr heta (fun z hz => (hlocal z hz).2) hf hk hfl hkl hY hZ
    (fun z hz => (hlocal z hz).1) hN hP
  refine ⟨z,ball_subset_ball hrrho hz,hp,hy,hzD,hn,htf,htk,hg.trans ?_,hh⟩
  nlinarith

end WeakMTWTransport

end

end OAI
