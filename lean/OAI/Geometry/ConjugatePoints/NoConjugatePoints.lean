import OAI.Geometry.ConjugatePoints.Passages

namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

lemma normalDensity_zero (P Q A B : TMat) (T : Vec) : normalDensity P Q A B T 0 0 = 0 := by
  simp [normalDensity, gamma, curvatureJet, gammaPrime, metric, pairing]

theorem truncated_return_nonnegative {right : Bool} {δ C b c : ℝ} {p : TVec}
    {t v : ℝ → ℝ} {V : ℝ → Vec} (hC : 18 ≤ C)
    (hδ : SmallParameter (3*C) (sourceMixed C) δ)
    (hbound : ∀ u ∈ Icc 0 1, ∀ q, sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧
      qform (coordinateCometric right δ u) q ≤ 18*sqnorm q)
    (hder : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ e) ≤ C^2*δ^2)
    (hconc : ∀ u ∈ Icc 0 1, ∀ q, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    (hdom : ∀ u ∈ Icc 0 1, sqnorm (deriv (coordinateCometric right δ) u *ᵥ p) ≤
      C*δ*qform (-deriv (deriv (coordinateCometric right δ)) u) p)
    (hc : c ∈ Ioo 0 b) (ht : ∀ s ∈ Icc 0 b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 b, HasDerivAt v (-force right δ p (t s)/2) s)
    (hta : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ t s)
    (hva : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ v s)
    (h0 : t 0 = 0) (hr : ∀ s ∈ Ioo 0 b, t s ∈ Ioo (0:ℝ) 1)
    (hvc : v c = 0) (hstar : 1/4 < t c)
    (henergy : ∀ s ∈ Icc 0 b, potential right δ p (t s) + v s^2 = 1)
    (hV : ∀ s ∈ Icc 0 b, ContDiffAt ℝ ∞ V s)
    (hcut : b < 2*c → V =ᶠ[𝓝 b] 0)
    (hfi : IntervalIntegrable (returnNormalDensity right δ p t v V (deriv V)) volume 0 b) :
    0 ≤ ∫ s in (0:ℝ)..b, returnNormalDensity right δ p t v V (deriv V) s := by
  have hb : 0 < b := hc.1.trans hc.2
  have hL : 0 < 2*c := by linarith [hc.1]
  have hd := reflected_closed_equations (force_smooth right δ p) hc ht hv hvc
  have hsmooth := reflected_closed_smooth (force_smooth right δ p) hc ht hv hvc hta hva
  have hcomplete := finite_turn_completion (force_smooth right δ p) hc ht hv hvc h0 hr
  simp only [sub_zero] at hd hsmooth hcomplete
  rcases hcomplete with ⟨hbL,het,hev,he0,heL,her⟩
  let te := reflectEven c t
  let ve := reflectOdd c v
  let W := if b < 2*c then cut b V else V
  have hWeq (s : ℝ) (hs : s ∈ Icc 0 b) : W s = V s := by
    dsimp only [W]
    split_ifs
    · exact cut_eq hs.2
    · rfl
  have hWdeq (s : ℝ) (hs : s ∈ Icc 0 b) : deriv W s = deriv V s := by
    dsimp only [W]
    split_ifs with hbl
    · exact cut_deriv (hcut hbl) hs.2
    · rfl
  have hWs (s : ℝ) (hs : s ∈ Icc 0 (2*c)) : ContDiffAt ℝ ∞ W s := by
    dsimp only [W]
    split_ifs with hbl
    · exact cut_smoothAt (hcut hbl) (fun hsb => hV s ⟨hs.1,hsb⟩)
    · exact hV s ⟨hs.1,hs.2.trans (le_of_not_gt hbl)⟩
  have hE (s : ℝ) (hs : s ∈ Icc 0 (2*c)) : potential right δ p (te s) + ve s^2 = 1 := by
    by_cases hsc : s ≤ c
    · simpa only [te,ve,reflectEven,reflectOdd,ite_eq_left hsc] using henergy s ⟨hs.1,hsc.trans hc.2.le⟩
    · have hh := henergy (2*c-s) ⟨by linarith [hs.2],by linarith [hc.2,lt_of_not_ge hsc]⟩
      simpa only [te,ve,reflectEven,reflectOdd,ite_eq_right hsc,neg_sq] using hh
  have hB := returning_arbitrary_field_nonnegative (right := right) (p := p) (t := te) (v := ve)
    hC hδ hbound hder hconc hdom hL
    (by simpa [te,reflectEven] using hstar)
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2)
    (fun s hs => (hsmooth s hs).1) (fun s hs => (hsmooth s hs).2)
    he0 heL her hE hWs
  let f := returnNormalDensity right δ p t v V (deriv V)
  let g := returnNormalDensity right δ p te ve W (deriv W)
  have heq : EqOn g f (Icc 0 b) := by
    intro s hs
    dsimp only [g,f,returnNormalDensity,momentumVelocity,te,ve]
    rw [het hs,hev hs,hWeq s hs,hWdeq s hs]
  have hzero : EqOn g 0 (Ioo b (2*c)) := by
    intro s hs
    have hbl : b < 2*c := hs.1.trans hs.2
    have hw : W = cut b V := ite_eq_left hbl
    dsimp only [g,returnNormalDensity]
    rw [hw,cut_zero hs.1,cut_deriv_zero hs.1,normalDensity_zero]
    rfl
  have hgi : IntervalIntegrable g volume 0 b := hfi.congr_uIoo (by
    rw [uIoo_of_le hb.le]; intro s hs; exact (heq (Ioo_subset_Icc_self hs)).symm)
  have hgib : IntervalIntegrable g volume b (2*c) := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume b (2*c)).congr_uIoo (by
    rw [uIoo_of_le hbL]
    intro s hs
    exact (hzero hs).symm)
  have hgz : (∫ s in b..(2*c), g s) = 0 := by
    calc
      _ = ∫ s in b..(2*c), (0:ℝ) := intervalIntegral.integral_congr_Ioo_of_le hbL hzero
      _ = 0 := by simp
  have hgf : (∫ s in (0:ℝ)..b, g s) = ∫ s in (0:ℝ)..b, f s :=
    intervalIntegral.integral_congr (by simpa only [uIcc_of_le hb.le] using heq)
  have hi := intervalIntegral.integral_add_adjacent_intervals hgi hgib
  change (∫ s in (0:ℝ)..b, g s) + (∫ s in b..(2*c), g s) = (∫ s in (0:ℝ)..(2*c), g s) at hi
  rw [hgz,hgf,add_zero] at hi
  rw [hi]
  exact hB
end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem framed_truncated_return_index (right : Bool) {δ C L c : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3 * C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hc : c ∈ Ioo 0 L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0)
    (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hvc : deriv γ c 0 = 0)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hstar : 1/4 < γ c 0)
    (henergy : ∀ s ∈ Icc 0 L,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  have hL : 0 < L := hc.1.trans hc.2
  have hgc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ γ s :=
    (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))
  have hJc (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ J s :=
    (euclidean_field_smooth hU hγ.1 hJ).contDiffAt (hU.mem_nhds (hsub hs))
  have hVa (s : ℝ) (hs : s ∈ Icc 0 L) : ContDiffAt ℝ ∞ (fun r => splitVector (J r)) s := by
    exact (TorusNeck.splitVector_smooth.contDiffAt.comp s (hJc s hs))
  let f := indexPairDensity (framedNeck right hδ) γ J J
  let q := fun s => ((framedNeck right hδ).inner (γ s)
      (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2
  have hfi : IntervalIntegrable f volume 0 L :=
    ((indexPairDensity_smooth _ hU hγ.1 hJ hJ).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have hqi : IntervalIntegrable q volume 0 L :=
    (((intrinsic_pairing_smooth _ hU hγ.1 (covariantDerivative_smooth _ hU hγ.1 hJ)
      (velocity_smooth hU hγ.1)).pow 2).continuousOn.mono hsub).intervalIntegrable_of_Icc hL.le
  have hnormalI : IntervalIntegrable (returnNormalDensity right δ p (fun r => γ r 0)
      (fun r => deriv γ r 0) (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r)))) volume 0 L := by
    apply (hfi.sub hqi).congr_ae
    apply (ae_restrict_mem measurableSet_uIoc).mono
    intro s hs
    rw [uIoc_of_le hL.le] at hs
    have hi := framedNeck_index_density right hδ (J := J) (hrc s (Ioc_subset_Icc_self hs))
    have he : momentumVelocity right δ p (fun r => γ r 0) (fun r => deriv γ r 0) s = splitVector (deriv γ s) := by
      apply Prod.ext
      · rfl
      · exact (framed_velocity_torus right hδ (hrc s (Ioc_subset_Icc_self hs)) (hp s (Ioc_subset_Icc_self hs))).symm
    dsimp only [f,q]
    rw [framedNeck_index_density right hδ (hrc s (Ioc_subset_Icc_self hs)),add_sub_cancel_right]
    rw [returnNormalDensity,he,split_deriv ((hJc s (Ioc_subset_Icc_self hs)).differentiableAt (by simp))]
  have hcut : L < 2*c → (fun r => splitVector (J r)) =ᶠ[𝓝 L] 0 := by
    intro hLC
    have hcomp := PassageDynamics.finite_turn_completion (force_smooth right δ p) hc
      (fun s hs => hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0)
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs)) hvc h0 hr
    simp only [sub_zero] at hcomp
    have hheight := hcomp.2.2.2.2.2 L ⟨hL,hLC⟩
    rw [hcomp.2.1 (right_mem_Icc.mpr hL.le)] at hheight
    change γ L 0 ∈ Ioo (0:ℝ) 1 at hheight
    rcases hend with (hz | ho) | hz
    · rw [hz] at hheight
      exact (lt_irrefl 0 hheight.1).elim
    · rw [ho] at hheight
      exact (lt_irrefl 1 hheight.2).elim
    · filter_upwards [hz] with s hs
      simp [hs,splitVector]
  have hbound : 0 ≤ ∫ s in (0:ℝ)..L,
      returnNormalDensity right δ p (fun r => γ r 0) (fun r => deriv γ r 0)
        (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s := by
    apply truncated_return_nonnegative (right := right) (p := p)
      (t := fun r => γ r 0) (v := fun r => deriv γ r 0) hC hsmall (fun u hu q => (hb u hu q).1)
      (fun u hu => ?_) (fun u hu q => (hb u hu q).2.2.1)
      (fun u hu => (hb u hu p).2.2.2) hc
      (fun s hs => hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0)
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s (hgc s hs))
      (fun s hs => (contDiff_apply ℝ ℝ (0 : Fin 3)).contDiffAt.comp s
        ((hgc s hs).derivWithin (m := ∞) (by simp)))
      h0 hr hvc hstar (fun s hs => (framed_energy_identity right hδ (hrc s hs) (hp s hs)).symm.trans (henergy s hs)) hVa hcut hnormalI
    simpa only [sqnorm_e,mul_one] using (hb u hu e).2.1
  have he : (∫ s in (0:ℝ)..L, returnNormalDensity right δ p (fun r => γ r 0)
      (fun r => deriv γ r 0) (fun r => splitVector (J r)) (deriv (fun r => splitVector (J r))) s) =
      ∫ s in (0:ℝ)..L, (f s - q s) := by
    apply intervalIntegral.integral_congr_uIoo
    rw [uIoo_of_le hL.le]
    intro s hs
    exact framed_return_density right hδ (hr s hs) (hp s (Ioo_subset_Icc_self hs))
      ((hJc s (Ioo_subset_Icc_self hs)).differentiableAt (by simp))
  rw [he,intervalIntegral.integral_sub hfi hqi] at hbound
  have hq : 0 ≤ ∫ s in (0:ℝ)..L, q s := intervalIntegral.integral_nonneg hL.le (fun s _ => sq_nonneg _)
  linarith
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

lemma coordinateCometric_end_third (right : Bool) {δ t : ℝ} (ht : t < 1/3) :
    coordinateCometric right δ t = !![1+δ*A t,0;0,1+δ*A 1] := by
  cases right
  · have hc := χ_eq_zero (show t ≤ 5/12 by linarith)
    have hA := A_plateau (show 2/3 ≤ 1-t by linarith) (show (2/3:ℝ) ≤ 1 by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateCometric,P,d₁,d₂,shear,hc,hA]
  · have hc := χ_eq_one (show 7/12 ≤ 1-t by linarith)
    have hA := A_plateau (show 2/3 ≤ 1-t by linarith) (show (2/3:ℝ) ≤ 1 by norm_num)
    have he : 1-(1-t) = t := by ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateCometric,PEnd,C₂,P,d₁,d₂,shear,hc,hA,he,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.transpose_apply] <;> ring

lemma metricInverse_end_warped (right : Bool) {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (ht : t ∈ Ioo (-1/4:ℝ) (1/3)) :
    metricInverse right δ t = WarpedCurvature.Q (Collar.ell δ) (Collar.ell δ 1) t := by
  unfold metricInverse
  rw [coordinateCometric_end_third right ht.2]
  apply Matrix.inv_eq_left_inv
  have h0 := Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ ht.1
  have h1 := Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ (by norm_num : (-1/4:ℝ) < 1)
  change (Collar.ell δ t)^2 * (1+δ*A t) = 1 at h0
  change (Collar.ell δ 1)^2 * (1+δ*A 1) = 1 at h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WarpedCurvature.Q,WarpedCurvature.diag,Matrix.mul_apply,Fin.sum_univ_two,h0,h1]

lemma ell_convex_nonnegative {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : 0 ≤ t) :
    0 ≤ deriv (deriv (Collar.ell δ)) t := by
  have he : Collar.k δ =ᶠ[𝓝 t] Collar.rate δ := by
    filter_upwards [Ioi_mem_nhds (show (-1/4:ℝ) < t by linarith)] with u hu
    exact Collar.k_eq_rate hu.le
  have hk : deriv (Collar.k δ) t ≤ 0 := by
    rw [he.deriv_eq,(Collar.rate_hasDerivAt ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonneg_of_nonpos hδ.1.le
      have hd := Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)
      have ha := mul_nonpos_of_nonpos_of_nonneg (a_deriv_nonpos t) hd.le
      have hq := mul_nonneg hδ.1.le (sq_nonneg (a t))
      linarith
    · positivity
  rw [Collar.ell_second ⟨hδ.1.le,hδ.2⟩]
  exact mul_nonneg (sub_nonneg.mpr (hk.trans (sq_nonneg _))) (Collar.ell_pos δ t).le

lemma framed_neck_shallow_nonpositive (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {x : E3} (hx : x 0 ∈ Icc (0:ℝ) (1/4)) : NonpositiveAt (framedNeck right hδ) x := by
  have he : metricMatrix (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[𝓝 x]
      fun y => blockMatrix (WarpedCurvature.Q (Collar.ell δ) (Collar.ell δ 1) (y 0)) := by
    filter_upwards [framedNeck_matrix_germ right hδ ⟨hx.1,by linarith [hx.2]⟩,
      ((continuous_apply 0).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (show x 0 ∈ Ioo (-1/4:ℝ) (1/3) from ⟨by linarith [hx.1],by linarith [hx.2]⟩)))] with y hy ht
    rw [hy,metricInverse_end_warped right hδ ht]
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  exact WarpedCurvature.warped_nonpositive _ _ (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)
    (Collar.ell_pos δ) (Collar.ell_pos δ 1).ne' he (ell_convex_nonnegative hδ hx.1) u v

lemma framed_shallow_index (right : Bool) {δ a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} (hab : a ≤ b)
    (hγ : ∀ s ∈ Icc a b, ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s)
    (ht : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) (1/4)) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  exact indexPairDensity_nonneg_of_nonpositiveAt _ J (hγ s hs) (framed_neck_shallow_nonpositive right hδ (ht s hs))
end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
lemma finite_turn_maximum {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) {t v : ℝ → ℝ}
    {b c : ℝ} (hc : c ∈ Ioo 0 b)
    (ht : ∀ s ∈ Icc 0 b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc 0 b, HasDerivAt v (-F (t s)/2) s) (hvc : v c = 0)
    (ha : t 0 = 0) (hr : ∀ s ∈ Ioo 0 b, t s ∈ Ioo (0:ℝ) 1) :
    ∀ s ∈ Icc 0 b, t s ≤ t c := by
  have hd := reflected_closed_equations hF hc ht hv hvc
  have hh := finite_turn_completion hF hc ht hv hvc ha hr
  simp only [sub_zero] at hd hh
  have hm := (actual_return_symmetry hF (by linarith [hc.1] : 0 < 2*c)
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2) hh.2.2.2.1 hh.2.2.2.2.1
    (fun s hs => (hh.2.2.2.2.2 s hs).1)).2.1
  rw [show 2*c/2 = c by ring] at hm
  intro s hs
  have he := hm ⟨hs.1,hs.2.trans hh.1⟩
  change reflectEven c t s ≤ reflectEven c t c at he
  rw [hh.2.1 hs,reflectEven,ite_eq_left le_rfl] at he
  exact he
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem framed_turn_index (right : Bool) {δ C L c : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ)
    (hb : ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
      (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
      0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
      sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q)
    {U : Set ℝ} (hU : IsOpen U) (hsub : Icc 0 L ⊆ U) (hc : c ∈ Ioo 0 L)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc 0 L, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (h0 : γ 0 0 = 0) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hvc : deriv γ c 0 = 0) (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (henergy : ∀ s ∈ Icc 0 L,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  by_cases hstar : 1/4 < γ c 0
  · exact framed_truncated_return_index right hδ hC hsmall hb hU hsub hc hγ hJ hp h0 hrc hend hvc hr hstar henergy
  · have ht (s : ℝ) (hs : s ∈ Icc 0 L) : HasDerivAt (fun r => γ r 0) (deriv γ s 0) s :=
      hasDerivAt_pi.mp (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))).differentiableAt (by simp)).hasDerivAt 0
    have hm := PassageDynamics.finite_turn_maximum (force_smooth right δ p) hc ht
      (fun s hs => framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs)) hvc h0 hr
    apply framed_shallow_index right hδ (hc.1.trans hc.2).le
      (fun s hs => hγ.1.contMDiffAt (hU.mem_nhds (hsub hs)))
    intro s hs
    exact ⟨(hrc s hs).1,(hm s hs).trans (le_of_not_gt hstar)⟩
end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma framed_boundary_hasDerivAt (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) (hJ : DifferentiableAt ℝ J s) :
    HasDerivAt (fun r => boundaryTerm (deriv (metricInverse right δ) (γ r 0))
      (splitVector (deriv γ r)) (splitVector (J r)))
      (boundaryJet (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s)) (splitVector (deriv J s))) s := by
  have hvel := framed_velocity_equation right hδ hU hγ hs ht
  have hfield := TorusNeck.splitVector_hasDerivAt hJ.hasDerivAt
  have hv : HasDerivAt (fun r => (splitVector (deriv γ r)).1)
      ((1/2:ℝ)*pairing (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)).2 (splitVector (deriv γ s)).2) s := by
    have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).1)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
    convert h using 1
    simp only [gamma,Prod.fst_neg]
    ring
  have hu : HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-(splitVector (deriv γ s)).1 • (coordinateCometric right δ (γ s 0) *ᵥ
        (deriv (metricInverse right δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
    have h := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at h
    convert h using 1
    ext i
    simp only [gamma,Prod.snd_neg,Pi.neg_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  exact boundaryTerm_hasDerivAt (coordinateCometric_transpose right δ _)
    (metricInverse_deriv_transpose right δ _) (metricInverse_second_transpose right δ _)
    (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht)).derivWithin (m := ∞)
      (by simp)).differentiableAt (by simp)).hasDerivAt
    (hasDerivAt_pi.mp (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt 0)
    hv hu ((ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hfield)
      ((ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hfield)

lemma framed_index_energy (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    indexPairDensity (framedNeck right hδ) γ J J s =
      coordinateEnergyDensity (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (deriv γ s))
        (splitVector (J s)) (splitVector (deriv J s)) -
      boundaryJet (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (deriv γ s))
        (splitVector (J s)) (splitVector (deriv J s)) := by
  rw [framedNeck_index_density right hδ ht]
  unfold normalDensity
  rw [index_density_identity (frame_QP right ⟨hδ.1.le,hδ.2⟩ ht)
    (metricInverse_transpose right δ _) (coordinateCometric_transpose right δ _)
    (metricInverse_deriv_transpose right δ _) (metricInverse_second_transpose right δ _)]
  rw [euclidean_velocity,framedNeck_covariant right hδ γ J ht,
    framedNeck_bilin right hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩,
    TorusNeck.split_add,split_join]
  ring

lemma framed_energy_nonneg (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) {p : TVec}
    (hc : 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) p)
    (v : ℝ) (V D : Vec) :
    0 ≤ coordinateEnergyDensity (metricInverse right δ t) (deriv (metricInverse right δ) t)
      (deriv (deriv (metricInverse right δ)) t) (v,coordinateCometric right δ t *ᵥ p) V D := by
  rw [metricInverse_first (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),
    metricInverse_second (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),
    energy_cometric_identity (frame_QP right ⟨hδ.1.le,hδ.2⟩ ht)
      (coordinateCometric_transpose right δ _) (metricInverse_transpose right δ _)
      (symmetric_total_deriv (coordinateCometric_transpose right δ) t)]
  have hp := (coordinateCometric_posDef (fun q => (frame_elliptic right ⟨hδ.1.le,hδ.2⟩ ht q).1)).inv.posSemidef
  have hh := hp.dotProduct_mulVec_nonneg (D.2-V.1 • (deriv (coordinateCometric right δ) t *ᵥ p))
  simp only [star_trivial] at hh
  change 0 ≤ pairing (metricInverse right δ t) _ _ at hh
  have hc' : pairing (deriv (deriv (coordinateCometric right δ)) t) p p ≤ 0 := by
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) t) p p at hc
    rw [pairing_matrix_neg] at hc
    linarith
  have hn := mul_nonpos_of_nonpos_of_nonneg hc' (sq_nonneg V.1)
  nlinarith [sq_nonneg D.1]
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
lemma framed_coordinate_index_integral (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ} (hab : uIcc a b ⊆ U)
    (htr : ∀ s ∈ uIcc a b, γ s 0 ∈ Icc (0:ℝ) 1) :
    (∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s) =
    (∫ s in a..b, coordinateEnergyDensity (metricInverse right δ (γ s 0))
      (deriv (metricInverse right δ) (γ s 0)) (deriv (deriv (metricInverse right δ)) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s)) (splitVector (deriv J s))) -
    (boundaryTerm (deriv (metricInverse right δ) (γ b 0)) (splitVector (deriv γ b)) (splitVector (J b)) -
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a)) (splitVector (J a))) := by
  let t := fun s => γ s 0
  let T := fun s => splitVector (deriv γ s)
  let V := fun s => splitVector (J s)
  let D := fun s => splitVector (deriv J s)
  have ht : ∀ s ∈ uIcc a b, ContinuousAt t s :=
    fun s hs => (hasDerivAt_pi.mp (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hab hs))).differentiableAt (by simp)).hasDerivAt 0).continuousAt
  have hP : ContinuousOn (coordinateCometric right δ ∘ t) (uIcc a b) := by
    intro s hs
    exact ((coordinateCometric_smooth right δ).continuous.continuousAt.comp (ht s hs)).continuousWithinAt
  have hQ : ContinuousOn (metricInverse right δ ∘ t) (uIcc a b) := by
    intro s hs
    have hr := htr s hs
    have hc : ContinuousAt (metricInverse right δ) (t s) := (metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hr)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hA : ContinuousOn (deriv (metricInverse right δ) ∘ t) (uIcc a b) := by
    intro s hs
    have hr := htr s hs
    have hc : ContinuousAt (deriv (metricInverse right δ)) (t s) :=
      ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hr)).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hB : ContinuousOn (deriv (deriv (metricInverse right δ)) ∘ t) (uIcc a b) := by
    intro s hs
    have hr := htr s hs
    have hc : ContinuousAt (deriv (deriv (metricInverse right δ))) (t s) :=
      (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hr)).derivWithin (m := ∞) (by simp)).derivWithin
        (m := ∞) (by simp)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hT : ContinuousOn T (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hab hs))).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hV : ContinuousOn V (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      (hJ.contDiffAt (hU.mem_nhds (hab hs))).continuousAt).continuousWithinAt
  have hD : ContinuousOn D (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      ((hJ.contDiffAt (hU.mem_nhds (hab hs))).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  let E := fun s => coordinateEnergyDensity (metricInverse right δ (t s)) (deriv (metricInverse right δ) (t s))
    (deriv (deriv (metricInverse right δ)) (t s)) (T s) (V s) (D s)
  let B := fun s => boundaryJet (coordinateCometric right δ (t s)) (deriv (metricInverse right δ) (t s))
    (deriv (deriv (metricInverse right δ)) (t s)) (T s) (V s) (D s)
  have he : ContinuousOn E (uIcc a b) := continuousOn_energy hQ hA hB hT hV hD
  have hb : ContinuousOn B (uIcc a b) := continuousOn_boundaryJet hP hA hB hT hV hD
  have hderiv : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r => boundaryTerm (deriv (metricInverse right δ) (t r)) (T r) (V r)) (B s) s := by
    intro s hs
    exact framed_boundary_hasDerivAt right hδ hU hγ (hab hs) (htr s hs)
      ((hJ.contDiffAt (hU.mem_nhds (hab hs))).differentiableAt (by simp))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hb.intervalIntegrable
  calc
    _ = ∫ s in a..b, E s - B s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact framed_index_energy right hδ (htr s hs)
    _ = (∫ s in a..b, E s) - ∫ s in a..b, B s :=
      intervalIntegral.integral_sub he.intervalIntegrable hb.intervalIntegrable
    _ = _ := by rw [hFTC]

lemma framed_zero_endpoints_index (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hc : ∀ t ∈ Icc (0:ℝ) 1, ∀ p, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) p)
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1) (hJa : J a = 0) (hJb : J b = 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  rw [framed_coordinate_index_integral right hδ hU hγ hJ
    (by simpa only [uIcc_of_le hab] using hsub) (by simpa only [uIcc_of_le hab] using htr)]
  have hb0 (s : ℝ) (hJs : J s = 0) :
      boundaryTerm (deriv (metricInverse right δ) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s)) = 0 := by
    simp [hJs, splitVector, boundaryTerm, pairing]
  rw [hb0 b hJb,hb0 a hJa,sub_self,sub_zero]
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  let p := metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2
  have hu := framed_velocity_torus right hδ (htr s hs) (show metricInverse right δ (γ s 0) *ᵥ
    (splitVector (deriv γ s)).2 = p from rfl)
  have hT : splitVector (deriv γ s) = ((splitVector (deriv γ s)).1,coordinateCometric right δ (γ s 0) *ᵥ p) := by
    rw [← hu]
  rw [hT]
  exact framed_energy_nonneg right hδ (htr s hs) (hc _ (htr s hs) p) _ _ _

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

lemma zeroHeight_covariant_pair {P Q : TMat} (hQP : Q * P = 1) (hQ : Qᵀ = Q)
    (A : TMat) (v : ℝ) (u z zd : TVec) :
    metric Q ((0,zd) + gamma P A (v,u) (0,z)) (v,u) = pairing Q zd u := by
  rw [metric_add_left,metric_symm hQ (gamma P A (v,u) (0,z)),metric_gamma hQP]
  simp only [metric]
  ring

lemma zeroHeight_normalDensity {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (v : ℝ) (u z zd : TVec) :
    normalDensity P Q A B (v,u) (0,z) (0,zd) =
      pairing Q zd zd - (pairing Q zd u)^2 - boundaryJet P A B (v,u) (0,z) (0,zd) := by
  unfold normalDensity
  rw [index_density_identity hQP hQ hP hA hB,zeroHeight_covariant_pair hQP hQ]
  simp only [coordinateEnergyDensity]
  ring

lemma transverse_energy_nonneg {Q : TMat} (hQ : Qᵀ = Q)
    (hpos : ∀ z, 0 ≤ pairing Q z z) {v : ℝ} {u : TVec}
    (hu : metric Q (v,u) (v,u) = 1) (z : TVec) :
    0 ≤ pairing Q z z - (pairing Q z u)^2 := by
  have hc := psd_cauchy hQ hpos z u
  have hp := mul_nonneg (hpos z) (sq_nonneg v)
  change v * v + pairing Q u u = 1 at hu
  nlinarith

lemma zeroHeight_index_nonnegative
    {P Q A B : ℝ → TMat} {t v : ℝ → ℝ} {u z zd : ℝ → TVec} {a b : ℝ}
    (hab : a ≤ b)
    (hP : ContinuousOn (P ∘ t) (uIcc a b)) (hQ : ContinuousOn (Q ∘ t) (uIcc a b))
    (hA : ContinuousOn (A ∘ t) (uIcc a b)) (hB : ContinuousOn (B ∘ t) (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hu : ContinuousOn u (uIcc a b))
    (hz : ContinuousOn z (uIcc a b)) (hzd : ContinuousOn zd (uIcc a b))
    (hQP : ∀ s ∈ uIcc a b, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ uIcc a b, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ uIcc a b, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ uIcc a b, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ uIcc a b, (B (t s))ᵀ = B (t s))
    (hpos : ∀ s ∈ uIcc a b, ∀ q, 0 ≤ pairing (Q (t s)) q q)
    (hunit : ∀ s ∈ uIcc a b, metric (Q (t s)) (v s,u s) (v s,u s) = 1)
    (ht : ∀ s ∈ uIcc a b, HasDerivAt t (v s) s)
    (hvd : ∀ s ∈ uIcc a b, HasDerivAt v ((1/2:ℝ)*pairing (A (t s)) (u s) (u s)) s)
    (hud : ∀ s ∈ uIcc a b, HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hAd : ∀ s ∈ uIcc a b, HasDerivAt A (B (t s)) (t s))
    (hzd' : ∀ s ∈ uIcc a b, HasDerivAt z (zd s) s)
    (hboundary : boundaryTerm (A (t b)) (v b,u b) (0,z b) ≤
      boundaryTerm (A (t a)) (v a,u a) (0,z a)) :
    0 ≤ ∫ s in a..b, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s,u s) (0,z s) (0,zd s) := by
  let e := fun s => pairing (Q (t s)) (zd s) (zd s) - (pairing (Q (t s)) (zd s) (u s))^2
  let j := fun s => boundaryJet (P (t s)) (A (t s)) (B (t s)) (v s,u s) (0,z s) (0,zd s)
  have he : ContinuousOn e (uIcc a b) :=
    (continuousOn_pairing hQ hzd hzd).sub ((continuousOn_pairing hQ hzd hu).pow 2)
  have hj : ContinuousOn j (uIcc a b) := continuousOn_boundaryJet hP hA hB
    (hv.prodMk hu) (continuousOn_const.prodMk hz) (continuousOn_const.prodMk hzd)
  have hd : ∀ s ∈ uIcc a b, HasDerivAt
      (fun r => boundaryTerm (A (t r)) (v r,u r) (0,z r)) (j s) s := by
    intro s hs
    exact boundaryTerm_hasDerivAt (hPs s hs) (hAs s hs) (hBs s hs)
      (hAd s hs) (ht s hs) (hvd s hs) (hud s hs) (hasDerivAt_const s 0) (hzd' s hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hj.intervalIntegrable
  have heq : (∫ s in a..b, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s,u s) (0,z s) (0,zd s)) = (∫ s in a..b, e s) - (∫ s in a..b, j s) := by
    rw [← intervalIntegral.integral_sub he.intervalIntegrable hj.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro s hs
    exact zeroHeight_normalDensity (hQP s hs) (hQs s hs) (hPs s hs) (hAs s hs) (hBs s hs) _ _ _ _
  rw [heq,hFTC]
  have hen : 0 ≤ ∫ s in a..b, e s := by
    apply intervalIntegral.integral_nonneg hab
    intro s hs
    have hs' : s ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hs
    exact transverse_energy_nonneg (hQs s hs') (hpos s hs') (hunit s hs') _
  linarith
end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

lemma euclidean_covariant (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    covariantDerivative g γ J s = deriv J s + connectionTerm g (OpenPartialHomeomorph.refl E3)
      (γ s) (deriv γ s) (J s) := by
  unfold covariantDerivative
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma euclidean_curvature (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    curvatureAlong g γ J s = curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s)
      (J s) (deriv γ s) (deriv γ s) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma euclidean_smoothField {γ J : ℝ → E3} {U : Set ℝ} (hJ : ContDiffOn ℝ ∞ J U) :
    SmoothFieldOn γ J U := by
  intro c hc
  have he := chartedSpaceSelf_atlas.mp hc
  subst c
  rw [euclidean_fieldCoordinates]
  exact hJ.mono inter_subset_left

lemma affine_hasDerivAt {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    HasDerivAt (fun r => f (a+k*r)) (k • deriv f (a+k*s)) s := by
  convert hf.hasDerivAt.scomp s (((hasDerivAt_id s).const_mul k).const_add a) using 1 <;> first | rfl | simp

lemma affine_deriv {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    deriv (fun r => f (a+k*r)) s = k • deriv f (a+k*s) := (affine_hasDerivAt hf).deriv

lemma connection_smul_left (g : SmoothMetric E3) (x u v : E3) (k : ℝ) :
    connectionTerm g (OpenPartialHomeomorph.refl E3) x (k • u) v =
      k • connectionTerm g (OpenPartialHomeomorph.refl E3) x u v := by
  simp only [← connectionBilin_apply,map_smul,_root_.smul_apply]
lemma connection_smul_right (g : SmoothMetric E3) (x u v : E3) (k : ℝ) :
    connectionTerm g (OpenPartialHomeomorph.refl E3) x u (k • v) =
      k • connectionTerm g (OpenPartialHomeomorph.refl E3) x u v := by
  simp only [← connectionBilin_apply,map_smul]

lemma euclidean_affine_geodesic (g : SmoothMetric E3) {γ : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) (a k : ℝ) :
    IsGeodesicOn g (fun s => γ (a+k*s)) ((fun s : ℝ => a+k*s) ⁻¹' U) := by
  have hgc := euclidean_curve_smooth hγ.1
  have hf : ContDiff ℝ ∞ (fun s : ℝ => a+k*s) := contDiff_const.add (contDiff_const.mul contDiff_id)
  refine ⟨contMDiffOn_iff_contDiffOn.mpr (hgc.comp hf.contDiffOn (fun _ hs => hs)),?_⟩
  intro c hc s hs _
  have he := chartedSpaceSelf_atlas.mp hc
  subst c
  change deriv (deriv (fun r => γ (a+k*r))) s + connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv (fun r => γ (a+k*r)) s) (deriv (fun r => γ (a+k*r)) s) = 0
  have hg : ContDiffAt ℝ ∞ γ (a+k*s) := hgc.contDiffAt (hU.mem_nhds hs)
  have hgd : DifferentiableAt ℝ (deriv γ) (a+k*s) :=
    (hg.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hev : deriv (fun r => γ (a+k*r)) =ᶠ[nhds s] (fun r => k • deriv γ (a+k*r)) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hs)] with r hr
    exact affine_deriv ((hgc.contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp))
  have hd : deriv (fun r => k • deriv γ (a+k*r)) s = k • (k • deriv (deriv γ) (a+k*s)) :=
    ((affine_hasDerivAt hgd).const_smul k).deriv
  rw [hev.deriv_eq, hd,
    affine_deriv (hg.differentiableAt (by simp)),connection_smul_left,connection_smul_right]
  have hz := hγ.2 (OpenPartialHomeomorph.refl E3) (chart_mem_atlas E3 (0:E3)) (a+k*s) hs (mem_univ _)
  change deriv (deriv γ) (a+k*s) + connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv γ (a+k*s)) (deriv γ (a+k*s)) = 0 at hz
  rw [← smul_add,← smul_add,hz,smul_zero,smul_zero]

lemma euclidean_affine_covariant (g : SmoothMetric E3) {γ J : ℝ → E3} {s a k : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) (hJ : DifferentiableAt ℝ J (a+k*s)) :
    covariantDerivative g (fun r => γ (a+k*r)) (fun r => J (a+k*r)) s =
      k • covariantDerivative g γ J (a+k*s) := by
  rw [euclidean_covariant,euclidean_covariant,affine_deriv hγ,affine_deriv hJ,connection_smul_left]
  change (k • deriv J (a+k*s) + k • connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv γ (a+k*s)) (J (a+k*s)) : E3) = k • _
  exact (smul_add k _ _).symm

lemma curvature_smul_velocity (g : SmoothMetric E3) (x J T : E3) (k : ℝ) :
    curvatureTerm g (OpenPartialHomeomorph.refl E3) x J (k • T) (k • T) =
      (k*k) • curvatureTerm g (OpenPartialHomeomorph.refl E3) x J T T := by
  ext l
  simp only [curvatureTerm,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  ring

lemma euclidean_affine_index (g : SmoothMetric E3) {γ J : ℝ → E3} {s a k : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) (hJ : DifferentiableAt ℝ J (a+k*s)) :
    indexPairDensity g (fun r => γ (a+k*r)) (fun r => J (a+k*r)) (fun r => J (a+k*r)) s =
      k^2 * indexPairDensity g γ J J (a+k*s) := by
  unfold indexPairDensity
  rw [euclidean_affine_covariant g hγ hJ,euclidean_curvature,euclidean_curvature,
    affine_deriv hγ,curvature_smul_velocity]
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ (a+k*s))
  let D : E3 := covariantDerivative g γ J (a+k*s)
  change B (k • D) (k • D) -
    B ((k*k) • curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ (a+k*s)) (J (a+k*s))
      (deriv γ (a+k*s)) (deriv γ (a+k*s))) (J (a+k*s)) =
    k^2 * (B D D -
      B (curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ (a+k*s)) (J (a+k*s))
        (deriv γ (a+k*s)) (deriv γ (a+k*s))) (J (a+k*s)))
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

lemma framed_metric_velocity_equations (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (htr : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => deriv γ r 0)
      ((1/2:ℝ)*pairing (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)).2 (splitVector (deriv γ s)).2) s ∧
    HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-deriv γ s 0 • (coordinateCometric right δ (γ s 0) *ᵥ
        (deriv (metricInverse right δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
  have hvel := framed_velocity_equation right hδ hU hγ hs htr
  constructor
  · have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => deriv γ r 0)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
    convert h using 1
    simp only [gamma,Prod.fst_neg]
    ring
  · have h := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at h
    convert h using 1
    ext i
    simp only [gamma,Prod.snd_neg,Pi.neg_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul,splitVector]
    ring

lemma framed_zeroheight_normal_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ W : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hW : ContDiffOn ℝ ∞ W U) (hW0 : ∀ s ∈ U, W s 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (W b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a)) (splitVector (W a))) :
    0 ≤ ∫ s in a..b, normalDensity (coordinateCometric right δ (γ s 0))
      (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
      (deriv (deriv (metricInverse right δ)) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (W s)) (splitVector (deriv W s)) := by
  let t := fun s => γ s 0
  let v := fun s => deriv γ s 0
  let u := fun s => (splitVector (deriv γ s)).2
  let z := fun s => (splitVector (W s)).2
  let zd := fun s => (splitVector (deriv W s)).2
  have hsubs : uIcc a b ⊆ U := by rwa [uIcc_of_le hab]
  have htrs : ∀ s ∈ uIcc a b, γ s 0 ∈ Icc (0:ℝ) 1 := by rwa [uIcc_of_le hab]
  have hgc (s : ℝ) (hs : s ∈ uIcc a b) := (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsubs hs))
  have hwc (s : ℝ) (hs : s ∈ uIcc a b) := hW.contDiffAt (hU.mem_nhds (hsubs hs))
  have ht (s : ℝ) (hs : s ∈ uIcc a b) : HasDerivAt t (v s) s :=
    hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0
  have hP : ContinuousOn (coordinateCometric right δ ∘ t) (uIcc a b) :=
    fun s hs => ((coordinateCometric_smooth right δ).continuous.continuousAt.comp (ht s hs).continuousAt).continuousWithinAt
  have hQ : ContinuousOn (metricInverse right δ ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (metricInverse right δ) (t s) := (metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hA : ContinuousOn (deriv (metricInverse right δ) ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (deriv (metricInverse right δ)) (t s) := ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hB : ContinuousOn (deriv (deriv (metricInverse right δ)) ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (deriv (deriv (metricInverse right δ))) (t s) := (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hTc : ContinuousOn (fun s => splitVector (deriv γ s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp ((hgc s hs).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hWc : ContinuousOn (fun s => splitVector (W s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp (hwc s hs).continuousAt).continuousWithinAt
  have hDc : ContinuousOn (fun s => splitVector (deriv W s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp ((hwc s hs).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hw0 (s : ℝ) (hs : s ∈ uIcc a b) : splitVector (W s) = (0,z s) := by
    change (W s 0,z s) = _
    rw [hW0 s (hsubs hs)]
  have hd0 (s : ℝ) (hs : s ∈ uIcc a b) : splitVector (deriv W s) = (0,zd s) := by
    have hgerm : (fun r => W r 0) =ᶠ[nhds s] (fun _ => (0:ℝ)) := by
      filter_upwards [hU.mem_nhds (hsubs hs)] with r hr
      exact hW0 r hr
    have hh := hasDerivAt_pi.mp ((hwc s hs).differentiableAt (by simp)).hasDerivAt 0
    have hd : deriv W s 0 = 0 := hh.deriv.symm.trans (hgerm.deriv_eq.trans (deriv_const s 0))
    change (deriv W s 0,zd s) = _
    rw [hd]
  have hbnd : boundaryTerm (deriv (metricInverse right δ) (t b)) (v b,u b) (0,z b) ≤
      boundaryTerm (deriv (metricInverse right δ) (t a)) (v a,u a) (0,z a) := by
    rw [hw0 a left_mem_uIcc,hw0 b right_mem_uIcc] at hboundary
    exact hboundary
  have hbound := zeroHeight_index_nonnegative hab hP hQ hA hB hTc.fst hTc.snd hWc.snd hDc.snd
    (fun s hs => frame_QP right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))
    (fun s _ => metricInverse_transpose right δ (t s))
    (fun s _ => coordinateCometric_transpose right δ (t s))
    (fun s _ => metricInverse_deriv_transpose right δ (t s))
    (fun s _ => metricInverse_second_transpose right δ (t s))
    (fun s hs q => ?_) (fun s hs => ?_) ht
    (fun s hs => (framed_metric_velocity_equations right hδ hU hγ (hsubs hs) (htrs s hs)).1)
    (fun s hs => (framed_metric_velocity_equations right hδ hU hγ (hsubs hs) (htrs s hs)).2)
    (fun s hs => (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt)
    (fun s hs => (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (splitVector_hasDerivAt ((hwc s hs).differentiableAt (by simp)).hasDerivAt)) hbnd
  · convert hbound using 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hw0 s hs,hd0 s hs]
  · have hp := (coordinateCometric_posDef (fun q => (frame_elliptic right ⟨hδ.1.le,hδ.2⟩ (htrs s hs) q).1)).inv.posSemidef
    have hh := hp.dotProduct_mulVec_nonneg q
    simp only [star_trivial] at hh
    change 0 ≤ pairing (metricInverse right δ (γ s 0)) q q at hh
    exact hh
  · have hh := hunit s (by simpa only [uIcc_of_le hab] using hs)
    rw [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [(htrs s hs).1],by linarith [(htrs s hs).2]⟩] at hh
    exact hh

lemma framed_gauge_index_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {h : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (hJ : ContDiffOn ℝ ∞ J U)
    (hh : ContDiffOn ℝ ∞ h U)
    (hzero : ∀ s ∈ U, (J s + h s • deriv γ s) 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (J b + h b • deriv γ b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a))
        (splitVector (J a + h a • deriv γ a))) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  let W : ℝ → E3 := fun s => J s + h s • deriv γ s
  have hgc (s : ℝ) (hs : s ∈ U) := (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)
  have hJc (s : ℝ) (hs : s ∈ U) := hJ.contDiffAt (hU.mem_nhds hs)
  have hhc (s : ℝ) (hs : s ∈ U) := hh.contDiffAt (hU.mem_nhds hs)
  have hWc (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ W s :=
    (hJc s hs).add ((hhc s hs).smul ((hgc s hs).derivWithin (m := ∞) (by simp)))
  have hWs : ContDiffOn ℝ ∞ W U := fun s hs => (hWc s hs).contDiffWithinAt
  have hb := framed_zeroheight_normal_nonnegative right hδ hU hγ hWs hzero hab hsub htr hunit hboundary
  let N := fun s => normalDensity (coordinateCometric right δ (γ s 0))
    (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
    (deriv (deriv (metricInverse right δ)) (γ s 0))
    (splitVector (deriv γ s)) (splitVector (W s)) (splitVector (deriv W s))
  let f := indexPairDensity (framedNeck right hδ) γ J J
  let q := fun s => ((framedNeck right hδ).inner (γ s)
    (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2
  have hfi : IntervalIntegrable f volume a b :=
    ((indexPairDensity_smooth _ hU hγ.1 (euclidean_smoothField hJ) (euclidean_smoothField hJ)).continuousOn.mono hsub).intervalIntegrable_of_Icc hab
  have hqi : IntervalIntegrable q volume a b :=
    (((intrinsic_pairing_smooth _ hU hγ.1 (covariantDerivative_smooth _ hU hγ.1 (euclidean_smoothField hJ))
      (velocity_smooth hU hγ.1)).pow 2).continuousOn.mono hsub).intervalIntegrable_of_Icc hab
  have heq : (∫ s in a..b, N s) = ∫ s in a..b, (f s - q s) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro s hs
    have hunit' : metric (metricInverse right δ (γ s 0)) (splitVector (deriv γ s)) (splitVector (deriv γ s)) = 1 := by
      have hm := hunit s hs
      rwa [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [(htr s hs).1],by linarith [(htr s hs).2]⟩] at hm
    have hG := normalDensity_deriv_gauge (frame_QP right ⟨hδ.1.le,hδ.2⟩ (htr s hs))
      (metricInverse_transpose right δ _) (coordinateCometric_transpose right δ _)
      (metricInverse_deriv_transpose right δ _) (metricInverse_second_transpose right δ (γ s 0)) hunit'
      (splitVector_hasDerivAt ((hJc s (hsub hs)).differentiableAt (by simp)).hasDerivAt)
      (framed_velocity_equation right hδ hU hγ (hsub hs) (htr s hs))
      ((hhc s (hsub hs)).differentiableAt (by simp)).hasDerivAt
    have hfun : (fun r => splitVector (J r) + h r • splitVector (deriv γ r)) = (fun r => splitVector (W r)) := by
      funext r
      rw [show W r = J r + h r • deriv γ r from rfl,split_add]
      congr 1
      apply Prod.ext
      · rfl
      · ext i
        fin_cases i <;> rfl
    rw [hfun,(splitVector_hasDerivAt ((hWc s (hsub hs)).differentiableAt (by simp)).hasDerivAt).deriv] at hG
    have hWs : splitVector (J s) + h s • splitVector (deriv γ s) = splitVector (W s) := congrFun hfun s
    rw [hWs] at hG
    have hi := framedNeck_index_density right hδ (J := J) (htr s hs)
    change N s = f s - q s
    change N s = _ at hG
    rw [hG]
    exact eq_sub_of_add_eq hi.symm
  rw [heq,intervalIntegral.integral_sub hfi hqi] at hb
  have hq : 0 ≤ ∫ s in a..b, q s := intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)
  linarith
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

def regularGauge (γ J : ℝ → E3) (s : ℝ) : ℝ := -J s 0 / deriv γ s 0

def gaugeField (γ J : ℝ → E3) (s : ℝ) : E3 := J s + regularGauge γ J s • deriv γ s

lemma regularGauge_zero_germ {γ J : ℝ → E3} {s : ℝ} (hz : J =ᶠ[𝓝 s] 0) :
    regularGauge γ J =ᶠ[𝓝 s] 0 := by
  filter_upwards [hz] with r hr
  simp [regularGauge,hr]
lemma gaugeField_zero_germ {γ J : ℝ → E3} {s : ℝ} (hz : J =ᶠ[𝓝 s] 0) :
    gaugeField γ J =ᶠ[𝓝 s] 0 := by
  filter_upwards [hz,regularGauge_zero_germ (γ := γ) hz] with r hr hg
  simp [gaugeField,hr,hg]

lemma regular_gauge_neighborhood {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ ∞ γ U) (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ}
    (hsub : Icc a b ⊆ U)
    (hreg : ∀ s ∈ Icc a b, deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc a b ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (regularGauge γ J) V ∧ ∀ s ∈ V, gaugeField γ J s 0 = 0 := by
  let Z := interior {s | J s = 0}
  let D := U ∩ (fun s => deriv γ s 0) ⁻¹' {r : ℝ | r ≠ 0}
  have hv (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ (fun r => deriv γ r 0) s :=
    (contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt.comp s ((hγ.contDiffAt (hU.mem_nhds hs)).derivWithin (m := ∞) (by simp))
  have hD : IsOpen D := by
    apply (show ContinuousOn (fun s => deriv γ s 0) U from fun s hs => (hv s hs).continuousAt.continuousWithinAt).isOpen_inter_preimage hU
    exact isClosed_singleton.isOpen_compl
  let V := D ∪ (U ∩ Z)
  have hVU : V ⊆ U := by intro s hs; exact hs.elim And.left And.left
  have hsV (s : ℝ) (hs : s ∈ V) : deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0 := by
    rcases hs with hs | hs
    · exact Or.inl hs.2
    · exact Or.inr (mem_interior_iff_mem_nhds.mp hs.2)
  refine ⟨V,hD.union (hU.inter isOpen_interior),?_,hVU,?_,?_⟩
  · intro s hs
    rcases hreg s hs with hv | hz
    · exact Or.inl ⟨hsub hs,hv⟩
    · exact Or.inr ⟨hsub hs,mem_interior_iff_mem_nhds.mpr hz⟩
  · intro s hs
    apply ContDiffAt.contDiffWithinAt
    rcases hsV s hs with hn | hz
    · exact (((contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt.comp s
        (hJ.contDiffAt (hU.mem_nhds (hVU hs)))).neg.div (hv s (hVU hs)) hn)
    · exact contDiffAt_const.congr_of_eventuallyEq (regularGauge_zero_germ hz)
  · intro s hs
    rcases hsV s hs with hn | hz
    · dsimp [gaugeField,regularGauge]
      rw [div_mul_cancel₀ _ hn]
      ring
    · simpa using congrFun (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds 0
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

lemma increasing_boundary_derivative {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (_hv : ContinuousOn v (Icc a b)) (hm : AntitoneOn v (Icc a b))
    (hp : t a < t b) : 0 < v a := by
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope t v hab
    (fun s hs => (ht s hs).continuousAt.continuousWithinAt)
    (fun s hs => ht s (Ioo_subset_Icc_self hs))
  have hpv : 0 < v c := by rw [he]; exact div_pos (sub_pos.mpr hp) (sub_pos.mpr hab)
  exact hpv.trans_le (hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hc) hc.1.le)

lemma scalar_enter_transverse {t v F : ℝ → ℝ} {a b r : ℝ} (hab : a < b)
    (hr : 0 < r) (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s)
    (hF : ∀ x < r, 0 ≤ F x) : 0 < v a := by
  have haI : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hn : {s | t s < r} ∈ 𝓝 a := (ht a haI).continuousAt (Iio_mem_nhds (by simpa [ha] using hr))
  obtain ⟨l,c,⟨hl,hac⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨d,had,hdb⟩ := exists_between (lt_min hab hac)
  have hdb' : d < b := hdb.trans_le (min_le_left _ _)
  have hdc : d < c := hdb.trans_le (min_le_right _ _)
  have hsubab : Icc a d ⊆ Icc a b := Icc_subset_Icc le_rfl hdb'.le
  have hm : AntitoneOn v (Icc a d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a d)
    · exact fun s hs => (hv s (hsubab hs)).continuousAt.continuousWithinAt
    · exact fun s hs => (hv s (hsubab (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hv s (hsubab (interior_subset hs))).deriv]
      have hh := hF (t s) (hsub ⟨hl.trans_le (interior_subset hs).1,(interior_subset hs).2.trans_lt hdc⟩)
      linarith
  exact increasing_boundary_derivative had (fun s hs => ht s (hsubab hs))
    (fun s hs => (hv s (hsubab hs)).continuousAt.continuousWithinAt) hm
    (by rw [ha]; exact hpos d ⟨had,hdb'⟩)

lemma force_end_nonnegative (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (p : TVec)
    {x : ℝ} (hx : x < 1/4) : 0 ≤ force right δ p x := by
  unfold force
  rw [coordinateCometric_end_deriv hx]
  have ha : 0 ≤ a x := a_nonneg x
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero]
  nlinarith [mul_nonneg (mul_nonneg hδ ha) (sq_nonneg (p 0))]

lemma neck_enter_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s) : 0 < v a :=
  scalar_enter_transverse hab (by norm_num : (0:ℝ) < 1/4) ht hv ha hpos
    (fun _ hx => force_end_nonnegative right hδ p hx)
end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

def flipFrame (right : Bool) (δ : ℝ) : TMat := if right then C₂ δ else T₂ δ

lemma coordinateCometric_flip (right : Bool) (δ t : ℝ) :
    coordinateCometric right δ t = flipFrame right δ * coordinateCometric (!right) δ (1-t) * (flipFrame right δ)ᵀ := by
  cases right with
  | true => simp [coordinateCometric,flipFrame,PEnd]
  | false =>
    simp only [coordinateCometric,flipFrame,Bool.false_eq_true,↓reduceIte,Bool.not_false]
    unfold PEnd
    rw [show 1-(1-t) = t by ring]
    simp only [← Matrix.mul_assoc,(frame_inverse δ).2,Matrix.one_mul]
    rw [Matrix.mul_assoc,← Matrix.transpose_mul,(frame_inverse δ).2,Matrix.transpose_one,Matrix.mul_one]

lemma coordinateCometric_flip_deriv (right : Bool) (δ t : ℝ) :
    deriv (coordinateCometric right δ) t = -(flipFrame right δ *
      deriv (coordinateCometric (!right) δ) (1-t) * (flipFrame right δ)ᵀ) := by
  have hd := ((coordinateCometric_smooth (!right) δ).differentiable (by simp) (1-t)).hasDerivAt.scomp t
    ((hasDerivAt_id t).const_sub 1)
  have he := (congruenceCLM (flipFrame right δ)).hasFDerivAt.comp_hasDerivAt t hd
  have hf : (fun r => (congruenceCLM (flipFrame right δ)) (coordinateCometric (!right) δ (1-r))) =
      coordinateCometric right δ := by
    funext r
    exact (coordinateCometric_flip right δ r).symm
  dsimp only [Function.comp_def] at he
  rw [hf] at he
  have he' := he.deriv
  change deriv (coordinateCometric right δ) t = flipFrame right δ * ((-1:ℝ) • deriv (coordinateCometric (!right) δ) (1-t)) * (flipFrame right δ)ᵀ at he'
  simpa only [zero_sub,neg_smul,one_smul,Matrix.mul_neg,Matrix.neg_mul] using he'

lemma force_far_end_nonpositive (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (p : TVec)
    {x : ℝ} (hx : 3/4 < x) : force right δ p x ≤ 0 := by
  unfold force
  rw [coordinateCometric_flip_deriv,pairing_matrix_neg]
  change -qform (flipFrame right δ * deriv (coordinateCometric (!right) δ) (1-x) * (flipFrame right δ)ᵀ) p ≤ 0
  rw [qform_congruence]
  have hh := PassageDynamics.force_end_nonnegative (!right) hδ ((flipFrame right δ)ᵀ *ᵥ p) (by linarith : 1-x < 1/4)
  unfold force at hh
  exact neg_nonpos.mpr hh

lemma inverse_jet_zero_nonpositive (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (coordinateCometric right δ 0).det ≠ 0) (z : TVec) :
    pairing (deriv (metricInverse right δ) 0) z z ≤ 0 := by
  rw [metricInverse_endpoint_deriv hd]
  have ha := a_nonneg (0:ℝ)
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero]
  nlinarith [mul_nonneg (mul_nonneg hδ ha) (sq_nonneg (z 0))]

lemma inverse_jet_one_nonnegative (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (coordinateCometric right δ 1).det ≠ 0) (z : TVec) :
    0 ≤ pairing (deriv (metricInverse right δ) 1) z z := by
  rw [metricInverse_first hd]
  simp only [Matrix.neg_mul,pairing_matrix_neg]
  have he := qform_congruence (metricInverse right δ 1) (deriv (coordinateCometric right δ) 1) z
  rw [metricInverse_transpose] at he
  change 0 ≤ -qform (metricInverse right δ 1 * deriv (coordinateCometric right δ) 1 * metricInverse right δ 1) z
  rw [he]
  exact neg_nonneg.mpr (force_far_end_nonpositive right hδ (metricInverse right δ 1 *ᵥ z) (x := 1) (by norm_num))

lemma zeroheight_boundary_nonnegative (right : Bool) {δ t v : ℝ} {u z : TVec}
    (hδ : 0 ≤ δ) (hd : (coordinateCometric right δ t).det ≠ 0)
    (ht : (t = 0 ∧ 0 ≤ v) ∨ (t = 1 ∧ v ≤ 0)) :
    0 ≤ boundaryTerm (deriv (metricInverse right δ) t) (v,u) (0,z) := by
  simp only [boundaryTerm,zero_mul,add_zero]
  rw [show -(1/2:ℝ)*v*pairing (deriv (metricInverse right δ) t) z z = -(v/2*pairing (deriv (metricInverse right δ) t) z z) by ring]
  rcases ht with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (inverse_jet_zero_nonpositive right hδ hd z))
  · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (inverse_jet_one_nonnegative right hδ hd z))

lemma zeroheight_boundary_nonpositive (right : Bool) {δ t v : ℝ} {u z : TVec}
    (hδ : 0 ≤ δ) (hd : (coordinateCometric right δ t).det ≠ 0)
    (ht : (t = 0 ∧ v ≤ 0) ∨ (t = 1 ∧ 0 ≤ v)) :
    boundaryTerm (deriv (metricInverse right δ) t) (v,u) (0,z) ≤ 0 := by
  simp only [boundaryTerm,zero_mul,add_zero]
  rw [show -(1/2:ℝ)*v*pairing (deriv (metricInverse right δ) t) z z = -(v/2*pairing (deriv (metricInverse right δ) t) z z) by ring]
  rcases ht with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos (by linarith) (inverse_jet_zero_nonpositive right hδ hd z))
  · exact neg_nonpos.mpr (mul_nonneg (by positivity) (inverse_jet_one_nonnegative right hδ hd z))
end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

lemma neck_enter_upper_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (ha : t a = 1) (hpos : ∀ s ∈ Ioo a b, t s < 1) : v a < 0 := by
  have hh := scalar_enter_transverse (t := fun s => 1-t s) (v := fun s => -v s)
    (F := fun x => -force right δ p (1-x)) hab (by norm_num : (0:ℝ) < 1/4)
    (fun s hs => by simpa using (ht s hs).const_sub 1)
    (fun s hs => by convert (hv s hs).neg using 1 ; first | rfl | simp [neg_div])
    (by simp [ha]) (fun s hs => by linarith [hpos s hs])
    (fun x hx => neg_nonneg.mpr (force_far_end_nonpositive right hδ p (by linarith : 3/4 < 1-x)))
  linarith

lemma neck_exit_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (hr : ∀ s ∈ Ioo a b, t s ∈ Ioo (0:ℝ) 1) (hb : t b = 0 ∨ t b = 1) :
    (t b = 0 ∧ v b < 0) ∨ (t b = 1 ∧ 0 < v b) := by
  have href (s : ℝ) (hs : s ∈ Icc a b) : a+b-s ∈ Icc a b := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hdt (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun r => t (a+b-r)) (-v (a+b-s)) s := by
    convert (ht _ (href s hs)).comp s ((hasDerivAt_id s).const_sub (a+b)) using 1 <;> first | rfl | simp
  have hdv (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun r => -v (a+b-r)) (-force right δ p (t (a+b-s))/2) s := by
    convert ((hv _ (href s hs)).comp s ((hasDerivAt_id s).const_sub (a+b))).neg using 1 <;> first | rfl | simp [neg_div]
  rcases hb with hb | hb
  · left
    refine ⟨hb,?_⟩
    have hh := neck_enter_transverse right hδ hab hdt hdv (by simpa using hb)
      (fun s hs => (hr (a+b-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩).1)
    simpa using hh
  · right
    refine ⟨hb,?_⟩
    have hh := neck_enter_upper_transverse right hδ hab hdt hdv (by simpa using hb)
      (fun s hs => (hr (a+b-s) ⟨by linarith [hs.2],by linarith [hs.1]⟩).2)
    simpa using hh
end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

theorem framed_monotone_index (right : Bool) {δ a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : SmoothFieldOn γ J U) {p : TVec}
    (hp : ∀ s ∈ Icc a b, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p)
    (hrc : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo a b, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0)
    (hb : (γ b 0 = 0 ∨ γ b 0 = 1) ∨ J =ᶠ[𝓝 b] 0)
    (hn : ∀ s ∈ Ioo a b, deriv γ s 0 ≠ 0)
    (hunit : ∀ s ∈ Icc a b,
      (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  have hgc (s : ℝ) (hs : s ∈ Icc a b) :=
    (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub hs))
  have ht (s : ℝ) (hs : s ∈ Icc a b) : HasDerivAt (fun r => γ r 0) (deriv γ s 0) s :=
    hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0
  have hv (s : ℝ) (hs : s ∈ Icc a b) :=
    framed_scalar_equation right hδ hU hγ (hsub hs) (hrc s hs) (hp s hs)
  have hentry : γ a 0 = 0 ∨ γ a 0 = 1 →
      (γ a 0 = 0 ∧ 0 < deriv γ a 0) ∨ (γ a 0 = 1 ∧ deriv γ a 0 < 0) := by
    rintro (hz | ho)
    · exact Or.inl ⟨hz,neck_enter_transverse right hδ.1.le hab ht hv hz (fun s hs => (hr s hs).1)⟩
    · exact Or.inr ⟨ho,neck_enter_upper_transverse right hδ.1.le hab ht hv ho (fun s hs => (hr s hs).2)⟩
  have hexit := neck_exit_transverse right hδ.1.le hab ht hv hr
  have hreg : ∀ s ∈ Icc a b, deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | has
    · rcases ha with ha | hz
      · rcases hentry ha with ⟨_,hv⟩ | ⟨_,hv⟩
        · exact Or.inl hv.ne'
        · exact Or.inl hv.ne
      · exact Or.inr hz
    rcases eq_or_lt_of_le hs.2 with rfl | hsb
    · rcases hb with hb | hz
      · rcases hexit hb with ⟨_,hv⟩ | ⟨_,hv⟩
        · exact Or.inl hv.ne
        · exact Or.inl hv.ne'
      · exact Or.inr hz
    exact Or.inl (hn s ⟨has,hsb⟩)
  obtain ⟨V,hV,hsubV,hVU,hgauge,hzero⟩ := regular_gauge_neighborhood hU
    (euclidean_curve_smooth hγ.1) (euclidean_field_smooth hU hγ.1 hJ) hsub hreg
  have hγV : IsGeodesicOn (framedNeck right hδ) γ V :=
    ⟨hγ.1.mono hVU,fun c hc s hs hsc => hγ.2 c hc s (hVU hs) hsc⟩
  apply framed_gauge_index_nonnegative right hδ hV hγV
    ((euclidean_field_smooth hU hγ.1 hJ).mono hVU) hgauge hzero hab.le hsubV hrc hunit
  let B (s : ℝ) := boundaryTerm (deriv (metricInverse right δ) (γ s 0))
    (splitVector (deriv γ s)) (splitVector (gaugeField γ J s))
  have hsplit (s : ℝ) (hs : s ∈ Icc a b) : splitVector (gaugeField γ J s) = (0,(splitVector (gaugeField γ J s)).2) := by
    apply Prod.ext
    · exact hzero s (hsubV hs)
    · rfl
  have hBa : 0 ≤ B a := by
    rcases ha with ha | hz
    · dsimp only [B]
      rw [hsplit a (left_mem_Icc.mpr hab.le)]
      apply zeroheight_boundary_nonnegative right hδ.1.le (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (hrc a (left_mem_Icc.mpr hab.le)))
      rcases hentry ha with ⟨ht,hv⟩ | ⟨ht,hv⟩
      · exact Or.inl ⟨ht,hv.le⟩
      · exact Or.inr ⟨ht,hv.le⟩
    · have hz' := (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds
      simp [B,hz',splitVector,boundaryTerm,pairing]
  have hBb : B b ≤ 0 := by
    rcases hb with hb | hz
    · dsimp only [B]
      rw [hsplit b (right_mem_Icc.mpr hab.le)]
      apply zeroheight_boundary_nonpositive right hδ.1.le (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (hrc b (right_mem_Icc.mpr hab.le)))
      rcases hexit hb with ⟨ht,hv⟩ | ⟨ht,hv⟩
      · exact Or.inl ⟨ht,hv.le⟩
      · exact Or.inr ⟨ht,hv.le⟩
    · have hz' := (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds
      simp [B,hz',splitVector,boundaryTerm,pairing]
  exact hBb.trans hBa
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

def toRight (δ : ℝ) (x : E3) : E3 := (fromRightLinear δ).symm (x - ![1,0,0])
lemma fromRight_toRight (δ : ℝ) (x : E3) : fromRight δ (toRight δ x) = x := by
  change fromRightLinear δ ((fromRightLinear δ).symm (x - ![1,0,0])) + ![1,0,0] = x
  rw [ContinuousLinearEquiv.apply_symm_apply,sub_add_cancel]
lemma toRight_height (δ : ℝ) (x : E3) : toRight δ x 0 = 1-x 0 := by
  change -(x 0-1) = 1-x 0
  ring
lemma toRight_smooth (δ : ℝ) : ContDiff ℝ ∞ (toRight δ) :=
  (fromRightLinear δ).symm.contDiff.comp (contDiff_id.sub contDiff_const)

theorem right_frame_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ J : ℝ → E3}
    (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U) :
    ∃ η V : ℝ → E3, IsGeodesicOn (framedNeck true hδ) η U ∧ SmoothFieldOn η V U ∧
      (∀ s, η s 0 = 1-γ s 0) ∧
      (∀ s ∈ U, indexPairDensity (framedNeck true hδ) η V V s =
        indexPairDensity (normalizedNeck hδ) γ J J s) ∧
      (∀ s, J s = 0 → V s = 0) ∧
      (∀ s ∈ U, (framedNeck true hδ).inner (η s) (velocity η s) (velocity η s) =
        (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s)) := by
  let R := fromRightIsometry hδ
  let η := toRight δ ∘ γ
  have he : fromRight δ ∘ η = γ := by funext s; exact fromRight_toRight δ (γ s)
  have hη : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ η U :=
    contMDiffOn_iff_contDiffOn.mpr ((toRight_smooth δ).comp_contDiffOn (euclidean_curve_smooth hγ.1))
  have hηR : MapsTo η U R.domain := fun _ _ => mem_univ _
  have hg : IsGeodesicOn (normalizedRight hδ) η U :=
    R.geodesic_reflect hU hη hηR (by simpa only [he] using hγ)
  have hf : SmoothFieldOn (fromRight δ ∘ η) J U :=
    smoothField_curve_congrOn hU hγ.1 (fun s _ => (congrFun he s).symm) (fun _ _ => rfl) hJ
  let V := R.unmapField η J
  have hV := R.unmapField_smooth hU hη hηR hf
  refine ⟨η,V,hg,hV,fun s => toRight_height δ (γ s),?_,?_,?_⟩
  · intro s hs
    have hm : R.mapField η V = J := by funext r; exact R.map_unmap J (mem_univ _)
    have h := R.indexPairDensity_map hU hη hηR hV hV hs
    rw [he,hm] at h
    exact h.symm
  · intro s hs
    exact (congrArg (mfderiv I3 I3 (fromRight δ) (η s)).inverse hs).trans
      ((mfderiv I3 I3 (fromRight δ) (η s)).inverse.map_zero)
  · intro s hs
    have hv := R.velocity_map (hη.contMDiffAt (hU.mem_nhds hs)) (hηR hs)
    rw [he] at hv
    change (normalizedRight hδ).inner (η s) (velocity η s) (velocity η s) = _
    rw [hv,← congrFun he s]
    exact (R.metric (η s) (hηR hs) (velocity η s) (velocity η s)).symm
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

def PassageBounds (C δ : ℝ) : Prop :=
  ∀ right : Bool, ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
    (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
    sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
    0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
    sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q

lemma const_on_closed_of_deriv_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {a b : ℝ} (hab : a ≤ b) (hf : ∀ s ∈ Icc a b, HasDerivAt f 0 s) :
    ∀ s ∈ Icc a b, f s = f a := by
  intro s hs
  have hn := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hf r hr).hasDerivWithinAt) (C := 0) (by simp) (left_mem_Icc.mpr hab) hs
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using hn

lemma framed_closed_momentum (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (ht : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1) :
    ∃ p : TVec, ∀ s ∈ Icc a b, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p :=
  ⟨_,const_on_closed_of_deriv_zero hab
    (fun s hs => framed_momentum_hasDerivAt right hδ hU hγ (hsub hs) (ht s hs))⟩

lemma framed_unit_entry_zero_index (right : Bool) {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (h0 : γ 0 0 = 0) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (framedNeck right hδ) γ J J s := by
  obtain ⟨p,hp⟩ := framed_closed_momentum right hδ hU hγ hL.le hsub hrc
  by_cases hc : ∃ c ∈ Ioo 0 L, deriv γ c 0 = 0
  · obtain ⟨c,hc,hvc⟩ := hc
    exact framed_turn_index right hδ hC hsmall (hB right) hU hsub hc hγ hJ hp h0 hrc hend hvc hr hunit
  · exact framed_monotone_index right hδ hU hL hsub hγ hJ hp hrc hr
      (Or.inl (Or.inl h0)) hend (fun s hs hzero => hc ⟨s,hs,hzero⟩) hunit

lemma unit_entry_index {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (h0 : γ 0 0 = 0 ∨ γ 0 0 = 1) (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (hend : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (normalizedNeck hδ) γ J J s := by
  rcases h0 with h0 | h0
  · exact framed_unit_entry_zero_index false hδ hC hsmall hB hU hL hsub hγ hJ h0 hrc hr hend hunit
  obtain ⟨η,V,hη,hV,hheight,hindex,hzero,henergy⟩ := right_frame_lift hδ hU hγ hJ
  have hV0 : J =ᶠ[𝓝 L] 0 → V =ᶠ[𝓝 L] 0 := by
    intro hz
    filter_upwards [hz] with s hs
    exact hzero s hs
  have hv := framed_unit_entry_zero_index true hδ hC hsmall hB hU hL hsub hη hV
    (by rw [hheight,h0]; ring)
    (fun s hs => by rw [hheight]; constructor <;> linarith [(hrc s hs).1,(hrc s hs).2])
    (fun s hs => by rw [hheight]; constructor <;> linarith [(hr s hs).1,(hr s hs).2])
    (by rcases hend with (hz|ho)|hJ0
        · exact Or.inl (Or.inr (by rw [hheight,hz]; ring))
        · exact Or.inl (Or.inl (by rw [hheight,ho]; ring))
        · exact Or.inr (hV0 hJ0))
    (fun s hs => (henergy s (hsub hs)).trans (hunit s hs))
  convert hv using 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact (hindex s (hsub (by simpa only [uIcc_of_le hL.le] using hs))).symm
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_affine_smoothField {γ J : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U) (a k : ℝ) :
    SmoothFieldOn (fun s => γ (a+k*s)) (fun s => J (a+k*s)) ((fun s : ℝ => a+k*s) ⁻¹' U) :=
  euclidean_smoothField ((euclidean_field_smooth hU hγ hJ).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn (fun _ hs => hs))
lemma affine_zero_germ {J : ℝ → E3} {a k s : ℝ} (hz : J =ᶠ[𝓝 (a+k*s)] 0) :
    (fun r => J (a+k*r)) =ᶠ[𝓝 s] 0 :=
  hz.comp_tendsto ((continuous_const.add (continuous_const.mul continuous_id)).tendsto s)
lemma euclidean_affine_speed (g : SmoothMetric E3) {γ : ℝ → E3} {a k s : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) :
    g.inner (γ (a+k*s)) (velocity (fun r => γ (a+k*r)) s) (velocity (fun r => γ (a+k*r)) s) =
      k^2 * g.inner (γ (a+k*s)) (velocity γ (a+k*s)) (velocity γ (a+k*s)) := by
  rw [euclidean_velocity,euclidean_velocity,affine_deriv hγ]
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ (a+k*s))
  change B (k • deriv γ (a+k*s)) (k • deriv γ (a+k*s)) = k^2 * B (deriv γ (a+k*s)) (deriv γ (a+k*s))
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
lemma euclidean_affine_index_integral (g : SmoothMetric E3) {γ J : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) {a k u v : ℝ} (hk : k ≠ 0)
    (hd : ∀ s ∈ uIcc u v, a+k*s ∈ U) :
    (∫ s in u..v, indexPairDensity g (fun r => γ (a+k*r))
      (fun r => J (a+k*r)) (fun r => J (a+k*r)) s) =
      k * ∫ s in (a+k*u)..(a+k*v), indexPairDensity g γ J J s := by
  calc
    _ = ∫ s in u..v, k^2 * indexPairDensity g γ J J (a+k*s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact euclidean_affine_index g
        (((euclidean_curve_smooth hγ).contDiffAt (hU.mem_nhds (hd s hs))).differentiableAt (by simp))
        (((euclidean_field_smooth hU hγ hJ).contDiffAt (hU.mem_nhds (hd s hs))).differentiableAt (by simp))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_mul _ hk a]
      simp only [smul_eq_mul]
      field_simp
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem finite_unit_index {δ C L : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hL : 0 < L) (hsub : Icc 0 L ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hrc : ∀ s ∈ Icc 0 L, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo 0 L, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ 0 0 = 0 ∨ γ 0 0 = 1) ∨ J =ᶠ[𝓝 0] 0)
    (hb : (γ L 0 = 0 ∨ γ L 0 = 1) ∨ J =ᶠ[𝓝 L] 0)
    (hunit : ∀ s ∈ Icc 0 L, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1) :
    0 ≤ ∫ s in (0:ℝ)..L, indexPairDensity (normalizedNeck hδ) γ J J s := by
  rcases ha with ha | ha
  · exact unit_entry_index hδ hC hsmall hB hU hL hsub hγ hJ ha hrc hr hb hunit
  rcases hb with hb | hb
  swap
  · exact framed_zero_endpoints_index false hδ (fun t ht p => (hB false t ht p).2.2.1)
      hU hγ (euclidean_field_smooth hU hγ.1 hJ) hL.le hsub hrc ha.eq_of_nhds hb.eq_of_nhds
  let A := fun s : ℝ => L+(-1)*s
  have hAc : Continuous A := continuous_const.add (continuous_const.mul continuous_id)
  have hclosed (s : ℝ) (hs : s ∈ Icc 0 L) : A s ∈ Icc 0 L := by
    dsimp only [A]; constructor <;> linarith [hs.1,hs.2]
  have hopen (s : ℝ) (hs : s ∈ Ioo 0 L) : A s ∈ Ioo 0 L := by
    dsimp only [A]; constructor <;> linarith [hs.1,hs.2]
  have hsub' : Icc 0 L ⊆ A ⁻¹' U := fun s hs => hsub (hclosed s hs)
  have hγ' := euclidean_affine_geodesic (normalizedNeck hδ) hU hγ L (-1)
  have hJ' := euclidean_affine_smoothField hU hγ.1 hJ L (-1)
  have hz : (fun s => J (A s)) =ᶠ[𝓝 L] 0 := by
    apply affine_zero_germ
    simpa only [neg_mul,one_mul,add_neg_cancel] using ha
  have hu := unit_entry_index hδ hC hsmall hB (hU.preimage hAc) hL hsub' hγ' hJ'
    (by simpa only [mul_zero,add_zero] using hb)
    (fun s hs => hrc _ (hclosed s hs)) (fun s hs => hr _ (hopen s hs)) (Or.inr hz)
    (fun s hs => by
      have hd : DifferentiableAt ℝ γ (L+(-1)*s) :=
        ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub' hs))).differentiableAt (by simp)
      rw [euclidean_affine_speed _ hd,hunit _ (hclosed s hs)]
      norm_num)
  have he := euclidean_affine_index_integral (normalizedNeck hδ) hU hγ.1 hJ
    (a := L) (k := -1) (u := 0) (v := L) (by norm_num) (fun s hs => hsub' (by simpa only [uIcc_of_le hL.le] using hs))
  rw [he] at hu
  simpa only [mul_zero,add_zero,neg_mul,one_mul,add_neg_cancel,
    intervalIntegral.integral_symm (a := L) (b := 0),neg_neg] using hu
end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_index_nonnegative_zero_velocity (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ)
    (hv : velocity γ s = 0) : 0 ≤ indexPairDensity g γ J J s := by
  rw [euclidean_velocity] at hv
  have hc : curvatureAlong g γ J s = 0 := by
    rw [euclidean_curvature,hv]
    change curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s) (J s) 0 0 = (0:E3)
    ext i
    simp [curvatureTerm]
  unfold indexPairDensity
  rw [hc]
  have hz : g.inner (γ s) (0 : TangentSpace I3 (γ s)) (J s) = 0 := by
    let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ s)
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (J s)) (map_zero B)
  rw [hz,sub_zero]
  exact inner_self_nonneg g _ _
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

theorem finite_neck_index {δ C a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ J : ℝ → E3} (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hrc : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hr : ∀ s ∈ Ioo a b, γ s 0 ∈ Ioo (0:ℝ) 1)
    (ha : (γ a 0 = 0 ∨ γ a 0 = 1) ∨ J =ᶠ[𝓝 a] 0)
    (hb : (γ b 0 = 0 ∨ γ b 0 = 1) ∨ J =ᶠ[𝓝 b] 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (normalizedNeck hδ) γ J J s := by
  let e := (normalizedNeck hδ).inner (γ a) (velocity γ a) (velocity γ a)
  have he : ∀ s ∈ Icc a b, (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s) = e :=
    const_on_closed_of_deriv_zero hab.le (fun s hs => geodesic_speed_hasDerivAt _ hU hγ (hsub hs))
  have he0 : 0 ≤ e := inner_self_nonneg _ _ _
  by_cases hz : e = 0
  · apply intervalIntegral.integral_nonneg hab.le
    intro s hs
    apply euclidean_index_nonnegative_zero_velocity
    by_contra hv
    have hp := (normalizedNeck hδ).pos (γ s) (velocity γ s) hv
    rw [he s hs,hz] at hp
    exact lt_irrefl _ hp
  have hep : 0 < e := lt_of_le_of_ne he0 (Ne.symm hz)
  let k := 1/Real.sqrt e
  let L := (b-a)*Real.sqrt e
  have hroot : 0 < Real.sqrt e := Real.sqrt_pos.mpr hep
  have hk : 0 < k := one_div_pos.mpr hroot
  have hL : 0 < L := mul_pos (sub_pos.mpr hab) hroot
  have hends : a+k*L = b := by dsimp only [k,L]; field_simp; ring
  have hscale : k^2*e = 1 := by
    dsimp only [k]
    field_simp
    exact (Real.sq_sqrt he0).symm
  let A := fun s : ℝ => a+k*s
  have hAc : Continuous A := continuous_const.add (continuous_const.mul continuous_id)
  have hclosed (s : ℝ) (hs : s ∈ Icc 0 L) : A s ∈ Icc a b := by
    dsimp only [A]; constructor <;> nlinarith [mul_nonneg hk.le hs.1,mul_nonneg hk.le (sub_nonneg.mpr hs.2)]
  have hopen (s : ℝ) (hs : s ∈ Ioo 0 L) : A s ∈ Ioo a b := by
    dsimp only [A]; constructor <;> nlinarith [mul_pos hk hs.1,mul_pos hk (sub_pos.mpr hs.2)]
  have hsub' : Icc 0 L ⊆ A ⁻¹' U := fun s hs => hsub (hclosed s hs)
  have hγ' := euclidean_affine_geodesic (normalizedNeck hδ) hU hγ a k
  have hJ' := euclidean_affine_smoothField hU hγ.1 hJ a k
  have hleft : (γ (A 0) 0 = 0 ∨ γ (A 0) 0 = 1) ∨ (fun s => J (A s)) =ᶠ[𝓝 0] 0 := by
    rcases ha with ha | ha
    · exact Or.inl (by simpa only [A,mul_zero,add_zero] using ha)
    · exact Or.inr (affine_zero_germ (by simpa only [mul_zero,add_zero] using ha))
  have hright : (γ (A L) 0 = 0 ∨ γ (A L) 0 = 1) ∨ (fun s => J (A s)) =ᶠ[𝓝 L] 0 := by
    rcases hb with hb | hb
    · exact Or.inl (by simpa only [A,hends] using hb)
    · exact Or.inr (affine_zero_germ (by simpa only [hends] using hb))
  have hu := finite_unit_index hδ hC hsmall hB (hU.preimage hAc) hL hsub' hγ' hJ'
    (fun s hs => hrc _ (hclosed s hs)) (fun s hs => hr _ (hopen s hs)) hleft hright
    (fun s hs => by
      have hd : DifferentiableAt ℝ γ (a+k*s) :=
        ((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsub' hs))).differentiableAt (by simp)
      rw [euclidean_affine_speed _ hd,he _ (hclosed s hs)]
      exact hscale)
  rw [euclidean_affine_index_integral _ hU hγ.1 hJ hk.ne'
    (fun s hs => hsub' (by simpa only [uIcc_of_le hL.le] using hs)),mul_zero,add_zero,hends] at hu
  exact nonneg_of_mul_nonneg_right hu hk

theorem actual_finite_neck_index {δ C a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hab : a < b) (hsub : Icc a b ⊆ U)
    {γ : ℝ → GluedConstruction.Manifold} {J : ℝ → E3}
    (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) (hJ : SmoothFieldOn γ J U)
    (hr : ∀ s ∈ Ioo a b, γ s ∈ openNeck)
    (ha : γ a ∉ openNeck ∨ J =ᶠ[𝓝 a] 0) (hb : γ b ∉ openNeck ∨ J =ᶠ[𝓝 b] 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (realCompactMetric hδ) γ J J s := by
  obtain ⟨W,η,V,hW,_,hcc,_,hη,hV,hh,hi,hz⟩ := actual_finite_neck_lift hδ hU hγ hab hsub hr hJ
  obtain ⟨ht,hleft,hright⟩ := finite_neck_height_boundary hδ hU hγ hab hsub hr
  have hzero (s : ℝ) (hs : s ∈ Icc a b) (hJs : J =ᶠ[𝓝 s] 0) : V =ᶠ[𝓝 s] 0 := by
    filter_upwards [hW.mem_nhds (hcc hs),hJs] with r hrw hrj
    exact hz r hrw hrj
  have he := finite_neck_index hδ hC hsmall hB hW hab hcc hη hV
    (fun s hs => by rw [hh s (hcc hs)]; exact ht s hs)
    (fun s hs => by
      rw [hh s (hcc (Ioo_subset_Icc_self hs))]
      exact (neckPosition_mem_iff δ (closure_openNeck_subset_extended (subset_closure (hr s hs)))).mpr (hr s hs))
    (by rcases ha with ha | ha
        · exact Or.inl (by rw [hh a (hcc (left_mem_Icc.mpr hab.le))]; exact hleft ha)
        · exact Or.inr (hzero a (left_mem_Icc.mpr hab.le) ha))
    (by rcases hb with hb | hb
        · exact Or.inl (by rw [hh b (hcc (right_mem_Icc.mpr hab.le))]; exact hright hb)
        · exact Or.inr (hzero b (right_mem_Icc.mpr hab.le) hb))
  convert he using 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact (hi s (hcc (by simpa only [uIcc_of_le hab.le] using hs))).symm
end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma compact_interval_window {K U : Set ℝ} (hK : IsCompact K) (hKn : K.Nonempty)
    (hU : IsOpen U) (hUc : OrdConnected U) (hKU : K ⊆ U) :
    ∃ A B : ℝ, A < B ∧ K ⊆ Ioo A B ∧ Icc A B ⊆ U := by
  obtain ⟨a,ha⟩ := hK.exists_isLeast hKn
  obtain ⟨b,hb⟩ := hK.exists_isGreatest hKn
  obtain ⟨A,B,hAa,hbB,hAB⟩ := IndexForm.interval_enlargement hU hUc (hKU ha.1) (hKU hb.1)
  exact ⟨A,B,hAa.trans_le ((ha.2 hb.1).trans hbB.le),fun s hs => ⟨hAa.trans_le (ha.2 hs),(hb.2 hs).trans_lt hbB⟩,hAB⟩

theorem realCompactMetric_nonnegative_index {δ C : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ)
    {U : Set ℝ} (hU : IsOpen U) (hUc : OrdConnected U)
    {γ : ℝ → GluedConstruction.Manifold} (hγ : IsGeodesicOn (realCompactMetric hδ) γ U) :
    NonnegativeIndexOn (realCompactMetric hδ) γ U := by
  intro J hJ hJc hJU
  by_cases hJn : (tsupport J).Nonempty
  swap
  · apply integral_nonneg
    intro s
    have hz : indexPairDensity (realCompactMetric hδ) γ J J s = 0 := by
      by_contra hn
      exact hJn ⟨s,indexPairDensity_support _ γ J J hn⟩
    exact hz.ge
  obtain ⟨A,B,hAB,hcut,hsub⟩ := compact_interval_window hJc hJn hU hUc hJU
  let P := Ioo A B ∩ γ ⁻¹' openNeck
  have hγAB : ContinuousOn γ (Ioo A B) := hγ.1.continuousOn.mono (Ioo_subset_Icc_self.trans hsub)
  have hP : IsOpen P := hγAB.isOpen_inter_preimage isOpen_Ioo openNeck_isOpen
  have hzero (s : ℝ) (hs : s ∉ Ioo A B) : J =ᶠ[𝓝 s] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun hx => hs (hcut hx))
  apply GlobalAssembly.integral_nonneg_of_passages hP
    (indexPairDensity_integrable _ hU hγ.1 hJ hJ hJc hJU)
  · intro x hx
    obtain ⟨a,b,hab,hAa,hbB,hcomp,ha,hb⟩ := FinitePassage.bounded_component hP inter_subset_left hx
    have hrange : ∀ s ∈ Ioo a b, γ s ∈ openNeck := by
      intro s hs
      exact (connectedComponentIn_subset P x (hcomp.symm.subset hs)).2
    have he := FinitePassage.endpoint_alternative hab hAa hbB hrange (hγ.1.continuousOn.mono hsub) ha hb
    have hi := actual_finite_neck_index hδ hC hsmall hB hU hab
      ((Icc_subset_Icc hAa hbB).trans hsub) hγ hJ hrange
      (by rcases he.1 with he | he
          · exact Or.inr (hzero a (by rw [he]; simp))
          · exact Or.inl he.2)
      (by rcases he.2 with he | he
          · exact Or.inr (hzero b (by rw [he]; simp))
          · exact Or.inl he.2)
    rw [hcomp]
    simpa only [intervalIntegral.integral_of_le hab.le,integral_Ioc_eq_integral_Ioo] using hi
  · intro s hs
    by_cases hin : s ∈ Ioo A B
    · exact indexPairDensity_nonneg_of_nonpositiveAt _ J
        (hγ.1.contMDiffAt (hU.mem_nhds (hsub (Ioo_subset_Icc_self hin))))
        (realCompactMetric_nonpositive_off_neck hδ (γ s) (fun hh => hs ⟨hin,hh⟩))
    · have hd : indexPairDensity (realCompactMetric hδ) γ J J s = 0 := by
        by_contra hn
        exact hin (hcut (indexPairDensity_support _ γ J J hn))
      exact hd.ge

theorem realCompactMetric_noConjugatePoints {δ C : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hC : 18 ≤ C) (hsmall : SmallParameter (3*C) (sourceMixed C) δ) (hB : PassageBounds C δ) :
    NoConjugatePoints (realCompactMetric hδ) := by
  apply noConjugatePoints_of_intrinsic_index
  intro U hU hUc γ hγ
  exact realCompactMetric_nonnegative_index hδ hC hsmall hB hU hUc hγ

theorem exists_uniform_compact_noConjugatePoints : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1/2 ∧
    ∀ δ (hδ : δ ∈ Ioc (0:ℝ) (1/2)), δ ≤ δ₀ → NoConjugatePoints (realCompactMetric hδ) := by
  obtain ⟨δ₀,C,hδ₀,hhalf,hC,hbounds⟩ := uniform_turning_parameters
  refine ⟨δ₀,hδ₀,hhalf,?_⟩
  intro δ hδ hsmall
  obtain ⟨hs,hB⟩ := hbounds δ ⟨hδ.1,hsmall⟩
  exact realCompactMetric_noConjugatePoints hδ hC hs hB
end ThreeManifold.CompactMetric

end

end OAI
