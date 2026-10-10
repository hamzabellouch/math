import Mathlib

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
abbrev ProfilePlane := ℝ × ℝ
abbrev ProfileLattice := ℤ × ℤ

def profileLatticePoint (k : ProfileLattice) : ProfilePlane := (k.1,k.2)

lemma profileLatticePoint_add (k l : ProfileLattice) :
    profileLatticePoint (k+l) = profileLatticePoint k + profileLatticePoint l := by
  ext <;> simp [profileLatticePoint]

lemma profileLattice_embedding : IsClosedEmbedding profileLatticePoint :=
  Int.isClosedEmbedding_coe_real.prodMap Int.isClosedEmbedding_coe_real

theorem profile_translates_locallyFinite (f : ProfilePlane → ℝ) (hf : HasCompactSupport f) :
    LocallyFinite (fun k : ProfileLattice => support (fun x => f (x-profileLatticePoint k))) := by
  obtain ⟨R,hR⟩ := hf.isCompact.isBounded.subset_closedBall (0 : ProfilePlane)
  intro x
  refine ⟨ball x 1, ball_mem_nhds x zero_lt_one, ?_⟩
  have hfin : (profileLatticePoint ⁻¹' closedBall (0 : ProfilePlane) (‖x‖+1+R)).Finite :=
    (profileLattice_embedding.isCompact_preimage (isCompact_closedBall _ _)).finite_of_discrete
  apply hfin.subset
  rintro k ⟨y,hy,hyx⟩
  have hr : ‖y-profileLatticePoint k‖ ≤ R := by
    simpa only [mem_closedBall,dist_zero_right] using hR (subset_closure hy)
  have hyb : ‖y‖ < ‖x‖+1 := by
    have hh : ‖y‖ ≤ ‖y-x‖ + ‖x‖ := by
      calc
        ‖y‖ = ‖(y-x)+x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y-x‖+‖x‖ := norm_add_le _ _
    rw [mem_ball,dist_eq_norm] at hyx
    linarith
  simp only [mem_preimage,mem_closedBall,dist_zero_right]

  calc
    ‖profileLatticePoint k‖ = ‖y-(y-profileLatticePoint k)‖ := by congr 1; abel
    _ ≤ ‖y‖ + ‖y-profileLatticePoint k‖ := norm_sub_le _ _
    _ ≤ ‖x‖+1+R := by linarith

def profilePeriodize (f : ProfilePlane → ℝ) (x : ProfilePlane) : ℝ :=
  ∑ᶠ k : ProfileLattice, f (x-profileLatticePoint k)

theorem profilePeriodize_smooth (f : ProfilePlane → ℝ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (profilePeriodize f) := by
  rw [← contMDiff_iff_contDiff]
  exact contMDiff_finsum (fun k => contMDiff_iff_contDiff.mpr
    (hs.comp (contDiff_id.sub contDiff_const))) (profile_translates_locallyFinite f hf)

theorem profilePeriodize_periodic (f : ProfilePlane → ℝ) (x : ProfilePlane) (l : ProfileLattice) :
    profilePeriodize f (x+profileLatticePoint l) = profilePeriodize f x := by
  unfold profilePeriodize
  rw [← finsum_comp_equiv (Equiv.addRight l)]
  apply finsum_congr
  intro k
  change f (x+profileLatticePoint l-profileLatticePoint (k+l)) = _
  rw [profileLatticePoint_add]
  congr 1
  abel


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

def radialPrimitive (β : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0:ℝ)..s, β t

lemma radialPrimitive_hasDeriv (β : ℝ → ℝ) (hβ : Continuous β) (s : ℝ) :
    HasDerivAt (radialPrimitive β) (β s) s :=
  (hβ.integral_hasStrictDerivAt 0 s).hasDerivAt

lemma radialPrimitive_smooth (β : ℝ → ℝ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (radialPrimitive β) := by
  rw [contDiff_infty_iff_deriv]
  have hd : deriv (radialPrimitive β) = β := funext fun s => (radialPrimitive_hasDeriv β hβ.continuous s).deriv
  refine ⟨fun s => (radialPrimitive_hasDeriv β hβ.continuous s).differentiableAt, ?_⟩
  rw [hd]
  exact hβ

lemma radialPrimitive_zero {β : ℝ → ℝ} {a s : ℝ} (ha : 0 ≤ a)
    (hβ : ∀ t, t ≤ a → β t = 0) (hs : s ≤ a) : radialPrimitive β s = 0 := by
  unfold radialPrimitive
  calc
    _ = ∫ _ in (0:ℝ)..s, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hβ t ((le_max_iff.mp ht.2).elim (fun h => h.trans ha) (fun h => h.trans hs))
    _ = 0 := intervalIntegral.integral_zero

lemma radialPrimitive_constant {β : ℝ → ℝ} (hβ : Continuous β) {b s : ℝ}
    (hzero : ∀ t, b ≤ t → β t = 0) (hs : b ≤ s) :
    radialPrimitive β s = radialPrimitive β b := by
  have hI : ∫ t in b..s, β t = 0 := by
    calc
      _ = ∫ _ in b..s, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc b s := by simpa only [uIcc_of_le hs] using ht
        exact hzero t ht'.1
      _ = 0 := intervalIntegral.integral_zero
  have hh := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (hβ.intervalIntegrable 0 b) (hβ.intervalIntegrable b s)
  simpa only [radialPrimitive,hI,add_zero] using hh.symm

theorem exists_radial_derivative {a b : ℝ} (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo a b ∧ (∀ t, β t ∈ Icc 0 1) ∧ β ((a+b)/2) = 1 := by
  obtain ⟨β,hsub,hcompact,hs,hr,hc⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (isOpen_Ioo.mem_nhds (show (a+b)/2 ∈ Ioo a b by constructor <;> linarith))
  exact ⟨β,hs,hcompact,hsub,fun t => hr (mem_range_self t),hc⟩

def radialSquaredBase (β : ℝ → ℝ) (b : ℝ) (x : ProfilePlane) : ℝ :=
  radialPrimitive β (x.1^2+x.2^2) - radialPrimitive β b

lemma radialSquaredBase_smooth (β : ℝ → ℝ) (b : ℝ) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (radialSquaredBase β b) :=
  ((radialPrimitive_smooth β hβ).comp
    ((contDiff_fst.pow 2).add (contDiff_snd.pow 2))).sub contDiff_const

lemma radialSquaredBase_zero {β : ℝ → ℝ} (hβ : Continuous β) {b : ℝ}
    (hzero : ∀ t, b ≤ t → β t = 0) (x : ProfilePlane) (hx : b ≤ x.1^2+x.2^2) :
    radialSquaredBase β b x = 0 := by
  simp [radialSquaredBase,radialPrimitive_constant hβ hzero hx]

lemma radialSquaredBase_compact {β : ℝ → ℝ} (hβ : Continuous β) {b R : ℝ}
    (hR : 0 ≤ R) (hb : b ≤ R^2) (hzero : ∀ t, b ≤ t → β t = 0) :
    HasCompactSupport (radialSquaredBase β b) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ProfilePlane) R)
  intro x hx
  apply radialSquaredBase_zero hβ hzero x
  have hxn : R < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  rw [Prod.norm_def,lt_max_iff] at hxn
  rcases hxn with hx | hx
  · rw [Real.norm_eq_abs] at hx
    have hsq : R^2 < x.1^2 := by nlinarith [sq_abs x.1]
    nlinarith [sq_nonneg x.2]
  · rw [Real.norm_eq_abs] at hx
    have hsq : R^2 < x.2^2 := by nlinarith [sq_abs x.2]
    nlinarith [sq_nonneg x.1]

theorem radial_periodic_smooth {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {b R : ℝ}
    (hR : 0 ≤ R) (hb : b ≤ R^2) (hzero : ∀ t, b ≤ t → β t = 0) :
    ContDiff ℝ ∞ (fun x : ProfilePlane => radialPrimitive β b +
      profilePeriodize (radialSquaredBase β b) x) := by
  exact contDiff_const.add (profilePeriodize_smooth _
    (radialSquaredBase_compact hβ.continuous hR hb hzero) (radialSquaredBase_smooth β b hβ))


end

section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff
open scoped ContDiff

lemma profileRadiusSquared_hasFDeriv (x : ProfilePlane) :
    HasFDerivAt (fun z : ProfilePlane => z.1^2+z.2^2)
      ((2*x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
       (2*x.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  convert ((hasFDerivAt_fst (𝕜:=ℝ) (p:=x)).pow 2).add
    ((hasFDerivAt_snd (𝕜:=ℝ) (p:=x)).pow 2) using 1
  first | rfl | simp

theorem radialSquaredBase_first {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (b : ℝ) (x v : ProfilePlane) :
    fderiv ℝ (radialSquaredBase β b) x v =
      2*β (x.1^2+x.2^2)*(x.1*v.1+x.2*v.2) := by
  have hh := ((radialPrimitive_hasDeriv β hβ.continuous (x.1^2+x.2^2)).comp_hasFDerivAt x
    (profileRadiusSquared_hasFDeriv x)).sub_const (radialPrimitive β b)
  change HasFDerivAt (radialSquaredBase β b) _ x at hh
  rw [hh.fderiv]
  simp only [_root_.smul_apply,_root_.add_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  ring

theorem radialSquaredBase_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (b : ℝ) (x v w : ProfilePlane) :
    fderiv ℝ (fun z => fderiv ℝ (radialSquaredBase β b) z w) x v =
      4*deriv β (x.1^2+x.2^2)*(x.1*v.1+x.2*v.2)*(x.1*w.1+x.2*w.2) +
      2*β (x.1^2+x.2^2)*(v.1*w.1+v.2*w.2) := by
  have hβd := (hβ.differentiable (by simp) (x.1^2+x.2^2)).hasDerivAt
  have hp := hβd.comp_hasFDerivAt x (profileRadiusSquared_hasFDeriv x)
  have hi := ((hasFDerivAt_fst (𝕜:=ℝ) (p:=x)).mul_const w.1).add
    ((hasFDerivAt_snd (𝕜:=ℝ) (p:=x)).mul_const w.2)
  have hh := (hp.const_mul 2).mul hi
  have he : (fun z => fderiv ℝ (radialSquaredBase β b) z w) =
      (fun z => 2*β (z.1^2+z.2^2)*(z.1*w.1+z.2*w.2)) := by
    funext z; exact radialSquaredBase_first hβ b z w
  rw [he]
  erw [hh.fderiv]
  simp only [_root_.smul_apply,_root_.add_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',Function.comp_apply,Pi.add_apply]
  ring

end

open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Filter Set
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
open Set Filter Function Metric Topology Manifold
open scoped Topology ContDiff
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma profilePeriodize_eventually_zero {f : ProfilePlane → ℝ} {r R : ℝ}
    (hrR : r < R) (hf : ∀ z, r < ‖z‖ → f z = 0) (x : ProfilePlane)
    (hx : ∀ k, R ≤ ‖x-profileLatticePoint k‖) :
    profilePeriodize f =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [ball_mem_nhds x (sub_pos.mpr hrR)] with z hz
  have hd : ‖z-x‖ < R-r := by simpa only [mem_ball,dist_eq_norm] using hz
  have hz0 : ∀ k, f (z-profileLatticePoint k) = 0 := by
    intro k
    apply hf
    have ht : ‖x-profileLatticePoint k‖ ≤ ‖z-x‖+‖z-profileLatticePoint k‖ := by
      calc
        _ = ‖(x-z)+(z-profileLatticePoint k)‖ := by congr 1; abel
        _ ≤ ‖x-z‖+‖z-profileLatticePoint k‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev x z]
    linarith only [ht,hd,hx k]
  simp [profilePeriodize,hz0]

lemma profilePeriodize_jets_zero {f : ProfilePlane → ℝ} {r R : ℝ}
    (hrR : r < R) (hf : ∀ z, r < ‖z‖ → f z = 0) (x : ProfilePlane)
    (hx : ∀ k, R ≤ ‖x-profileLatticePoint k‖) :
    fderiv ℝ (profilePeriodize f) x = 0 ∧
    fderiv ℝ (fderiv ℝ (profilePeriodize f)) x = 0 := by
  have he := profilePeriodize_eventually_zero hrR hf x hx
  constructor
  · simpa using he.fderiv_eq (𝕜 := ℝ)
  · simpa using (he.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

def planeRadialCovector (z : ProfilePlane) : ProfilePlane →L[ℝ] ℝ :=
  if z = 0 then ContinuousLinearMap.fst ℝ ℝ ℝ else
    (z.1/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (z.2/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ

def planeAngularCovector (z : ProfilePlane) : ProfilePlane →L[ℝ] ℝ :=
  if z = 0 then ContinuousLinearMap.snd ℝ ℝ ℝ else
    (-z.2/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    (z.1/Real.sqrt (z.1^2+z.2^2)) • ContinuousLinearMap.snd ℝ ℝ ℝ

lemma plane_radius_pos {z : ProfilePlane} (hz : z ≠ 0) :
    0 < Real.sqrt (z.1^2+z.2^2) := by
  apply Real.sqrt_pos.mpr
  have hp : 0 ≤ z.1^2+z.2^2 := by positivity
  apply lt_of_le_of_ne hp
  intro he
  apply hz
  ext <;> simp only [Prod.fst_zero,Prod.snd_zero]
  · nlinarith only [sq_nonneg z.2,he]
  · nlinarith only [sq_nonneg z.1,he]

lemma plane_radial_angular_sq (z v : ProfilePlane) :
    (planeRadialCovector z v)^2+(planeAngularCovector z v)^2 = v.1^2+v.2^2 := by
  by_cases hz : z = 0
  · simp [planeRadialCovector,planeAngularCovector,hz]
  · have hs := plane_radius_pos hz
    have hs2 := Real.sq_sqrt (show 0 ≤ z.1^2+z.2^2 by positivity)
    simp only [planeRadialCovector,planeAngularCovector,ite_eq_right hz,
      _root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    field_simp
    rw [hs2]
    ring

lemma radialSquaredBase_radial_first {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (b : ℝ) (z v : ProfilePlane) :
    fderiv ℝ (radialSquaredBase β b) z v =
      (2*Real.sqrt (z.1^2+z.2^2)*β (z.1^2+z.2^2))*planeRadialCovector z v := by
  rw [radialSquaredBase_first hβ]
  by_cases hz : z = 0
  · simp [hz,hβ0]
  · have hs := plane_radius_pos hz
    simp only [planeRadialCovector,ite_eq_right hz,_root_.add_apply,
      _root_.smul_apply,ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd',smul_eq_mul]
    field_simp

lemma radialSquaredBase_radial_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) (b : ℝ) (z v w : ProfilePlane) :
    fderiv ℝ (fun p => fderiv ℝ (radialSquaredBase β b) p w) z v =
      (2*β (z.1^2+z.2^2)+4*(z.1^2+z.2^2)*deriv β (z.1^2+z.2^2))*
        planeRadialCovector z v*planeRadialCovector z w+
      (2*β (z.1^2+z.2^2))*planeAngularCovector z v*planeAngularCovector z w := by
  rw [radialSquaredBase_second hβ]
  by_cases hz : z = 0
  · simp [hz,hβ0]
  · have hs := plane_radius_pos hz
    have hs2 := Real.sq_sqrt (show 0 ≤ z.1^2+z.2^2 by positivity)
    simp only [planeRadialCovector,planeAngularCovector,ite_eq_right hz,
      _root_.add_apply,_root_.smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    field_simp
    rw [hs2]
    ring



end YauCounterexamples
end

end OAI
