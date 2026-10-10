import Mathlib
import OAI.Geometry.SmoothYau.Geometry.ProfilePeriodizeFirst

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
open Set Filter Function Metric Topology Manifold MeasureTheory
open scoped Topology ContDiff

lemma radialSquaredBase_zero_of_norm {β : ℝ → ℝ} (hβ : Continuous β) {b R : ℝ}
    (hR : 0 ≤ R) (hb : b ≤ R^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (x : ProfilePlane) (hx : R < ‖x‖) : radialSquaredBase β b x = 0 := by
  apply radialSquaredBase_zero hβ hzero
  rw [Prod.norm_def,lt_max_iff] at hx
  rcases hx with hx | hx
  · rw [Real.norm_eq_abs] at hx
    have hh : R^2 < x.1^2 := by nlinarith [sq_abs x.1]
    nlinarith [sq_nonneg x.2]
  · rw [Real.norm_eq_abs] at hx
    have hh : R^2 < x.2^2 := by nlinarith [sq_abs x.2]
    nlinarith [sq_nonneg x.1]

theorem radial_periodic_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) {b R : ℝ}
    (hR : 0 ≤ R) (hsmall : 2*R < 1) (hb : b ≤ R^2)
    (hzero : ∀ t, b ≤ t → β t = 0) (k : ProfileLattice) {x : ProfilePlane}
    (hx : ‖x-profileLatticePoint k‖ < R) (v w : ProfilePlane) :
    let z := x-profileLatticePoint k
    fderiv ℝ (fun p => fderiv ℝ (fun q : ProfilePlane => radialPrimitive β b +
      profilePeriodize (radialSquaredBase β b) q) p w) x v =
      4*deriv β (z.1^2+z.2^2)*(z.1*v.1+z.2*v.2)*(z.1*w.1+z.2*w.2) +
      2*β (z.1^2+z.2^2)*(v.1*w.1+v.2*w.2) := by
  dsimp only
  simp only [fderiv_const_add]
  rw [profilePeriodize_second hsmall (radialSquaredBase_zero_of_norm hβ.continuous hR hb hzero)
    (radialSquaredBase_smooth β b hβ) k hx,radialSquaredBase_second hβ]


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

def periodicRadialOffset (R : ℝ) (x : ProfilePlane) : ProfilePlane := by
  classical
  exact if h : ∃ k, ‖x-profileLatticePoint k‖ < R then x-profileLatticePoint h.choose else 0

def periodicRadialFunction (β : ℝ → ℝ) (b : ℝ) (x : ProfilePlane) : ℝ :=
  radialPrimitive β b + profilePeriodize (radialSquaredBase β b) x

def periodicRadialSpeed (β : ℝ → ℝ) (R : ℝ) (x : ProfilePlane) : ℝ :=
  let z := periodicRadialOffset R x
  2*Real.sqrt (z.1^2+z.2^2)*β (z.1^2+z.2^2)

def periodicAngularSecond (β : ℝ → ℝ) (R : ℝ) (x : ProfilePlane) : ℝ :=
  let z := periodicRadialOffset R x
  2*β (z.1^2+z.2^2)

def periodicRadialSecond (β : ℝ → ℝ) (R : ℝ) (x : ProfilePlane) : ℝ :=
  let z := periodicRadialOffset R x
  2*β (z.1^2+z.2^2)+4*(z.1^2+z.2^2)*deriv β (z.1^2+z.2^2)

theorem periodicRadialFunction_first {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hsmall : 2*R < 1) (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (x v : ProfilePlane) :
    fderiv ℝ (periodicRadialFunction β b) x v =
      periodicRadialSpeed β R x * planeRadialCovector (periodicRadialOffset R x) v := by
  unfold periodicRadialFunction
  simp only [fderiv_const_add]
  have hf := radialSquaredBase_zero_of_norm hβ.continuous hr hb hzero
  have hR : 0 ≤ R := hr.trans hrR.le
  have hfR : ∀ z, R < ‖z‖ → radialSquaredBase β b z = 0 :=
    fun z hz => hf z (hrR.trans hz)
  by_cases hx : ∃ k, ‖x-profileLatticePoint k‖ < R
  · simp only [periodicRadialSpeed,periodicRadialOffset,dite_eq_left hx]
    rw [profilePeriodize_first hsmall hfR
      ((radialSquaredBase_smooth β b hβ).differentiable (by simp)) hx.choose hx.choose_spec]
    exact radialSquaredBase_radial_first hβ hβ0 b _ v
  · have hxn : ∀ k, R ≤ ‖x-profileLatticePoint k‖ := by simpa only [not_exists,not_lt] using hx
    have hz := (profilePeriodize_jets_zero hrR hf x hxn).1
    simp [periodicRadialSpeed,periodicRadialOffset,hx,hz]

theorem periodicRadialFunction_second {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβ0 : β 0 = 0) {b r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hsmall : 2*R < 1) (hb : b ≤ r^2) (hzero : ∀ t, b ≤ t → β t = 0)
    (x v w : ProfilePlane) :
    fderiv ℝ (fun p => fderiv ℝ (periodicRadialFunction β b) p w) x v =
      periodicRadialSecond β R x * planeRadialCovector (periodicRadialOffset R x) v *
        planeRadialCovector (periodicRadialOffset R x) w+
      periodicAngularSecond β R x * planeAngularCovector (periodicRadialOffset R x) v *
        planeAngularCovector (periodicRadialOffset R x) w := by
  unfold periodicRadialFunction
  simp only [fderiv_const_add]
  have hf := radialSquaredBase_zero_of_norm hβ.continuous hr hb hzero
  have hfR : ∀ z, R < ‖z‖ → radialSquaredBase β b z = 0 :=
    fun z hz => hf z (hrR.trans hz)
  by_cases hx : ∃ k, ‖x-profileLatticePoint k‖ < R
  · simp only [periodicRadialSecond,periodicAngularSecond,
      periodicRadialOffset,dite_eq_left hx]
    rw [profilePeriodize_second hsmall hfR
      (radialSquaredBase_smooth β b hβ) hx.choose hx.choose_spec]
    exact radialSquaredBase_radial_second hβ hβ0 b _ v w
  · have hxn : ∀ k, R ≤ ‖x-profileLatticePoint k‖ := by simpa only [not_exists,not_lt] using hx
    have he := profilePeriodize_eventually_zero hrR hf x hxn
    have he' : (fun p => fderiv ℝ (profilePeriodize (radialSquaredBase β b)) p w)
        =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [he.fderiv (𝕜 := ℝ)] with p hp
      simp [hp]
    have hz := congrArg (fun L : ProfilePlane →L[ℝ] ℝ => L v) (he'.fderiv_eq (𝕜 := ℝ))
    simpa [periodicRadialFunction,periodicRadialSecond,periodicAngularSecond,
      periodicRadialOffset,hx,hβ0] using hz

lemma norm_planeRadialCovector_le (z : ProfilePlane) : ‖planeRadialCovector z‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  have hsq := plane_radial_angular_sq z v
  have h1 : |v.1| ≤ ‖v‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_left |v.1| |v.2|
  have h2 : |v.2| ≤ ‖v‖ := by simpa only [Prod.norm_def,Real.norm_eq_abs] using le_max_right |v.1| |v.2|
  rw [Real.norm_eq_abs]
  have hs1 : v.1^2 ≤ ‖v‖^2 := by nlinarith only [h1,sq_abs v.1,norm_nonneg v,abs_nonneg v.1]
  have hs2 : v.2^2 ≤ ‖v‖^2 := by nlinarith only [h2,sq_abs v.2,norm_nonneg v,abs_nonneg v.2]
  nlinarith only [hsq,hs1,hs2,sq_nonneg (planeAngularCovector z v),
    sq_abs (planeRadialCovector z v),abs_nonneg (planeRadialCovector z v),norm_nonneg v]


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

theorem radial_speed_positive_annulus {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {β : ℝ → ℝ} (hβ : Continuous β) (hmid : β ((a+b)/2) = 1) :
    ∃ r₁ r₂ c : ℝ, Real.sqrt a < r₁ ∧ r₁ < r₂ ∧ r₂ < Real.sqrt b ∧ 0 < c ∧
      ∀ s ∈ Ioo r₁ r₂, c ≤ 2*s*β (s^2) := by
  let s₀ := Real.sqrt ((a+b)/2)
  have hmp : 0 < (a+b)/2 := by linarith only [ha,hab]
  have hs₀ : 0 < s₀ := Real.sqrt_pos.mpr hmp
  have hsqa : Real.sqrt a < s₀ := Real.sqrt_lt_sqrt ha.le (by linarith only [hab])
  have hsqb : s₀ < Real.sqrt b := Real.sqrt_lt_sqrt hmp.le (by linarith only [hab])
  have hcont : Continuous (fun s : ℝ => 2*s*β (s^2)) :=
    (continuous_const.mul continuous_id).mul (hβ.comp (continuous_id.pow 2))
  let U := Ioo (Real.sqrt a) (Real.sqrt b) ∩ {s : ℝ | s₀ < 2*s*β (s^2)}
  have hU : IsOpen U := isOpen_Ioo.inter (isOpen_lt continuous_const hcont)
  have hmem : s₀ ∈ U := by
    refine ⟨⟨hsqa,hsqb⟩,?_⟩
    change s₀ < 2*s₀*β ((Real.sqrt ((a+b)/2))^2)
    rw [Real.sq_sqrt hmp.le,hmid,mul_one]
    linarith only [hs₀]
  obtain ⟨l,r,hlr,hsub⟩ := hU.exists_Ioo_subset ⟨s₀,hmem⟩
  have hl : (2*l+r)/3 ∈ Ioo l r := by constructor <;> linarith only [hlr]
  have hr : (l+2*r)/3 ∈ Ioo l r := by constructor <;> linarith only [hlr]
  refine ⟨(2*l+r)/3,(l+2*r)/3,s₀,(hsub hl).1.1,by linarith only [hlr],
    (hsub hr).1.2,hs₀,?_⟩
  intro s hs
  exact (hsub ⟨by linarith only [hl.1,hs.1],by linarith only [hr.2,hs.2]⟩).2.le

lemma periodicRadialOffset_eq {R : ℝ} (hR : 2*R < 1) (k : ProfileLattice)
    {x : ProfilePlane} (hx : ‖x-profileLatticePoint k‖ < R) :
    periodicRadialOffset R x = x-profileLatticePoint k := by
  classical
  have he : ∃ l, ‖x-profileLatticePoint l‖ < R := ⟨k,hx⟩
  have hh : he.choose = k := by
    by_contra hn
    have hsep := profileLattice_separated hn
    have htri : ‖profileLatticePoint he.choose-profileLatticePoint k‖ ≤
        ‖x-profileLatticePoint he.choose‖+‖x-profileLatticePoint k‖ := by
      calc
        _ = ‖(profileLatticePoint he.choose-x)+(x-profileLatticePoint k)‖ := by congr 1; abel
        _ ≤ ‖profileLatticePoint he.choose-x‖+‖x-profileLatticePoint k‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev (profileLatticePoint he.choose) x]
    linarith only [hsep,htri,he.choose_spec,hx,hR]
  simp only [periodicRadialOffset,dite_eq_left he,hh]

lemma plane_norm_le_radius (z : ProfilePlane) :
    ‖z‖ ≤ Real.sqrt (z.1^2+z.2^2) := by
  have hs := Real.sq_sqrt (show 0 ≤ z.1^2+z.2^2 by positivity)
  have hp := Real.sqrt_nonneg (z.1^2+z.2^2)
  rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff]
  constructor
  · nlinarith only [hs,hp,sq_nonneg z.2,sq_abs z.1,abs_nonneg z.1]
  · nlinarith only [hs,hp,sq_nonneg z.1,sq_abs z.2,abs_nonneg z.2]

theorem periodicRadialSpeed_annular_lower {β : ℝ → ℝ} {R r₁ r₂ c : ℝ}
    (hR : 2*R < 1) (hr₂ : r₂ ≤ R)
    (hc : ∀ s ∈ Ioo r₁ r₂, c ≤ 2*s*β (s^2))
    (x : ProfilePlane) (k : ProfileLattice)
    (hx : Real.sqrt ((x-profileLatticePoint k).1^2+(x-profileLatticePoint k).2^2) ∈ Ioo r₁ r₂) :
    c ≤ periodicRadialSpeed β R x := by
  have hn : ‖x-profileLatticePoint k‖ < R :=
    (plane_norm_le_radius _).trans_lt (hx.2.trans_le hr₂)
  unfold periodicRadialSpeed
  rw [periodicRadialOffset_eq hR k hn]
  have hh := hc _ hx
  simpa only [Real.sq_sqrt (show 0 ≤ (x-profileLatticePoint k).1^2+
    (x-profileLatticePoint k).2^2 by positivity)] using hh



end YauCounterexamples
end

end OAI
