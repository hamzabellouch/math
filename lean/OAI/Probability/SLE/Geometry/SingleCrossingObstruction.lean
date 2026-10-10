import OAI.Probability.SLE.Geometry.LocalLogObstruction
import OAI.Probability.SLE.Geometry.RectangleLogBoundary
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! The local crossing obstruction in the parameter square. Clamping
extends the difference map to the plane; the four-side logarithm supplies
its outer boundary logarithm. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

def unitClamp (x : ℝ) : unitInterval := projIcc 0 1 zero_le_one x

lemma continuous_unitClamp : Continuous unitClamp := continuous_projIcc (h := zero_le_one)

@[simp] lemma unitClamp_coe (t : unitInterval) : unitClamp (t:ℝ)=t := projIcc_val zero_le_one t

lemma unitClamp_eq_interior {x : ℝ} {t : unitInterval}
    (ht₀ : 0<(t:ℝ)) (ht₁ : (t:ℝ)<1) (h : unitClamp x=t) : x=(t:ℝ) := by
  have hx₀ : 0<x := by
    by_contra hn
    have he : unitClamp x=0 := projIcc_of_le_left zero_le_one (le_of_not_gt hn)
    rw [he] at h
    have hv := congrArg (fun u : unitInterval => (u:ℝ)) h
    simp only [Set.Icc.coe_zero] at hv
    linarith
  have hx₁ : x<1 := by
    by_contra hn
    have he : unitClamp x=1 := projIcc_of_right_le zero_le_one (le_of_not_gt hn)
    rw [he] at h
    have hv := congrArg (fun u : unitInterval => (u:ℝ)) h
    simp only [Set.Icc.coe_one] at hv
    linarith
  have he : unitClamp x=⟨x,hx₀.le,hx₁.le⟩ := projIcc_of_mem zero_le_one ⟨hx₀.le,hx₁.le⟩
  rw [he] at h
  exact congrArg (fun u : unitInterval => (u:ℝ)) h

def crossingSquareParam (z : ℂ) : unitInterval × unitInterval :=
  (unitClamp z.re,unitClamp z.im)

lemma continuous_crossingSquareParam : Continuous crossingSquareParam :=
  (continuous_unitClamp.comp Complex.continuous_re).prodMk
    (continuous_unitClamp.comp Complex.continuous_im)

def crossingSquareMap (c p : C(unitInterval,ℂ)) (z : ℂ) : ℂ :=
  c (crossingSquareParam z).2-p (crossingSquareParam z).1

lemma continuous_crossingSquareMap (c p : C(unitInterval,ℂ)) : Continuous (crossingSquareMap c p) :=
  (c.continuous.comp (continuous_crossingSquareParam.snd)).sub
    (p.continuous.comp (continuous_crossingSquareParam.fst))

lemma crossingSquareMap_zero_iff (c p : C(unitInterval,ℂ))
    (s t : unitInterval) (hs : 0<(s:ℝ) ∧ (s:ℝ)<1) (ht : 0<(t:ℝ) ∧ (t:ℝ)<1)
    (hcross : c t=p s) (hu : ∀ u v, c v=p u → u=s ∧ v=t) (z : ℂ) :
    crossingSquareMap c p z=0 ↔ z=(s:ℂ)+(t:ℂ)*Complex.I := by
  constructor
  · intro hz
    obtain ⟨hre,him⟩ := hu _ _ (sub_eq_zero.mp hz)
    have hr := unitClamp_eq_interior hs.1 hs.2 hre
    have hi := unitClamp_eq_interior ht.1 ht.2 him
    apply Complex.ext <;> simp [hr,hi]
  · intro hz
    subst z
    simp [crossingSquareMap,crossingSquareParam,hcross]

lemma crossingSquareParam_on_outer_circle (s t : unitInterval) (z : ℂ) (hz : ‖z‖=4) :
    let q := crossingSquareParam (z+((s:ℂ)+(t:ℂ)*Complex.I))
    q.1=0 ∨ q.1=1 ∨ q.2=0 ∨ q.2=1 := by
  dsimp only
  by_contra hn
  push Not at hn
  let a := z+((s:ℂ)+(t:ℂ)*Complex.I)
  let u := unitClamp a.re
  let v := unitClamp a.im
  have hu₀ : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun he => hn.1 (Subtype.ext he.symm))
  have hu₁ : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun he => hn.2.1 (Subtype.ext he))
  have hv₀ : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (fun he => hn.2.2.1 (Subtype.ext he.symm))
  have hv₁ : (v:ℝ)<1 := lt_of_le_of_ne v.property.2 (fun he => hn.2.2.2 (Subtype.ext he))
  have har := unitClamp_eq_interior hu₀ hu₁ (rfl : unitClamp a.re=u)
  have hai := unitClamp_eq_interior hv₀ hv₁ (rfl : unitClamp a.im=v)
  have hre : a.re=z.re+(s:ℝ) := by simp [a]
  have him : a.im=z.im+(t:ℝ) := by simp [a]
  have hr : |z.re|<1 := abs_lt.mpr ⟨by linarith [s.property.2],by linarith [s.property.1]⟩
  have hi : |z.im|<1 := abs_lt.mpr ⟨by linarith [t.property.2],by linarith [t.property.1]⟩
  have hnorm := Complex.norm_le_abs_re_add_abs_im z
  linarith

lemma no_single_locally_injective_crossing (c p : C(unitInterval,ℂ))
    (s t : unitInterval) (hs : 0<(s:ℝ) ∧ (s:ℝ)<1) (ht : 0<(t:ℝ) ∧ (t:ℝ)<1)
    (hcross : c t=p s) (hu : ∀ u v, c v=p u → u=s ∧ v=t)
    (hi : ∃ ρ : ℝ, 0<ρ ∧ InjOn (crossingSquareMap c p)
      (closedBall ((s:ℂ)+(t:ℂ)*Complex.I) ρ))
    (hloop : c 0=c 1) (hbase : ∀ u, c 0-p u≠0)
    (L₀ L₁ : C(unitInterval,ℂ))
    (hL₀ : ∀ u, Complex.exp (L₀ u)=c u-p 0)
    (hL₁ : ∀ u, Complex.exp (L₁ u)=c u-p 1)
    (h₀ : L₀ 0=L₀ 1) (h₁ : L₁ 0=L₁ 1) : False := by
  obtain ⟨K,hK⟩ := rectangle_difference_boundary_log c p hloop hbase L₀ L₁ hL₀ hL₁ h₀ h₁
  let a := (s:ℂ)+(t:ℂ)*Complex.I
  let f := fun z : ℂ => crossingSquareMap c p (z+a)
  have hf : Continuous f := (continuous_crossingSquareMap c p).comp (continuous_id.add continuous_const)
  have hf0 : f 0=0 := by
    simpa only [f,zero_add] using (crossingSquareMap_zero_iff c p s t hs ht hcross hu a).mpr rfl
  have hzero (z : ℂ) : f z=0 → z=0 := by
    intro hz
    have he := (crossingSquareMap_zero_iff c p s t hs ht hcross hu (z+a)).mp hz
    have he' : z+a=0+a := by simpa only [zero_add] using he
    exact add_right_cancel he'
  obtain ⟨ρ,hρ,hiρ⟩ := hi
  let r := min ρ 1
  have hr : 0<r := lt_min hρ zero_lt_one
  have hir : InjOn f (closedBall 0 r) := by
    intro z hz w hw he
    have hm (z : ℂ) (hz : z∈closedBall 0 r) : z+a∈closedBall a ρ := by
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right,sub_zero] using
        (mem_closedBall_zero_iff.mp hz).trans (min_le_left ρ 1)
    exact add_right_cancel (hiρ (hm z hz) (hm w hw) he)
  let L : C(sphere (0:ℂ) 4,ℂ) := K.comp
    ⟨fun z => crossingSquareParam ((z:ℂ)+a),
      continuous_crossingSquareParam.comp (continuous_subtype_val.add continuous_const)⟩
  apply isolated_zero_no_continuous_boundary_log f 4 r (by norm_num) hr
    ((min_le_right ρ 1).trans (by norm_num)) hf.continuousOn
    (fun z _ hz => hzero z (by rwa [hf0] at hz)) hir L
  intro z
  rw [hf0,sub_zero]
  exact hK _ (crossingSquareParam_on_outer_circle s t z
    (by simpa only [mem_sphere,dist_zero_right] using z.property))

end SLEExactGauge

end

end OAI
