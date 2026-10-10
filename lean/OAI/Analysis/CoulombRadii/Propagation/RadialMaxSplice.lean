import Mathlib
import OAI.Analysis.CoulombRadii.Propagation.PropagationBarrierOffset

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
noncomputable section
namespace NeutralAtom

def radialMaxSplice (α β : ℝ) (f g : Position → ℝ) (x : Position) : ℝ :=
  if ‖x‖<α then f x else if ‖x‖<β then max (f x) (g x) else g x

lemma radialMaxSplice_inner {α β a b : ℝ} {f g : Position → ℝ}
    (hbα : b≤α) (haβ : a≤β)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    {x : Position} (hx : ‖x‖<a) : radialMaxSplice α β f g x=f x := by
  unfold radialMaxSplice
  split_ifs with hα hβ
  · rfl
  · exact max_eq_left (hlow x (hbα.trans (le_of_not_gt hα)) hx.le)
  · exact False.elim (hβ (hx.trans_le haβ))

lemma radialMaxSplice_middle {α β a b c e : ℝ} {f g : Position → ℝ}
    (hαa : α≤a) (heβ : e≤β)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖≤c → f x≤g x)
    {x : Position} (hx : b<‖x‖ ∧ ‖x‖<c) : radialMaxSplice α β f g x=max (f x) (g x) := by
  unfold radialMaxSplice
  split_ifs with hα hβ
  · exact (max_eq_left (hlow x hx.1.le (hα.le.trans hαa))).symm
  · rfl
  · exact (max_eq_right (hupp x (heβ.trans (le_of_not_gt hβ)) hx.2.le)).symm

lemma radialMaxSplice_outer {α β c e : ℝ} {f g : Position → ℝ}
    (hαe : α≤e) (hβc : β≤c)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖≤c → f x≤g x)
    {x : Position} (hx : e<‖x‖) : radialMaxSplice α β f g x=g x := by
  unfold radialMaxSplice
  have hn : ¬‖x‖<α := not_lt_of_ge (hαe.trans hx.le)
  rw [ite_eq_right hn]
  split_ifs with hβ
  · exact max_eq_right (hupp x hx.le (hβ.le.trans hβc))
  · rfl

lemma continuous_radialMaxSplice {α β a b c e : ℝ} {f g : Position → ℝ}
    (hbα : b<α) (hαa : α<a) (hae : a≤e) (heβ : e<β) (hβc : β<c)
    (hf : Continuous f) (hg : Continuous g)
    (hlow : ∀ x,b≤‖x‖ → ‖x‖≤a → g x≤f x)
    (hupp : ∀ x,e≤‖x‖ → ‖x‖≤c → f x≤g x) :
    Continuous (radialMaxSplice α β f g) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxa : ‖x‖<a
  · apply hf.continuousAt.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hxa] with y hy
    exact radialMaxSplice_inner hbα.le (hae.trans heβ.le) hlow hy
  · by_cases hex : e<‖x‖
    · apply hg.continuousAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hex] with y hy
      exact radialMaxSplice_outer (hαa.le.trans hae) hβc.le hupp hy
    · have hxb : b<‖x‖ := (hbα.trans hαa).trans_le (le_of_not_gt hxa)
      have hxc : ‖x‖<c := (le_of_not_gt hex).trans_lt (heβ.trans hβc)
      apply (hf.max hg).continuousAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxb,
        (isOpen_lt continuous_norm continuous_const).mem_nhds hxc] with y hy hy'
      exact radialMaxSplice_middle hαa.le heβ.le hlow hupp ⟨hy,hy'⟩

lemma radialMaxSplice_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → Position → ℝ} (α β : ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : Ω×Position => radialMaxSplice α β (f z.1) (g z.1) z.2) := by
  exact hf.ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const)
    ((hf.max hg).ite (measurableSet_lt (continuous_norm.measurable.comp measurable_snd) measurable_const) hg)

lemma radialMaxSplice_abs_bound {α β A B : ℝ} {f g : Position → ℝ} {x : Position}
    (hf : |f x|≤A) (hg : |g x|≤B) : |radialMaxSplice α β f g x| ≤ max A B := by
  unfold radialMaxSplice
  split_ifs
  · exact hf.trans (le_max_left _ _)
  · have hAf : -(max A B)≤f x := (neg_le_neg (le_max_left A B)).trans ((abs_le.mp hf).1)
    have hBf : f x ≤ max A B := (abs_le.mp hf).2.trans (le_max_left _ _)
    have hAg : g x ≤ max A B := (abs_le.mp hg).2.trans (le_max_right _ _)
    exact abs_le.mpr ⟨hAf.trans (le_max_left _ _),max_le hBf hAg⟩
  · exact hg.trans (le_max_right _ _)

end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

def propagationPairOffset (bad : Prop) (R l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) : ℝ :=
  if bad then u x-l1/R^4 else max (u x-l1/R^4) (H x-l2/R^4)

def propagationNextOffset (bad : Prop) (B R Z L l1 l2 : ℝ) (u H : Position → ℝ) : Position → ℝ :=
  radialMaxSplice ((53/50)*R) ((3/2)*L*R)
    (propagationPairOffset bad R l1 l2 u H) (propagationBarrierOffset B R Z)

lemma propagationPairOffset_continuous (bad : Prop) (R l1 l2 : ℝ) {u H : Position → ℝ}
    (hu : Continuous u) (hH : Continuous H) : Continuous (propagationPairOffset bad R l1 l2 u H) := by
  change Continuous (fun x => if bad then u x-l1/R^4 else max (u x-l1/R^4) (H x-l2/R^4))
  by_cases hb : bad
  · simp only [ite_eq_left hb]
    exact hu.sub continuous_const
  · simp only [ite_eq_right hb]
    exact (hu.sub continuous_const).max (hH.sub continuous_const)

lemma le_propagationPairOffset (bad : Prop) (R l1 l2 : ℝ) (u H : Position → ℝ) (x : Position) :
    u x-l1/R^4 ≤ propagationPairOffset bad R l1 l2 u H x := by
  unfold propagationPairOffset
  split_ifs
  · rfl
  · exact le_max_left _ _

lemma propagation_shift_cap_nonpos {C d R L l v : ℝ} (hR : 0<R) (hL : 0<L)
    (hl : 0≤l) (hd : L*R≤d) (hC : C≤l*L^4) (hv : v≤C/d^4) : v-l/R^4≤0 := by
  have hd' := (mul_pos hL hR).trans_le hd
  have hp := pow_le_pow_left₀ (mul_pos hL hR).le hd 4
  have h1 := mul_le_mul_of_nonneg_right hC (pow_pos hR 4).le
  have h2 := mul_le_mul_of_nonneg_left hp hl
  have hh : C/d^4≤l/R^4 := (div_le_div_iff₀ (pow_pos hd' 4) (pow_pos hR 4)).mpr (by
    nlinarith only [h1,h2])
  linarith only [hv,hh]

lemma propagation_old_lower_overlap {B r R Z l1 : ℝ} (hB : 0<B) (hr : 0<r)
    (hR : R=2*r) (hl1 : l1≤propagationGamma B) {u : Position → ℝ} {x : Position}
    (hx : R≤‖x‖) (hx' : ‖x‖≤(11/10)*R)
    (hu : propagationBarrier B r x≤Z*coulombKernel x+u x) :
    propagationBarrierOffset B R Z x≤u x-l1/R^4 := by
  have hRp : 0<R := by rw [hR]; positivity
  have H := propagationBarrier_gap hB hr (by simpa only [hR] using hx) (by simpa only [hR] using hx')
  rw [←hR] at H
  have Hl := div_le_div_of_nonneg_right hl1 (pow_pos hRp 4).le
  have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hx
  linarith only [hu,H,Hl,he]

lemma propagation_splice_overlaps {bad : Prop} {B C r R Z L l1 l2 : ℝ}
    {u H : Position → ℝ} (hB : 0<B) (hr : 0<r) (hR : R=2*r) (hL : 2<L)
    (hl2 : 0≤l2) (hl21 : l2≤l1) (hlγ : l1≤propagationGamma B) (hCL : C≤l2*L^4)
    (hu : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
      Z*coulombKernel x+u x≤C/‖x‖^4)
    (hH : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4) :
    (∀ x,(26/25)*R≤‖x‖ → ‖x‖≤(27/25)*R →
      propagationBarrierOffset B R Z x≤propagationPairOffset bad R l1 l2 u H x) ∧
    (∀ x,L*R≤‖x‖ → ‖x‖≤2*L*R →
      propagationPairOffset bad R l1 l2 u H x≤propagationBarrierOffset B R Z x) := by
  have hRp : 0<R := by rw [hR]; positivity
  constructor
  · intro x hx hx'
    have hRx : R≤‖x‖ := by linarith only [hx,hRp]
    have hrx : r≤‖x‖ := by rw [hR] at hRx; linarith only [hRx,hr]
    exact (propagation_old_lower_overlap hB hr hR hlγ hRx
      (by linarith only [hx',hRp]) (hu x hrx).1).trans (le_propagationPairOffset bad R l1 l2 u H x)
  · intro x hx hx'
    have hRx : R≤‖x‖ := by nlinarith only [hx,mul_pos (show 0<L-1 by linarith) hRp]
    have hrx : r≤‖x‖ := by rw [hR] at hRx; linarith only [hRx,hr]
    have hb := propagationBarrier_positive hB hRp hRx
    have he := propagationBarrierOffset_eq (B:=B) (Z:=Z) hRx
    have hC1 : C≤l1*L^4 := hCL.trans (mul_le_mul_of_nonneg_right hl21 (pow_nonneg (by linarith) _))
    have hv1 := propagation_shift_cap_nonpos hRp (by linarith : 0<L) (hl2.trans hl21) hx hC1 (hu x hrx).2
    have hv1' : u x-l1/R^4≤propagationBarrierOffset B R Z x := by linarith only [hv1,hb,he]
    unfold propagationPairOffset
    split_ifs with hbad
    · exact hv1'
    · have hv2 := propagation_shift_cap_nonpos hRp (by linarith : 0<L) hl2 hx hCL (hH hbad x hrx hx')
      exact max_le hv1' (by linarith only [hv2,hb,he])

lemma propagationNextOffset_continuous {bad : Prop} {B C r R Z L l1 l2 : ℝ}
    {u H : Position → ℝ} (hB : 0<B) (hr : 0<r) (hR : R=2*r) (hL : 2<L)
    (hl2 : 0≤l2) (hl21 : l2≤l1) (hlγ : l1≤propagationGamma B) (hCL : C≤l2*L^4)
    (huc : Continuous u) (hHc : Continuous H)
    (hu : ∀ x,r≤‖x‖ → propagationBarrier B r x≤Z*coulombKernel x+u x ∧
      Z*coulombKernel x+u x≤C/‖x‖^4)
    (hH : ¬bad → ∀ x,r≤‖x‖ → ‖x‖≤2*L*R → Z*coulombKernel x+H x≤C/‖x‖^4) :
    Continuous (propagationNextOffset bad B R Z L l1 l2 u H) := by
  have hRp : 0<R := by rw [hR]; positivity
  obtain ⟨hlow,hupp⟩ := propagation_splice_overlaps hB hr hR hL hl2 hl21 hlγ hCL hu hH
  apply continuous_radialMaxSplice
    (b:=(26/25)*R) (a:=(27/25)*R) (e:=L*R) (c:=2*L*R)
  · linarith only [hRp]
  · linarith only [hRp]
  · nlinarith only [mul_pos (show 0<L-27/25 by linarith) hRp]
  · nlinarith only [mul_pos (show 0<L by linarith) hRp]
  · nlinarith only [mul_pos (show 0<L by linarith) hRp]
  · exact propagationPairOffset_continuous bad R l1 l2 huc hHc
  · exact propagationBarrierOffset_continuous B Z hRp
  · exact hlow
  · exact hupp

end NeutralAtom
end

end

end OAI
