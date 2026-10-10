import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.NetFieldVariationBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric

namespace CoulombAtom
open CoulombAnalysis

lemma localTFResponse_mono_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    localTFResponse a ≤ localTFResponse b := by
  rcases hab.eq_or_lt with h | h
  · exact congrArg localTFResponse h |>.le
  · exact (localTFResponse_strict_mono ha h).le

theorem exists_inverse_height_net {lo hi xi : ℝ}
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ H : Finset ℝ, (∀ k ∈ H, lo/2 ≤ k ∧ k ≤ 2*hi) ∧
      ∀ h ∈ Icc lo hi,
        (∃ k ∈ H, h-xi/4 ≤ k ∧ k ≤ h-xi/8) ∧
        (∃ k ∈ H, h+xi/8 ≤ k ∧ k ≤ h+xi/4) := by
  classical
  obtain ⟨S,hS,hfin,hcover⟩ := isCompact_Icc.finite_cover_balls
    (s := Icc (lo/2) (2*hi)) (show 0 < xi/16 by positivity)
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro k hk
    exact hS (hfin.mem_toFinset.mp hk)
  · intro h hh
    have hlo' : h-3*xi/16 ∈ Icc (lo/2) (2*hi) := by
      constructor <;> linarith [hh.1,hh.2]
    have hhi' : h+3*xi/16 ∈ Icc (lo/2) (2*hi) := by
      constructor <;> linarith [hh.1,hh.2]
    have extract (t : ℝ) (ht : t ∈ Icc (lo/2) (2*hi)) :
        ∃ k ∈ hfin.toFinset, |t-k| < xi/16 := by
      obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover ht)
      obtain ⟨hk,hball⟩ := mem_iUnion.mp hk
      refine ⟨k,hfin.mem_toFinset.mpr hk,?_⟩
      simpa only [Metric.mem_ball,Real.dist_eq] using hball
    obtain ⟨kl,hkl,hl⟩ := extract _ hlo'
    obtain ⟨kh,hkh,hh'⟩ := extract _ hhi'
    have hl' := abs_lt.mp hl
    have hh'' := abs_lt.mp hh'
    exact ⟨⟨kl,hkl,by linarith,by linarith⟩,⟨kh,hkh,by linarith,by linarith⟩⟩

theorem exists_uniform_inverse_density_margin {lo hi xi : ℝ}
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ h ∈ Icc lo hi,
      localTFResponse (h-xi/8)+eta ≤ localTFResponse h ∧
      localTFResponse h+eta ≤ localTFResponse (h+xi/8) := by
  let g : ℝ → ℝ := fun h => min
    (localTFResponse h-localTFResponse (h-xi/8))
    (localTFResponse (h+xi/8)-localTFResponse h)
  have hg : Continuous g :=
    (localTFResponse_continuous.sub
      (localTFResponse_continuous.comp (continuous_id.sub continuous_const))).min
      ((localTFResponse_continuous.comp (continuous_id.add continuous_const)).sub
        localTFResponse_continuous)
  obtain ⟨h,hh,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlh) hg.continuousOn
  have hgpos : 0 < g h := by
    apply lt_min
    · exact sub_pos.mpr (localTFResponse_strict_mono (by linarith [hh.1]) (by linarith))
    · exact sub_pos.mpr (localTFResponse_strict_mono (by linarith [hh.1]) (by linarith))
  refine ⟨g h,hgpos,?_⟩
  intro t ht
  have hm : g h ≤ g t := hmin ht
  have h1 := hm.trans (min_le_left _ _)
  have h2 := hm.trans (min_le_right _ _)
  exact ⟨by linarith,by linarith⟩

theorem inverse_net_propagation {X : Type*} {B : Set X} {Q : Finset X}
    {H : Finset ℝ} {v rho : X → ℝ} {lo hi xi eta alpha beta : ℝ}
    (hxi : 0 < xi) (hlo : 16*xi < lo)
    (halpha : alpha ≤ xi/4) (hbeta : beta ≤ 1)
    (hmargin : ∀ h ∈ Icc lo hi,
      localTFResponse (h-xi/8)+eta ≤ localTFResponse h ∧
      localTFResponse h+eta ≤ localTFResponse (h+xi/8))
    (hheight : ∀ h ∈ Icc lo hi,
      (∃ k ∈ H, h-xi/4 ≤ k ∧ k ≤ h-xi/8) ∧
      (∃ k ∈ H, h+xi/8 ≤ k ∧ k ≤ h+xi/4))
    (hnet : ∀ y ∈ B, ∃ x ∈ Q,
      |v x-v y| ≤ alpha+beta*max (-v y) 0 ∧ |rho x-rho y| ≤ eta)
    (hgood : ∀ x ∈ Q, ∀ k ∈ H,
      ¬(v x ≤ k-xi/4 ∧ localTFResponse k ≤ rho x) ∧
      ¬(k+xi/4 ≤ v x ∧ rho x ≤ localTFResponse k)) :
    ∀ y ∈ B, ∀ h ∈ Icc lo hi,
      (localTFResponse h < rho y → h-xi ≤ v y) ∧
      (rho y < localTFResponse h → v y ≤ h+xi) := by
  intro y hy h hh
  obtain ⟨x,hx,hv,hr⟩ := hnet y hy
  have hr' := abs_le.mp hr
  constructor
  · intro hhigh
    by_contra hn
    have hvy : v y ≤ h-xi := (lt_of_not_ge hn).le
    have hvx : v x ≤ h-3*xi/4 :=
      net_field_high_transfer hxi.le (by linarith [hh.1]) halpha hbeta hv hvy
    obtain ⟨k,hk,hkl,hkh⟩ := (hheight h hh).1
    have hk0 : 0 ≤ k := by linarith [hh.1]
    have hkresp := localTFResponse_mono_nonneg hk0 hkh
    have hgap := (hmargin h hh).1
    apply (hgood x hx k hk).1
    exact ⟨by linarith,by linarith⟩
  · intro hlow
    by_contra hn
    have hvy : h+xi ≤ v y := (lt_of_not_ge hn).le
    have hvx : h+3*xi/4 ≤ v x :=
      net_field_low_transfer hxi.le (by linarith [hh.1]) halpha hv hvy
    obtain ⟨k,hk,hkl,hkh⟩ := (hheight h hh).2
    have hh0 : 0 ≤ h+xi/8 := by linarith [hh.1]
    have hkresp := localTFResponse_mono_nonneg hh0 hkl
    have hgap := (hmargin h hh).2
    apply (hgood x hx k hk).2
    exact ⟨by linarith,by linarith⟩

end CoulombAtom

end

end OAI
