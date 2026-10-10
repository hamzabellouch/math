import OAI.Analysis.StrictMeans.MorseGeometry

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma goodPair_lower_regular_cut {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0<h) :
    ∃ a : ℝ, 0<a ∧ a<h ∧ criticalCut k f ξ a=criticalCut k f ξ h ∧
      ∀ z∈criticalCut k f ξ h, a<criticalHeight k (halfPlaneFunction f) z := by
  classical
  have hfin := goodPair_criticalCut_finite hk hg (show 0<h/2 by positivity)
  have hev : ∀ᶠ a in 𝓝 h, ∀ z∈criticalCut k f ξ (h/2),
      criticalHeight k (halfPlaneFunction f) z<h → criticalHeight k (halfPlaneFunction f) z<a := by
    apply (hfin.eventually_all).mpr
    intro z hz
    by_cases hz' : criticalHeight k (halfPlaneFunction f) z<h
    · exact (lt_mem_nhds hz').mono (fun _ ha _=>ha)
    · exact Filter.Eventually.of_forall (fun _ ha=>False.elim (hz' ha))
  obtain ⟨a,ha,hhalf,hbound⟩ := ((lt_mem_nhds (show h/2<h by linarith)).and hev).exists_lt
  refine ⟨a,by linarith,ha,?_,?_⟩
  · ext z
    constructor
    · intro hz
      have hz' : z∈criticalCut k f ξ (h/2) := ⟨hz.1,hhalf.le.trans hz.2⟩
      refine ⟨hz.1,?_⟩
      by_contra hn
      have hx := hbound z hz' (lt_of_not_ge hn)
      linarith [hz.2]
    · intro hz
      exact ⟨hz.1,ha.le.trans hz.2⟩
  · intro z hz
    exact ha.trans_le hz.2

lemma source_squared_critical_strict {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    {z : UpperHalfPlane} {a : ℝ} (ha : 0<a)
    (hz : criticalMap k (halfPlaneFunction f) z=ξ)
    (hheight : a<criticalHeight k (halfPlaneFunction f) z) :
    squaredReciprocalPotential k (halfPlaneFunction f) ξ z<(1/a)^2 := by
  apply (squaredReciprocalPotential_lt_sublevel z.im_pos ha).mpr
  have hn : 0<‖halfPlaneFunction f z-ξ‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun he=>criticalMap_ne_image hk.ne' z.im_pos
      (halfPlaneFunction_deriv_ne_zero f z.im_pos) (hz.trans he.symm)))
  rw [← criticalHeight_value hk z.im_pos hz] at hheight
  rw [lt_div_iff₀ ha]
  have ht := (lt_div_iff₀ hn).mp hheight
  nlinarith

lemma source_squared_interior {k : ℝ} {f : DiskFamily} {ξ z : ℂ} {c : ℝ}
    (hz : 0<z.im) (hc : squaredReciprocalPotential k (halfPlaneFunction f) ξ z<c) :
    z∈interior {w : ℂ | 0<w.im ∧ squaredReciprocalPotential k (halfPlaneFunction f) ξ w≤c} := by
  apply mem_interior_iff_mem_nhds.mpr
  have ha := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have hu := (squaredReciprocalPotential_contDiffAt (k:=k) (ξ:=ξ) hz ha).continuousAt
  filter_upwards [isOpen_halfPlane.mem_nhds hz,hu (gt_mem_nhds hc)] with w hw hwc
  exact ⟨hw,hwc.le⟩

lemma source_poles_subsingleton (f : DiskFamily) (ξ : ℂ) :
    {z : ℂ | 0<z.im ∧ halfPlaneFunction f z=ξ}.Subsingleton := by
  intro z hz w hw
  exact halfPlaneFunction_injOn f hz.1 hw.1 (hz.2.trans hw.2.symm)

end
end StrictInverseFirstPower

end

end OAI
