import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierOuterWeakBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierGluing_barrier_scope
open Set Filter MeasureTheory Laplacian Metric
open scoped Topology ContDiff
open CoulombAnalysis
variable {r t L R : ℝ} {u v : TFSpace → ℝ}
variable (hrt : r < t) (htL : t < L) (hLR : L < R)
variable (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ < t → v x ≤ u x)
variable (hhi : ∀ x, L < ‖x‖ → ‖x‖ < R → u x ≤ v x)

include htL hLR hlo in
lemma cutMaximum_inner {x : TFSpace} (hx : ‖x‖ < t) : cutMaximum r R u v x = u x := by
  unfold cutMaximum
  split_ifs with h1 h2
  · rfl
  · exact max_eq_left (hlo x (le_of_not_gt h1) hx)
  · exact False.elim (h2 (hx.trans (htL.trans hLR)))

lemma cutMaximum_middle {x : TFSpace} (hx : r < ‖x‖) (hR : ‖x‖ < R) :
    cutMaximum r R u v x = max (u x) (v x) := by
  simp only [cutMaximum,ite_eq_right (not_lt.mpr hx.le),ite_eq_left hR]

include hrt htL hhi in
lemma cutMaximum_outer {x : TFSpace} (hx : L < ‖x‖) : cutMaximum r R u v x = v x := by
  unfold cutMaximum
  rw [ite_eq_right (not_lt.mpr ((hrt.trans htL).trans hx).le)]
  split_ifs with hR
  · exact max_eq_right (hhi x hx hR)
  · rfl

include hrt htL hLR hlo hhi in
lemma cutMaximum_continuous (hu : Continuous u) (hv : Continuous v) :
    Continuous (cutMaximum r R u v) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : ‖x‖ < t
  · apply hu.continuousAt.congr
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact (cutMaximum_inner htL hLR hlo hy).symm
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      apply (hu.max hv).continuousAt.congr
      filter_upwards [((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨hx',hR⟩] with y hy
      exact (cutMaximum_middle hy.1 hy.2).symm
    · have hL : L < ‖x‖ := hLR.trans_le (le_of_not_gt hR)
      apply hv.continuousAt.congr
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hL] with y hy
      exact (cutMaximum_outer hrt htL hhi hy).symm

include hrt htL hLR hlo hhi in

theorem cutMaximum_weak_nuclear (Z k : ℝ) (hr : 0 < r)
    (hu : Continuous u) (hv : Continuous v) {g χ : TFSpace → ℝ}
    (hg : LocallyIntegrable g) (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < r → χ x = 0)
    (hui : WeakNuclearLowerOn {x : TFSpace | ‖x‖ < t} Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hum : WeakNuclearLowerOn {x : TFSpace | r < ‖x‖ ∧ ‖x‖ < R} Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hvm : WeakNuclearLowerOn {x : TFSpace | r < ‖x‖ ∧ ‖x‖ < R} Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x)))
    (hvo : WeakNuclearLowerOn {x : TFSpace | L < ‖x‖} Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x))) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+cutMaximum r R u v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+cutMaximum r R u v x)) := by
  have hc := cutMaximum_continuous hrt htL hLR hlo hhi hu hv
  have hg' := nuclear_source_locallyIntegrable Z k hr hg hχ hbχ hzero hc
  rw [weakNuclearLower_add_iff Z hc.locallyIntegrable]
  apply weak_lower_local hc.locallyIntegrable hg'
  intro x _
  have transfer {V : Set TFSpace} {w : TFSpace → ℝ}
      (hw : WeakNuclearLowerOn V Z (fun y => nuclearField Z y+w y)
        (fun y => g y+χ y*reaction k (nuclearField Z y+w y)))
      (he : ∀ y ∈ V, w y = cutMaximum r R u v y) :
      WeakLaplacianLowerOn V (cutMaximum r R u v)
        (fun y => g y+χ y*reaction k (nuclearField Z y+cutMaximum r R u v y)) := by
    have hn := hw.congr_field (fun y hy => congrArg (nuclearField Z y+·) (he y hy))
    have hn' := hn.congr_source (fun y hy => by rw [he y hy])
    exact (weakNuclearLower_add_iff Z hc.locallyIntegrable).mp hn'
  by_cases hx : ‖x‖ < t
  · exact ⟨{y | ‖y‖ < t},isOpen_lt continuous_norm continuous_const,hx,
      transfer hui (fun y hy => (cutMaximum_inner htL hLR hlo hy).symm)⟩
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      have hopen : IsOpen {y : TFSpace | r < ‖y‖ ∧ ‖y‖ < R} := (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      exact ⟨{y | r < ‖y‖ ∧ ‖y‖ < R},hopen,⟨hx',hR⟩,
        transfer (nuclear_weak_maximum hopen Z k hr hu hv hg hχ hbχ hzero hum hvm)
          (fun y hy => (cutMaximum_middle hy.1 hy.2).symm)⟩
    · exact ⟨{y | L < ‖y‖},isOpen_lt continuous_const continuous_norm,hLR.trans_le (le_of_not_gt hR),
        transfer hvo (fun y hy => (cutMaximum_outer hrt htL hhi hy).symm)⟩

end Work_BarrierGluing_barrier_scope

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology

open CoulombAnalysis

theorem cutMaximum_weak_nuclear_of_cover {r t L R ρ : ℝ} {u v : TFSpace → ℝ}
    (hrt : r < t) (htL : t < L) (hLR : L < R)
    (hlo : ∀ x, r ≤ ‖x‖ → ‖x‖ < t → v x ≤ u x)
    (hhi : ∀ x, L < ‖x‖ → ‖x‖ < R → u x ≤ v x)
    (Z k : ℝ) (hρ : 0 < ρ) (hu : Continuous u) (hv : Continuous v)
    {g χ : TFSpace → ℝ} (hg : LocallyIntegrable g)
    (hχ : Measurable χ) (hbχ : ∀ x, ‖χ x‖ ≤ 1)
    (hzero : ∀ x, ‖x‖ < ρ → χ x = 0)
    (hui : WeakNuclearLowerOn {x : TFSpace | ‖x‖ < t} Z (fun x => nuclearField Z x+u x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u x)))
    (hwm : WeakNuclearLowerOn {x : TFSpace | r < ‖x‖ ∧ ‖x‖ < R} Z
      (fun x => nuclearField Z x+max (u x) (v x))
      (fun x => g x+χ x*reaction k (nuclearField Z x+max (u x) (v x))))
    (hvo : WeakNuclearLowerOn {x : TFSpace | L < ‖x‖} Z (fun x => nuclearField Z x+v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+v x))) :
    WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+cutMaximum r R u v x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+cutMaximum r R u v x)) := by
  have hc := cutMaximum_continuous hrt htL hLR hlo hhi hu hv
  have hg' := nuclear_source_locallyIntegrable Z k hρ hg hχ hbχ hzero hc
  rw [weakNuclearLower_add_iff Z hc.locallyIntegrable]
  apply weak_lower_local hc.locallyIntegrable hg'
  intro x _
  have transfer {V : Set TFSpace} {w : TFSpace → ℝ}
      (hw : WeakNuclearLowerOn V Z (fun y => nuclearField Z y+w y)
        (fun y => g y+χ y*reaction k (nuclearField Z y+w y)))
      (he : ∀ y ∈ V, w y = cutMaximum r R u v y) :
      WeakLaplacianLowerOn V (cutMaximum r R u v)
        (fun y => g y+χ y*reaction k (nuclearField Z y+cutMaximum r R u v y)) := by
    have hn := hw.congr_field (fun y hy => congrArg (nuclearField Z y+·) (he y hy))
    have hn' := hn.congr_source (fun y hy => by rw [he y hy])
    exact (weakNuclearLower_add_iff Z hc.locallyIntegrable).mp hn'
  by_cases hx : ‖x‖ < t
  · exact ⟨{y | ‖y‖ < t},isOpen_lt continuous_norm continuous_const,hx,
      transfer hui (fun y hy => (cutMaximum_inner htL hLR hlo hy).symm)⟩
  · by_cases hR : ‖x‖ < R
    · have hx' : r < ‖x‖ := hrt.trans_le (le_of_not_gt hx)
      have hopen : IsOpen {y : TFSpace | r < ‖y‖ ∧ ‖y‖ < R} :=
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      exact ⟨{y | r < ‖y‖ ∧ ‖y‖ < R},hopen,⟨hx',hR⟩,
        transfer hwm (fun y hy => (cutMaximum_middle hy.1 hy.2).symm)⟩
    · exact ⟨{y | L < ‖y‖},isOpen_lt continuous_const continuous_norm,hLR.trans_le (le_of_not_gt hR),
        transfer hvo (fun y hy => (cutMaximum_outer hrt htL hhi hy).symm)⟩

end CoulombBarrier

end

end OAI
