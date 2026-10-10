import OAI.MeasureTheory.Falconer.Recursion.ProfileSuffixContact
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! # Right contact points of a profile's future minimum -/

namespace Falconer
open Set Filter
open scoped Topology NNReal

theorem hasDerivAt_right_secant_lower {f : ℝ → ℝ} {A l r : ℝ}
    (hd : HasDerivAt f l A) (hr : r < l) :
    ∃ η > 0, ∀ w, A < w → w < A+η → r*(w-A) < f w-f A := by
  have he : ∀ᶠ w in 𝓝[>] A, r < slope f A w :=
    (hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE A)).eventually (eventually_gt_nhds hr)
  obtain ⟨η,hη,heη⟩ := Metric.eventually_nhds_iff_ball.mp
    (eventually_nhdsWithin_iff.mp he)
  refine ⟨η,hη,fun w hw hwd => ?_⟩
  have hs := heη w (by
    change dist w A < η
    rw [Real.dist_eq,abs_of_pos (sub_pos.mpr hw)]
    linarith) hw
  rw [slope_def_field] at hs
  exact (lt_div_iff₀ (sub_pos.mpr hw)).mp hs

theorem profileSuffixMinimum_right_contact {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (Icc 0 1)) {A l T : ℝ}
    (hA : A ∈ Ioo 0 1) (hd : HasDerivAt (profileSuffixMinimum f) l A)
    (hl : 0 < l) (hAT : A < T) (hT : T ≤ 1) :
    ∃ B, A < B ∧ B < T ∧ profileSuffixMinimum f B = f B := by
  let F := profileSuffixMinimum f
  have hFL := profileSuffixMinimum_lipschitz hf
  have hc := hf.continuousOn
  have hmono := profileSuffixMinimum_monotone hc
  obtain ⟨η,hη,hgrowth⟩ := hasDerivAt_right_secant_lower hd hl
  let y := A+min η (T-A)/2
  have hmin : 0 < min η (T-A) := lt_min hη (sub_pos.mpr hAT)
  have hAy : A < y := by dsimp [y]; linarith
  have hyT : y < T := by dsimp [y]; linarith [min_le_right η (T-A)]
  have hyη : y < A+η := by dsimp [y]; linarith [min_le_left η (T-A)]
  have hyI : y ∈ Icc (0:ℝ) 1 := ⟨hA.1.le.trans hAy.le,hyT.le.trans hT⟩
  have hFy : F A < F y := by
    have hh := hgrowth y hAy hyη
    dsimp [F]
    linarith
  let v := (F A+F y)/2
  have hv : v ∈ Icc (F A) (F y) := by dsimp [v]; constructor <;> linarith
  obtain ⟨u,hu,heu⟩ := intermediate_value_Icc hAy.le
    (hFL.continuousOn.mono (Icc_subset_Icc hA.1.le hyI.2)) hv
  have hAu : A < u := by
    by_contra hn
    have heq : u = A := le_antisymm (le_of_not_gt hn) hu.1
    rw [heq] at heu
    change F A = v at heu
    dsimp [v] at heu
    linarith
  have hFu : F u < F y := by
    change F u = v at heu
    dsimp [v] at heu
    linarith
  have huI : u ∈ Icc (0:ℝ) 1 := ⟨hA.1.le.trans hu.1,hu.2.trans hyI.2⟩
  obtain ⟨B,hB,heB,_⟩ := profileSuffixMinimum_attained hc huI
  have huB : u ≤ B := hB.1
  have hBI : B ∈ Icc (0:ℝ) 1 := ⟨huI.1.trans huB,hB.2⟩
  have hBy : B < y := by
    by_contra hn
    have hh := profileSuffixMinimum_le hc hyI ⟨le_of_not_gt hn,hB.2⟩
    change F u = f B at heB
    linarith
  refine ⟨B,hAu.trans_le huB,hBy.trans hyT,?_⟩
  apply le_antisymm (profileSuffixMinimum_le hc hBI ⟨le_rfl,hB.2⟩)
  rw [← heB]
  exact hmono huI hBI huB

end Falconer

end OAI
