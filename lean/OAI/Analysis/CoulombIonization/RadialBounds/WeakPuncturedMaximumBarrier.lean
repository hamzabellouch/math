import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakPositiveComparisonBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma punctured_test_integrable {u g : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ) (hg : Continuous g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) : Integrable (fun x => u x*g x) :=
  continuousOn_mul_integrable_support hcg (hu.mono hs) hg (subset_tsupport g)

lemma punctured_laplacian_pairing_integrable {u g : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) : Integrable (fun x => u x*Δ g x) :=
  continuousOn_mul_integrable_support hcg (hu.mono hs) (tfLaplacian_continuous hg)
    (tfLaplacian_support hg)

theorem weak_annular_maximum {a R : ℝ} (ha : 0 < a) {u : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | x ≠ 0 ∧ ‖x‖ ≤ R ∧ 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x)
    (hb : ∀ x, ‖x‖ = a ∨ ‖x‖ = R → u x ≤ 0) :
    ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ R → u x ≤ 0 := by
  let K : Set Space := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ R}
  have hk : IsCompact K := by
    have he : K = closedBall (0 : Space) R ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [K,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right]
      exact and_comm
    rw [he]
    exact (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hn (x : Space) (hx : x ∈ K) : x ≠ 0 :=
    norm_pos_iff.mp (ha.trans_le hx.1)
  have hb' (x : Space) (hx : x ∈ K) (hi : x ∉ interior K) : u x ≤ 0 := by
    apply hb
    by_contra! h
    have ha' : a < ‖x‖ := lt_of_le_of_ne hx.1 h.1.symm
    have hr' : ‖x‖ < R := lt_of_le_of_ne hx.2 h.2
    apply hi
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).mem_nhds ⟨ha',hr'⟩)
    exact fun y hy => ⟨hy.1.le,hy.2.le⟩
  have hm := weak_subharmonic_positive_compact hk (hu.mono (fun x hx => hn x hx)) hb'
    (fun g hg hcg hs hgn => hw g hg hcg
      (fun x hx => ⟨hn x (interior_subset (hs hx).1),(interior_subset (hs hx).1).2,(hs hx).2⟩) hgn)
  exact fun x hx hxR => hm x ⟨hx,hxR⟩

theorem weak_punctured_ball_maximum {R : ℝ} {u : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | x ≠ 0 ∧ ‖x‖ ≤ R ∧ 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x)
    (hb : ∀ x, ‖x‖ = R → u x ≤ 0)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0) :
    ∀ x, x ≠ 0 → ‖x‖ ≤ R → u x ≤ 0 := by
  obtain ⟨a,ha,hnear⟩ := hz
  intro x hx hxR
  by_cases hxa : ‖x‖ ≤ a
  · exact hnear x hx hxa
  · exact weak_annular_maximum ha hu hw (fun y hy => by
      rcases hy with hy | hy
      · exact hnear y (norm_pos_iff.mp (hy ▸ ha)) hy.le
      · exact hb y hy) x (le_of_not_ge hxa) hxR

theorem weak_global_punctured_maximum {u : Space → ℝ}
    (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | x ≠ 0 ∧ 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x)
    (hz : ∃ a > 0, ∀ x, x ≠ 0 → ‖x‖ ≤ a → u x ≤ 0)
    (hinfty : ∃ R > 0, ∀ x, R ≤ ‖x‖ → u x ≤ 0) :
    ∀ x, x ≠ 0 → u x ≤ 0 := by
  obtain ⟨R,_hR,hfar⟩ := hinfty
  intro x hx
  by_cases hxr : R ≤ ‖x‖
  · exact hfar x hxr
  · exact weak_punctured_ball_maximum hu
      (fun g hg hcg hs hgn => hw g hg hcg (fun x hx => ⟨(hs hx).1,(hs hx).2.2⟩) hgn)
      (fun y hy => hfar y hy.ge) hz
      x hx (le_of_not_ge hxr)

end CoulombAnalysis

end

end OAI
