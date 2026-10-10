import Mathlib
import OAI.Analysis.Crouzeix.DiskBoundaryChart

namespace OAI

/-! Convex Approximation. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

theorem isSimplyConnected_of_convex {U : Set ℂ} (hc : Convex ℝ U) (hne : U.Nonempty) :
    IsSimplyConnected U := by
  let _ := hc.contractibleSpace hne
  change SimplyConnectedSpace U
  infer_instance

theorem exists_convex_analytic_neighborhood {K V : Set ℂ} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ U : Set ℂ, IsOpen U ∧ Bornology.IsBounded U ∧ Convex ℝ U ∧
      K ⊆ U ∧ closure U ⊆ V ∧
      (∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) := by
  obtain ⟨δ, hδ, hδsub⟩ := hK.exists_cthickening_subset_open hV hKV
  let N := thickening δ K
  have hNo : IsOpen N := isOpen_thickening
  have hNb : Bornology.IsBounded N := hK.isBounded.thickening
  have hNc : Convex ℝ N := hconv.thickening δ
  have hKN : K ⊆ N := self_subset_thickening hδ K
  obtain ⟨a, ha⟩ := hne
  have hNa : a ∈ N := hKN ha
  obtain ⟨f, h, hf, hh, hfb, hhb, hinv, _, _, _⟩ :=
    riemann_biholomorphic_bounded hNo hNb (isSimplyConnected_of_convex hNc ⟨a, hNa⟩) hNa
  obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn ⟨a, ha⟩ ((hf.continuousOn.mono hKN).norm)
  obtain ⟨r, hbr, hr1⟩ := exists_between (mem_ball_zero_iff.mp (hfb.mapsTo (hKN hb)))
  have hr : 0 < r := (norm_nonneg _).trans_lt hbr
  have hKU : K ⊆ h '' ball 0 r := by
    intro z hz
    exact ⟨f z, mem_ball_zero_iff.mpr ((hbmax hz).trans_lt hbr), hinv.1 (hKN hz)⟩
  have hha := hh.analyticOnNhd isOpen_ball
  have hUo := isOpen_image_of_univalent isOpen_ball (hha.mono (ball_subset_ball hr1.le))
    (hhb.injOn.mono (ball_subset_ball hr1.le))
  have hUc := convex_image_subdisk hNc hf hh hhb hinv hr1.le
  have hUclosed := closure_image_subdisk hr hr1 hh.continuousOn
  have hUsubN : closure (h '' ball 0 r) ⊆ N := by
    rw [hUclosed]
    rintro z ⟨w, hw, rfl⟩
    exact hhb.mapsTo ((closedBall_subset_ball hr1) hw)
  exact ⟨h '' ball 0 r, hUo, hNb.subset (subset_closure.trans hUsubN), hUc,
    hKU, hUsubN.trans ((thickening_subset_cthickening δ K).trans hδsub),
    fun p hp => boundaryChart_image_subdisk hr hr1 hha hhb.injOn hp⟩

end CrouzeixHilbert.Conformal

end

end OAI
