import OAI.Geometry.SurfaceImmersion.Correction.NormalizedJetCorrection
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! Uniform C1 stability of radial normalization along a compact family
of spherical first jets. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

abbrev FirstJet := Space × (Plane →L[ℝ] Space)

def normalizeFirstJet (J : FirstJet) : FirstJet :=
  (radialNormalize J.1,(fderiv ℝ radialNormalize J.1).comp J.2)

lemma normalizeFirstJet_continuousAt {J : FirstJet} (hJ : J.1 ≠ 0) :
    ContinuousAt normalizeFirstJet J := by
  have h := radialNormalize_smoothAt hJ
  exact (h.continuousAt.comp continuousAt_fst).prodMk
    (((h.fderiv_right (m := ∞) (by simp)).continuousAt.comp continuousAt_fst).clm_comp
      continuousAt_snd)

lemma normalizeFirstJet_fixed {J : FirstJet} (hu : ‖J.1‖ = 1)
    (ht : ∀ v, inner ℝ J.1 (J.2 v) = 0) : normalizeFirstJet J = J := by
  apply Prod.ext
  · simp [normalizeFirstJet,radialNormalize,hu]
  · apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ radialNormalize J.1 (J.2 v) = J.2 v
    rw [radialNormalize_fderiv_unit hu,ht v,zero_smul,sub_zero]

theorem compact_normalization_C1_stability {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F : X → Space) (L : X → Plane →L[ℝ] Space) (hF : Continuous F) (hL : Continuous L)
    (hu : ∀ x, ‖F x‖ = 1) (ht : ∀ x v, inner ℝ (F x) (L x v) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ (Y : Space) (A : Plane →L[ℝ] Space),
      ‖Y-F x‖ < δ → ‖A-L x‖ < δ →
      Y ≠ 0 ∧ ‖radialNormalize Y-F x‖ < ε ∧
        ‖(fderiv ℝ radialNormalize Y).comp A-L x‖ < ε := by
  let J : X → FirstJet := fun x => (F x,L x)
  have hJ : Continuous J := hF.prodMk hL
  let U : Set FirstJet := {J | J.1 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_fst continuous_const
  have hJU : range J ⊆ U := by
    rintro _ ⟨x,rfl⟩
    change F x ≠ 0
    intro hz
    have hh := hu x
    simp [hz] at hh
  have hK := isCompact_range hJ
  obtain ⟨r,hr,hrs⟩ := hK.exists_cthickening_subset_open hU hJU
  have hc : ContinuousOn normalizeFirstJet (Metric.cthickening r (range J)) :=
    fun z hz => (normalizeFirstJet_continuousAt (hrs hz)).continuousWithinAt
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.cthickening.uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro x Y A hY hA
  let H : FirstJet := (Y,A)
  have hHJ : ‖H-J x‖ < min r d := by
    change max ‖Y-F x‖ ‖A-L x‖ < min r d
    exact max_lt hY hA
  have hH : H ∈ Metric.cthickening r (range J) :=
    Metric.thickening_subset_cthickening r (range J)
      (Metric.mem_thickening_iff.mpr ⟨J x,mem_range_self x,by
        simpa only [dist_eq_norm] using hHJ.trans_le (min_le_left r d)⟩)
  have hh := hclose H hH (J x)
    (Metric.self_subset_cthickening (range J) (mem_range_self x)) (by
      simpa only [dist_eq_norm] using hHJ.trans_le (min_le_right r d))
  have hfix : normalizeFirstJet (J x) = J x := normalizeFirstJet_fixed (hu x) (ht x)
  rw [hfix,dist_eq_norm] at hh
  change ‖(radialNormalize Y-F x,(fderiv ℝ radialNormalize Y).comp A-L x)‖ < ε at hh
  exact ⟨hrs hH,(norm_fst_le _).trans_lt hh,(norm_snd_le _).trans_lt hh⟩

end ClosedSurfaceR4.SphericalJets

end

end OAI
