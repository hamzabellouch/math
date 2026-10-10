import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakMaximum

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAnalysis
open CoulombAtom

lemma continuousOn_mul_integrable_support {K : Set Space} (hK : IsCompact K)
    {f g : Space → ℝ} (hf : ContinuousOn f K) (hg : Continuous g)
    (hs : Function.support g ⊆ K) : Integrable (fun x => f x*g x) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp
    ((hf.mul hg.continuousOn).integrableOn_compact hK)
  intro x hx
  exact hs ((mul_ne_zero_iff.mp hx).2)

lemma weak_pairing_congr {K : Set Space} {u v g : Space → ℝ}
    (he : ∀ x ∈ K, u x = v x) (hg : ContDiff ℝ 2 g) (hs : tsupport g ⊆ K) :
    (∫ x, u x*Δ g x) = ∫ x, v x*Δ g x := by
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : Δ g x = 0
    · simp only [hx,mul_zero]
    · change u x * Δ g x = v x * Δ g x
      rw [he x (hs (tfLaplacian_support hg hx))]

theorem weak_strict_source_comparison {K : Set Space} (hK : IsCompact K)
    {u F : Space → ℝ} (hu : ContinuousOn u K) (hF : ContinuousOn F K)
    (hpos : ∀ x ∈ interior K, 0 < u x → 0 < F x)
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ interior K → (∀ x, 0 ≤ g x) →
      (∫ x, F x*g x) ≤ ∫ x, u x*Δ g x) : ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hu
  have huy : 0 < u y := hux.trans_le (hmax hx)
  have hyi : y ∈ interior K := by
    by_contra hn
    exact (not_lt_of_ge (hb y hy hn)) huy
  let c := F y/2
  have hc : 0 < c := half_pos (hpos y hyi huy)
  have hcf : c < F y := half_lt_self (hpos y hyi huy)
  have hnb : {z | c < F z} ∩ interior K ∈ 𝓝 y :=
    inter_mem ((hF.continuousAt (mem_interior_iff_mem_nhds.mp hyi)).preimage_mem_nhds
      (Ioi_mem_nhds hcf)) (isOpen_interior.mem_nhds hyi)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hbsub : closedBall y (r/2) ⊆ ball y r := closedBall_subset_ball (half_lt_self hr)
  have hsub : closedBall y (r/2) ⊆ K := fun z hz => interior_subset (hrs (hbsub hz)).2
  apply weak_laplacian_no_positive_at_max_local (hu.mono hsub) (half_pos hr) hc
  · intro z hz
    exact hmax (hsub (ball_subset_closedBall hz))
  · intro g hg hcg hs hn
    have hsi : tsupport g ⊆ interior K := fun z hz =>
      (hrs (hbsub (ball_subset_closedBall (hs hz)))).2
    have hiF := continuousOn_mul_integrable_support hK hF hg.continuous
      ((subset_tsupport g).trans (hsi.trans interior_subset))
    calc
      c*(∫ z, g z) = ∫ z, c*g z := (integral_const_mul c g).symm
      _ ≤ ∫ z, F z*g z := by
        apply integral_mono ((hg.continuous.integrable_of_hasCompactSupport hcg).const_mul c) hiF
        intro z
        by_cases hz : g z = 0
        · simp only [hz,mul_zero,le_refl]
        · exact mul_le_mul_of_nonneg_right
            ((hrs (hbsub (ball_subset_closedBall (hs (subset_tsupport g hz))))).1.le) (hn z)
      _ ≤ _ := hw g hg hcg hsi hn

end CoulombAnalysis

end

end OAI
