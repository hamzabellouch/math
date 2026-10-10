import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.WeakComparison
import OAI.Analysis.CoulombIonization.FieldAnalysis.PatchWeakPoisson

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

open CoulombAtom

lemma norm_sq_weak_laplacian {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) :
    (∫ x, ‖x‖^2*Δ g x) = 6*(∫ x, g x) := by
  have he := compact_laplacian_green (contDiff_norm_sq ℝ) hg hcg
  have hl : Δ (fun x : Space => ‖x‖^2) = fun _ => (6 : ℝ) := by
    funext x
    have h := CoulombPDE.laplacian_norm_sq x
    norm_num [Space,finrank_euclideanSpace_fin] at h
    exact h
  rw [hl,integral_const_mul] at he
  exact he

lemma quadratic_weak_pairing {u : Space → ℝ} {R e : ℝ}
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hui : Integrable (fun x => u x*Δ g x)) :
    (∫ x, (u x+e*(‖x‖^2-R^2))*Δ g x) =
      (∫ x, u x*Δ g x)+6*e*(∫ x, g x) := by
  have hli : Integrable (Δ g) := (tfLaplacian_continuous hg).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg)
  have hqi : Integrable (fun x : Space => ‖x‖^2*Δ g x) := ((continuous_norm.pow 2).mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
    (tfLaplacian_compact hg hcg).mul_left
  have hei : Integrable (fun x : Space => e*(‖x‖^2*Δ g x-R^2*Δ g x)) :=
    (hqi.sub (hli.const_mul (R^2))).const_mul e
  have hsum := integral_add hui hei
  have hsub := integral_sub hqi (hli.const_mul (R^2))
  calc
    _ = ∫ x, u x*Δ g x+e*(‖x‖^2*Δ g x-R^2*Δ g x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [hsum,
        integral_const_mul,hsub,integral_const_mul,
        compact_laplacian_mass hg hcg,norm_sq_weak_laplacian hg hcg]
      ring

theorem weak_subharmonic_positive_ball {u : Space → ℝ} {R : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u (closedBall 0 R))
    (hb : ∀ x : Space, ‖x‖ = R → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R ∩ {x | 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x) : ∀ x ∈ closedBall (0 : Space) R, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  let e := u x/(2*(R^2+1))
  have he : 0 < e := div_pos hux (by positivity)
  have heq : e*(2*(R^2+1)) = u x := div_mul_cancel₀ _ (by positivity)
  let w : Space → ℝ := fun z => u z+e*(‖z‖^2-R^2)
  have hwcont : ContinuousOn w (closedBall 0 R) :=
    hu.add (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.sub continuousOn_const))
  have hwx : 0 < w x := by
    dsimp only [w]
    nlinarith [sq_nonneg ‖x‖,mul_nonneg he.le (sq_nonneg ‖x‖),sq_nonneg R]
  obtain ⟨y,hy,hmax⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn ⟨x,hx⟩ hwcont
  have hwy : 0 < w y := hwx.trans_le (hmax hx)
  have hyi : y ∈ ball (0 : Space) R := by
    have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    by_contra hn
    have heqR : ‖y‖ = R := le_antisymm hyR (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hn))
    have hub := hb y heqR
    dsimp only [w] at hwy
    rw [heqR,sub_self,mul_zero,add_zero] at hwy
    exact (not_lt_of_ge hub) hwy
  have huyp : 0 < u y := by
    have hyR : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hsq := pow_le_pow_left₀ (norm_nonneg y) hyR 2
    have hneg := mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr hsq)
    dsimp only [w] at hwy
    linarith
  have hyn : closedBall (0 : Space) R ∈ 𝓝 y :=
    mem_of_superset (isOpen_ball.mem_nhds hyi) ball_subset_closedBall
  have hnb : ball (0 : Space) R ∩ {z | 0 < u z} ∈ 𝓝 y :=
    inter_mem (isOpen_ball.mem_nhds hyi)
      ((hu.continuousAt hyn).preimage_mem_nhds (Ioi_mem_nhds huyp))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : closedBall y (r/2) ⊆ ball (0 : Space) R ∩ {z | 0 < u z} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrs
  apply weak_laplacian_no_positive_at_max_local
    (hwcont.mono (hsub.trans (inter_subset_left.trans ball_subset_closedBall)))
    (half_pos hr) (mul_pos (by norm_num : (0:ℝ) < 6) he)
  · intro z hz
    exact hmax (ball_subset_closedBall (hsub (ball_subset_closedBall hz)).1)
  · intro g hg hcg hs hn
    have hs' : tsupport g ⊆ ball (0 : Space) R ∩ {z | 0 < u z} :=
      hs.trans (ball_subset_closedBall.trans hsub)
    have hui := continuousOn_mul_integrable_support (isCompact_closedBall (0 : Space) R)
      hu (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans (inter_subset_left.trans ball_subset_closedBall)))
    change 6*e*(∫ z, g z) ≤ ∫ z, (u z+e*(‖z‖^2-R^2))*Δ g z
    rw [quadratic_weak_pairing hg hcg hui]
    linarith only [hw g hg hcg hs' hn]

end Work_WeakPositiveComparison_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

theorem weak_subharmonic_positive_compact {K : Set Space} (hK : IsCompact K)
    {u : Space → ℝ} (hu : ContinuousOn u K)
    (hb : ∀ x ∈ K, x ∉ interior K → u x ≤ 0)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ interior K ∩ {x | 0 < u x} → (∀ x, 0 ≤ g x) →
      0 ≤ ∫ x, u x*Δ g x) : ∀ x ∈ K, u x ≤ 0 := by
  intro x hx
  by_contra! hux
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  let R := max M 1
  have hn (z : Space) (hz : z ∈ K) : ‖z‖ ≤ R := by
    have ht := hM z hz
    rw [Real.norm_of_nonneg (norm_nonneg z)] at ht
    exact ht.trans (le_max_left _ _)
  let e := u x/(2*(R^2+1))
  have he : 0 < e := div_pos hux (by positivity)
  have heq : e*(2*(R^2+1)) = u x := div_mul_cancel₀ _ (by positivity)
  let w : Space → ℝ := fun z => u z+e*(‖z‖^2-R^2)
  have hwcont : ContinuousOn w K :=
    hu.add (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.sub continuousOn_const))
  have hwx : 0 < w x := by
    dsimp only [w]
    nlinarith [sq_nonneg ‖x‖,mul_nonneg he.le (sq_nonneg ‖x‖),sq_nonneg R]
  obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn ⟨x,hx⟩ hwcont
  have hwy : 0 < w y := hwx.trans_le (hmax hx)
  have hpert : e*(‖y‖^2-R^2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos he.le
      (sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg y) (hn y hy) 2))
  have huy : 0 < u y := by dsimp only [w] at hwy; linarith
  have hyi : y ∈ interior K := by
    by_contra hh
    exact (not_lt_of_ge (hb y hy hh)) huy
  have hnb : interior K ∩ {z | 0 < u z} ∈ 𝓝 y :=
    inter_mem (isOpen_interior.mem_nhds hyi)
      ((hu.continuousAt (mem_interior_iff_mem_nhds.mp hyi)).preimage_mem_nhds (Ioi_mem_nhds huy))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hnb
  have hsub : closedBall y (r/2) ⊆ interior K ∩ {z | 0 < u z} :=
    (closedBall_subset_ball (half_lt_self hr)).trans hrs
  apply weak_laplacian_no_positive_at_max_local
    (hwcont.mono (hsub.trans (inter_subset_left.trans interior_subset)))
    (half_pos hr) (mul_pos (by norm_num : (0:ℝ) < 6) he)
  · intro z hz
    exact hmax (interior_subset (hsub (ball_subset_closedBall hz)).1)
  · intro g hg hcg hs hgn
    have hs' : tsupport g ⊆ interior K ∩ {z | 0 < u z} :=
      hs.trans (ball_subset_closedBall.trans hsub)
    have hui := continuousOn_mul_integrable_support hK hu (tfLaplacian_continuous hg)
      ((tfLaplacian_support hg).trans (hs'.trans (inter_subset_left.trans interior_subset)))
    change 6*e*(∫ z, g z) ≤ ∫ z, (u z+e*(‖z‖^2-R^2))*Δ g z
    rw [quadratic_weak_pairing hg hcg hui]
    linarith only [hw g hg hcg hs' hgn]

end CoulombAnalysis

end

end OAI
