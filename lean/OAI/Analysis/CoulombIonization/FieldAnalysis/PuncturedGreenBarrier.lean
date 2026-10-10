import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.WeakPuncturedMaximumBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

lemma punctured_laplacian_green {f g : TFSpace → ℝ}
    (hf : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 f x)
    (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {0}ᶜ) :
    (∫ x, f x*Δ g x) = ∫ x, Δ f x*g x := by
  have hn : (tsupport g)ᶜ ∈ 𝓝 (0 : TFSpace) :=
    (isClosed_tsupport g).isOpen_compl.mem_nhds (by
      intro hh
      exact hs hh rfl)
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hn
  let b : ContDiffBump (0 : TFSpace) := ⟨r/4,r/2,by positivity,by linarith⟩
  let F : TFSpace → ℝ := fun x => (1-b x)*f x
  have hF : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst x
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : TFSpace) b.rIn_pos] with z hz
      simp only [F,b.one_of_mem_closedBall (ball_subset_closedBall hz),sub_self,zero_mul]
    · exact (contDiffAt_const.sub b.contDiffAt).mul (hf x hx)
  have he {x : TFSpace} (hx : x ∈ tsupport g) : F =ᶠ[𝓝 x] f := by
    have hxr : r ≤ ‖x‖ := by
      by_contra! hh
      exact hrs (by simpa only [mem_ball,dist_zero_right] using hh) hx
    have hxb : b.rOut < ‖x‖ := by dsimp [b]; linarith
    filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hxb)] with z hz
    simp only [F,b.zero_of_le_dist (by simpa only [dist_zero_right] using hz.le),sub_zero,one_mul]
  calc
    _ = ∫ x, F x*Δ g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : Δ g x = 0
        · simp only [hx,mul_zero]
        · change f x*Δ g x = F x*Δ g x
          rw [(he (tfLaplacian_support hg hx)).eq_of_nhds]
    _ = ∫ x, Δ F x*g x := compact_laplacian_green hF hg hcg
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : g x = 0
        · simp only [hx,mul_zero]
        · change Δ F x*g x = Δ f x*g x
          rw [(laplacian_congr_nhds (he (subset_tsupport g hx))).eq_of_nhds]

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology

open CoulombAtom

def PuncturedPoisson (u f : Space → ℝ) : Prop :=
  ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
    tsupport g ⊆ {0}ᶜ → (∫ x, u x*Δ g x) = ∫ x, f x*g x

lemma PuncturedPoisson.of_classical {u : Space → ℝ}
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ 2 u x) : PuncturedPoisson u (Δ u) :=
  fun _ hg hcg hs => punctured_laplacian_green hu hg hcg hs

lemma PuncturedPoisson.congr_source {u f h : Space → ℝ} (hu : PuncturedPoisson u f)
    (he : EqOn f h {0}ᶜ) : PuncturedPoisson u h := by
  intro g hg hcg hs
  rw [hu g hg hcg hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : g x = 0
    · simp only [hx,mul_zero]
    · change f x*g x = h x*g x
      rw [he (hs (subset_tsupport g hx))]

lemma PuncturedPoisson.sub {u v f h : Space → ℝ}
    (hu : PuncturedPoisson u f) (hv : PuncturedPoisson v h)
    (huc : ContinuousOn u {0}ᶜ) (hvc : ContinuousOn v {0}ᶜ)
    (hfc : ContinuousOn f {0}ᶜ) (hhc : ContinuousOn h {0}ᶜ) :
    PuncturedPoisson (u-v) (f-h) := by
  intro g hg hcg hs
  have hui := punctured_laplacian_pairing_integrable huc hg hcg hs
  have hvi := punctured_laplacian_pairing_integrable hvc hg hcg hs
  have hfi := punctured_test_integrable hfc hg.continuous hcg hs
  have hhi := punctured_test_integrable hhc hg.continuous hcg hs
  change (∫ x, (u x-v x)*Δ g x) = ∫ x, (f x-h x)*g x
  simp_rw [sub_mul]
  rw [integral_sub hui hvi,integral_sub hfi hhi,hu g hg hcg hs,hv g hg hcg hs]

lemma PuncturedPoisson.const_mul {u f : Space → ℝ} (hu : PuncturedPoisson u f) (a : ℝ) :
    PuncturedPoisson (fun x => a*u x) (fun x => a*f x) := by
  intro g hg hcg hs
  change (∫ x, (a*u x)*Δ g x) = ∫ x, (a*f x)*g x
  simp_rw [mul_assoc]
  rw [integral_const_mul,integral_const_mul,hu g hg hcg hs]

lemma PuncturedPoisson.constant (c : ℝ) : PuncturedPoisson (fun _ => c) (fun _ => 0) := by
  intro g hg hcg _
  simp only [zero_mul,integral_zero]
  rw [integral_const_mul,compact_laplacian_mass hg hcg,mul_zero]

lemma PuncturedPoisson.add_const {u f : Space → ℝ} (hu : PuncturedPoisson u f)
    (huc : ContinuousOn u {0}ᶜ) (hfc : ContinuousOn f {0}ᶜ) (c : ℝ) :
    PuncturedPoisson (fun x => u x+c) f := by
  have hh := hu.sub (PuncturedPoisson.constant (-c)) huc continuousOn_const hfc continuousOn_const
  convert hh using 1 <;> (try funext x) <;> simp

lemma PuncturedPoisson.nonneg_on {u f : Space → ℝ}
    (hu : PuncturedPoisson u f) {U : Set Space} (hU : U ⊆ {0}ᶜ)
    (hf : ∀ x ∈ U, 0 ≤ f x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ U) (hgn : ∀ x, 0 ≤ g x) :
    0 ≤ ∫ x, u x*Δ g x := by
  rw [hu g hg hcg (hs.trans hU)]
  apply integral_nonneg
  intro x
  by_cases hx : g x = 0
  · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
  · exact mul_nonneg (hf x (hs (subset_tsupport g hx))) (hgn x)

lemma PuncturedPoisson.nonneg_on_positive {u f : Space → ℝ}
    (hu : PuncturedPoisson u f)
    (hf : ∀ x, x ≠ 0 → 0 < u x → 0 ≤ f x)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hs : tsupport g ⊆ {x | x ≠ 0 ∧ 0 < u x}) (hgn : ∀ x, 0 ≤ g x) :
    0 ≤ ∫ x, u x*Δ g x := by
  rw [hu g hg hcg (fun x hx => (hs hx).1)]
  apply integral_nonneg
  intro x
  by_cases hx : g x = 0
  · simp only [hx,mul_zero,Pi.zero_apply,le_refl]
  · have hh := hs (subset_tsupport g hx)
    exact mul_nonneg (hf x hh.1 hh.2) (hgn x)

end CoulombAnalysis

end

end OAI
