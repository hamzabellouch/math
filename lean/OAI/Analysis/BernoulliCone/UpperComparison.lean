import OAI.Analysis.BernoulliCone.ThresholdRecovery

namespace OAI

section
noncomputable section
open Set Filter InnerProductSpace MeasureTheory
open scoped Topology ContDiff NNReal
namespace Bernoulli.DeSilvaJerison

lemma threshold_lipschitz {φ:Space 7→ℝ} {D:Set (Space 7)} (hφ:Test D φ) (δ:ℝ) :
    ∃K:ℝ≥0,LipschitzWith K (fun x=>max (φ x-δ) 0) := by
  obtain ⟨K,hK⟩:=hφ.1.lipschitzWith_of_hasCompactSupport hφ.2.1 (by simp)
  have hD:LipschitzWith K (fun x=>φ x-δ):=by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hK.dist_le_mul x y
  exact ⟨K,hD.max_const 0⟩
lemma threshold_support {φ:Space 7→ℝ} {δ:ℝ} (hδ:0≤δ):
    tsupport (fun x=>U x+max (φ x-δ) 0-U x)⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hn
  have hφ:φ x=0:=image_eq_zero_of_notMem_tsupport hn
  have hh:max (φ x-δ) 0=0:=by rw [hφ,max_eq_right (by linarith)]
  exact hx (by dsimp; rw [hh]; ring)

/-- The actual upper foliation comparison, transferred through H1-zero trace
closure to every admissible upper Sobolev competitor on every ball. -/
theorem U_upper_comparison (c:Space 7) (r:ℝ) (hr:0<r)
    {v:Space 7→ℝ} {V:Space 7→Space 7}
    (hv:H1 (Metric.ball c r) v V)
    (hUv:∀ᵐ x ∂volume.restrict (Metric.ball c r),U x≤v x)
    (htrace:H10 (Metric.ball c r) (fun x=>v x-U x) (fun x=>V x-gradient U x)) :
    energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r) v V := by
  have hu:=U_h1loc c r hr (subset_univ _)
  have hh:=ThresholdRecovery.upper_variation_of_threshold_tests hu ⟨hv.sub hu, htrace.2⟩
    (Eventually.of_forall U_nonneg) (hUv.mono fun x hx=>sub_nonneg.mpr hx)
  have hcomp:∀δ:ℝ,0<δ → ∀φ:Space 7→ℝ,Test (Metric.ball c r) φ →
      energy (Metric.ball c r) U (gradient U)≤energy (Metric.ball c r)
      (fun x=>U x+max (φ x-δ) 0)
      (fun x=>gradient U x+(if 0<φ x-δ then (1:ℝ) else 0) • gradient φ x):=by
    intro δ hδ φ hφ
    obtain ⟨K,hK⟩:=exists_lipschitz_U
    obtain ⟨L,hL⟩:=threshold_lipschitz hφ δ
    have hvL:=hK.add hL
    have hsub:=threshold_support (φ:=φ) hδ.le
    have hc:HasCompactSupport (fun x=>U x+max (φ x-δ) 0-U x):=
      hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hsub
    have he:=U_upper_lipschitz_comparison hvL (fun x=>by have hh:=le_max_right (φ x-δ) 0; linarith) hc (hsub.trans hφ.2.2)
    have hH:H1 (Metric.ball c r) (fun x=>U x+max (φ x-δ) 0)
        (fun x=>gradient U x+(if 0<φ x-δ then (1:ℝ) else 0) • gradient φ x):=
      hu.add (SobolevCalculus.h1_positivePart Metric.isOpen_ball (ThresholdRecovery.h1_sub_const_ball hφ.h1 δ))
    rwa [energy_congr (EventuallyEq.refl _ _) ((LipschitzSobolev.h1_ball hvL c r).gradient_unique Metric.isOpen_ball hH)] at he
  simpa only [add_sub_cancel] using hh hcomp
end Bernoulli.DeSilvaJerison

end
end

end OAI
