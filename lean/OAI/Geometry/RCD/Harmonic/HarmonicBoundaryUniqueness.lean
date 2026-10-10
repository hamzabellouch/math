import OAI.Geometry.RCD.Harmonic.HarmonicLayerMassBound

namespace OAI

/-! # Squared-thickness boundary control determines a harmonic function -/

open Set Metric Filter MeasureTheory Laplacian
open scoped ContDiff Topology
noncomputable section
namespace RegularPointCoordinates

theorem harmonic_zero_of_squared_boundary_layer {n : ℕ} (hn : 0<n) {R : ℝ}
    (hR : 0<R) {f : Euclidean n → ℝ}
    (hf : ContDiffOn ℝ ∞ f (ball 0 R))
    (hh : ∀ x∈ball (0:Euclidean n) R, (Δ f) x=0)
    {A η : ℝ} (hη : 0<η)
    (hlayer : ∀ δ : ℝ, 0<δ → δ<η → ∀ b : ℝ, R-δ<b → b<R →
      (∫ x in ball (0:Euclidean n) b \ ball 0 (R-δ), (f x)^2)≤A*δ^2) :
    EqOn f 0 (ball 0 R) := by
  obtain ⟨C,hC,hbound⟩ := harmonic_layer_mass_bound hR hf hh
  have hzero (ρ : ℝ) (_hρ : 0<ρ) (hρR : ρ<R) :
      (∫ x in ball (0:Euclidean n) ρ, (f x)^2)=0 := by
    have hfi : IntegrableOn (fun x => (f x)^2) (ball (0:Euclidean n) ρ) volume :=
      (((hf.continuousOn.pow 2).mono (closedBall_subset_ball hρR)).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
        2*(n:ℝ)*(∫ x in ball (0:Euclidean n) ρ, (f x)^2)≤C*A*δ := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hη).filter_mono nhdsWithin_le_nhds,
        (eventually_lt_nhds (show 0<R/4 by positivity)).filter_mono nhdsWithin_le_nhds,
        (eventually_lt_nhds (show 0<1/R by positivity)).filter_mono nhdsWithin_le_nhds,
        (eventually_lt_nhds (show 0<R-ρ by linarith)).filter_mono nhdsWithin_le_nhds]
        with δ hδ hδη hδR hδinv hδρ
      change 0<δ at hδ
      have ht1 : R*δ/4≤1 := by
        have ht := (lt_div_iff₀ hR).mp hδinv
        nlinarith
      obtain ⟨b,hab,hbR,hm⟩ := hbound δ hδ (by linarith) ht1
      have hib : IntegrableOn (fun x => (f x)^2) (ball (0:Euclidean n) (R-δ)) volume :=
        (((hf.continuousOn.pow 2).mono (closedBall_subset_ball (by linarith : R-δ<R))).integrableOn_compact
          (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
      have hmono := setIntegral_mono_set hib (Eventually.of_forall fun x => sq_nonneg (f x))
        (Eventually.of_forall (ball_subset_ball (by linarith : ρ≤R-δ)))
      have h₁ := mul_le_mul_of_nonneg_left hmono (show 0≤2*(n:ℝ) by positivity)
      have h₂ := mul_le_mul_of_nonneg_left (hlayer δ hδ hδη b hab hbR)
        (show 0≤C/δ by positivity)
      have he : C/δ*(A*δ^2)=C*A*δ := by field_simp
      rw [he] at h₂
      exact h₁.trans (hm.trans h₂)
    have ht : Tendsto (fun δ : ℝ => C*A*δ) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun δ : ℝ => C*A*δ) := continuous_const.mul continuous_id
      simpa using (hc.continuousAt (x:=0)).tendsto.mono_left nhdsWithin_le_nhds
    have hz : 2*(n:ℝ)*(∫ x in ball (0:Euclidean n) ρ, (f x)^2)=0 :=
      le_antisymm (ge_of_tendsto ht hevent) (by positivity)
    exact (mul_eq_zero.mp hz).resolve_left (by positivity)
  intro x hx
  have hxR : ‖x‖<R := by simpa only [mem_ball,dist_zero_right] using hx
  let ρ := (‖x‖+R)/2
  have hρ : 0<ρ := by dsimp only [ρ]; linarith [norm_nonneg x]
  have hρR : ρ<R := by dsimp only [ρ]; linarith
  have hfi : IntegrableOn (fun x => (f x)^2) (ball (0:Euclidean n) ρ) volume :=
    (((hf.continuousOn.pow 2).mono (closedBall_subset_ball hρR)).integrableOn_compact
      (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (f x)) hfi).mp (hzero ρ hρ hρR)
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_ball
    ((hf.continuousOn.pow 2).mono (ball_subset_ball hρR.le)) continuousOn_const
  have hxρ : x∈ball (0:Euclidean n) ρ := by
    simp only [mem_ball,dist_zero_right]
    dsimp only [ρ]
    linarith
  exact sq_eq_zero_iff.mp (heq hxρ)

end RegularPointCoordinates

end

end OAI
