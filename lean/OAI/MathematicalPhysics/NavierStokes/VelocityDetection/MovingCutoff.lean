import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CompactIntegral
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.CutoffDecay

namespace OAI

noncomputable section
namespace VelocityDetection.MovingCutoff
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory SpatialCalculus

theorem hasDerivAt_capture {n : ℕ} {φ : Coord n → ℝ}
    {ρ : ℝ → Coord n → ℝ} {c : ℝ → Coord n} {a : Coord n → Coord n}
    {g : Coord n → ℝ} {ν t : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hc : ContDiff ℝ 1 c)
    (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i)) (hg : Continuous g)
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0)
    (heq : ∀ X, deriv (fun s => ρ s X) t + (∑ i, a X i * partialD i (ρ t) X) =
      ν * laplacian (fun _ => ρ t) 0 X + g X) :
    HasDerivAt (fun s => ∫ X, φ (X - c s) * ρ s X)
      ((∫ X, fderiv ℝ φ (X - c t) (a X - deriv c t) * ρ t X) +
        ν * (∫ X, laplacian (fun _ => φ) 0 (X - c t) * ρ t X) +
        ∫ X, φ (X - c t) * g X) t := by
  let ψ : Coord n → ℝ := fun X => φ (X - c t)
  have hψ : ContDiff ℝ 2 ψ := hφ.comp (contDiff_id.sub contDiff_const)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph (Homeomorph.subRight (c t))
  have hψ1 := hψ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hψd := hψ.differentiable (by norm_num)
  have hρt : ContDiff ℝ 2 (ρ t) := hρ.comp (contDiff_const.prodMk contDiff_id)
  have hdt (X : Coord n) : deriv (fun s => ρ s X) t =
      fderiv ℝ (uncurry ρ) (t, X) (1, 0) := by
    have hd : HasFDerivAt (uncurry ρ) (fderiv ℝ (uncurry ρ) (t, X)) (t, X) :=
      (hρ.differentiable (by norm_num) (t, X)).hasFDerivAt
    exact (hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t X))).deriv
  have hdtc : Continuous (fun X => deriv (fun s => ρ s X) t) := by
    simp_rw [hdt]
    exact ((hρ.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)).clm_apply
      continuous_const
  have hi : Integrable (fun X => ψ X * deriv (fun s => ρ s X) t) :=
    (hψ.continuous.mul hdtc).integrable_of_hasCompactSupport hψc.mul_right
  have hj : Integrable (fun X => fderiv ℝ ψ X (deriv c t) * ρ t X) :=
    (((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul hρt.continuous)
      |>.integrable_of_hasCompactSupport (hψc.fderiv_apply ℝ _).mul_right
  have hI := CompactIntegral.hasDerivAt_moving_capture
    (hφ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)) hφc
    (hρ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)) hc t
  have hid : (∫ X, φ (X - c t) * deriv (fun s => ρ s X) t -
      fderiv ℝ φ (X - c t) (deriv c t) * ρ t X) =
      (∫ X, ψ X * deriv (fun s => ρ s X) t) -
        (∫ X, fderiv ℝ ψ X (deriv c t) * ρ t X) := by
    simpa only [ψ, fderiv_comp_sub] using integral_sub hi hj
  rw [hid] at hI
  have hweak := weak_scalar_equation hψ hψc hρt hg ha hdiv heq
  simp_rw [← fderiv_apply_eq_sum hψd] at hweak
  rw [hweak] at hI
  have hca : Continuous a := continuous_pi (fun i => (ha i).continuous)
  have htranssupp : HasCompactSupport (fun X => fderiv ℝ ψ X (a X)) := by
    apply (hψc.fderiv ℝ).mono
    intro X hX hzero
    apply hX
    simp only [hzero, zero_apply]
  have haint : Integrable (fun X => fderiv ℝ ψ X (a X) * ρ t X) :=
    (((hψ.continuous_fderiv (by norm_num)).clm_apply hca).mul hρt.continuous)
      |>.integrable_of_hasCompactSupport htranssupp.mul_right
  have hdrift : (∫ X, fderiv ℝ φ (X - c t) (a X - deriv c t) * ρ t X) =
      (∫ X, fderiv ℝ ψ X (a X) * ρ t X) -
        (∫ X, fderiv ℝ ψ X (deriv c t) * ρ t X) := by
    simpa only [ψ, fderiv_comp_sub, map_sub, sub_mul] using integral_sub haint hj
  have hlap : (∫ X, laplacian (fun _ => φ) 0 (X - c t) * ρ t X) =
      ∫ X, laplacian (fun _ => ψ) 0 X * ρ t X := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro X
    dsimp only
    rw [show laplacian (fun _ => ψ) 0 X = laplacian (fun _ => φ) 0 (X - c t) from
      laplacian_translate (fun _ => φ) (fun _ => c t) 0 X]
  apply hI.congr_deriv
  rw [hdrift, hlap]
  dsimp only [ψ]
  ring

def capture (R : ℝ) (c : ℝ → Coord 2) (ρ : ScalarField 2) (t : ℝ) : ℝ :=
  ∫ X, Cutoff.cutoff R (X - c t) * ρ t X

theorem differentiable_capture {R : ℝ} (hR : 0 < R)
    {ρ : ScalarField 2} {c : ℝ → Coord 2}
    (hρ : ContDiff ℝ 1 (uncurry ρ)) (hc : ContDiff ℝ 1 c) :
    Differentiable ℝ (capture R c ρ) := by
  intro t
  exact (CompactIntegral.hasDerivAt_moving_capture
    ((Cutoff.contDiff_cutoff R).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num))
    (Cutoff.hasCompactSupport_cutoff hR) hρ hc t).differentiableAt

theorem cutoff_transport_eq_zero {R : ℝ} (hR : 0 < R)
    (X c a G : Coord 2) (hplateau : (∀ i, |X i - c i| ≤ R) → a = G) :
    fderiv ℝ (Cutoff.cutoff R) (X - c) (a - G) = 0 := by
  by_cases hX : ∀ i, |X i - c i| ≤ R
  · rw [hplateau hX, sub_self, map_zero]
  · obtain ⟨j, hj⟩ := not_forall.mp hX
    rw [fderiv_apply_eq_sum ((Cutoff.contDiff_cutoff R).differentiable (by norm_num))]
    apply Finset.sum_eq_zero
    intro i _
    have hz : partialD i (Cutoff.cutoff R) (X - c) = 0 :=
      Cutoff.spatialD_cutoff_zero_of_large hR ⟨j, (lt_of_not_ge hj).le⟩ i 0
    rw [hz, mul_zero]

theorem hasDerivAt_capture_of_plateau {R ν t : ℝ} (hR : 0 < R)
    {ρ : ScalarField 2} {c : ℝ → Coord 2} {a : Coord 2 → Coord 2}
    {g : Coord 2 → ℝ}
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hc : ContDiff ℝ 1 c)
    (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i)) (hg : Continuous g)
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0)
    (heq : ∀ X, deriv (fun s => ρ s X) t + (∑ i, a X i * partialD i (ρ t) X) =
      ν * laplacian (fun _ => ρ t) 0 X + g X)
    (hplateau : ∀ X, (∀ i, |X i - c t i| ≤ R) → a X = deriv c t) :
    HasDerivAt (capture R c ρ)
      (ν * (∫ X, laplacian (fun _ => Cutoff.cutoff R) 0 (X - c t) * ρ t X) +
        ∫ X, Cutoff.cutoff R (X - c t) * g X) t := by
  have hid := hasDerivAt_capture (Cutoff.contDiff_cutoff R)
    (Cutoff.hasCompactSupport_cutoff hR) hρ hc ha hg hdiv heq
  unfold capture
  simpa only [cutoff_transport_eq_zero hR _ _ _ _ (hplateau _), zero_mul,
    integral_zero, zero_add] using hid

theorem capture_source_eq {R : ℝ} (hR : 0 < R) (c : Coord 2) (g : Coord 2 → ℝ)
    (hsource : ∀ X, g X ≠ 0 → ∀ i, |X i - c i| ≤ R / 2) :
    (∫ X, Cutoff.cutoff R (X - c) * g X) = ∫ X, g X := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  by_cases hX : g X = 0
  · simp only [hX, mul_zero]
  · have h := Cutoff.cutoff_one hR (hsource X hX)
    change Cutoff.cutoff R (X - c) = 1 at h
    rw [h, one_mul]

theorem capture_deriv_lower {R ν t : ℝ} (hR : 0 < R) (hν : 0 ≤ ν)
    {ρ : ScalarField 2} {c : ℝ → Coord 2} {a : Coord 2 → Coord 2}
    {g : Coord 2 → ℝ}
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hc : ContDiff ℝ 1 c)
    (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i)) (hg : Continuous g)
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0)
    (heq : ∀ X, deriv (fun s => ρ s X) t + (∑ i, a X i * partialD i (ρ t) X) =
      ν * laplacian (fun _ => ρ t) 0 X + g X)
    (hplateau : ∀ X, (∀ i, |X i - c t i| ≤ R) → a X = deriv c t)
    (hρint : Integrable (ρ t)) (hρ0 : ∀ X, 0 ≤ ρ t X)
    (hmass : (∫ X, ρ t X) ≤ 1)
    (hsource : ∀ X, g X ≠ 0 → ∀ i, |X i - c t i| ≤ R / 2) :
    -(ν * 3000 / R ^ 2) + (∫ X, g X) ≤ deriv (capture R c ρ) t := by
  rw [(hasDerivAt_capture_of_plateau hR hρ hc ha hg hdiv heq hplateau).deriv,
    capture_source_eq hR _ _ hsource]
  linarith [Cutoff.integral_laplacian_mul_lower hR hν (c t) hρint hρ0 hmass]

theorem retention_on_interval {R ν α β : ℝ} (hR : 0 < R) (hν : 0 ≤ ν) (hαβ : α ≤ β)
    {ρ : ScalarField 2} {c : ℝ → Coord 2} {a : ℝ → Coord 2 → Coord 2}
    {g : ScalarField 2} {M : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 (uncurry ρ)) (hc : ContDiff ℝ 1 c)
    (hM : ContinuousOn M (Icc α β))
    (hM' : ∀ t ∈ Ioo α β, HasDerivAt M (∫ X, g t X) t)
    (ha : ∀ t ∈ Ioo α β, ∀ i, ContDiff ℝ 1 (fun X => a t X i))
    (hg : ∀ t ∈ Ioo α β, Continuous (g t))
    (hdiv : ∀ t ∈ Ioo α β, ∀ X, (∑ i, partialD i (fun Y => a t Y i) X) = 0)
    (heq : ∀ t ∈ Ioo α β, ∀ X,
      deriv (fun s => ρ s X) t + (∑ i, a t X i * partialD i (ρ t) X) =
      ν * laplacian (fun _ => ρ t) 0 X + g t X)
    (hplateau : ∀ t ∈ Ioo α β, ∀ X, (∀ i, |X i - c t i| ≤ R) → a t X = deriv c t)
    (hρint : ∀ t ∈ Ioo α β, Integrable (ρ t))
    (hρ0 : ∀ t ∈ Ioo α β, ∀ X, 0 ≤ ρ t X)
    (hmass : ∀ t ∈ Ioo α β, (∫ X, ρ t X) ≤ 1)
    (hsource : ∀ t ∈ Ioo α β, ∀ X, g t X ≠ 0 → ∀ i, |X i - c t i| ≤ R / 2) :
    M β - capture R c ρ β ≤ M α - capture R c ρ α + (ν * 3000 / R ^ 2) * (β - α) := by
  have hI := differentiable_capture hR (hρ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)) hc
  have hcont : ContinuousOn (fun t => capture R c ρ t - M t) (Icc α β) :=
    hI.continuous.continuousOn.sub hM
  have hdiff : DifferentiableOn ℝ (fun t => capture R c ρ t - M t) (interior (Icc α β)) := by
    rw [interior_Icc]
    intro t ht
    exact ((hI t).sub (hM' t ht).differentiableAt).differentiableWithinAt
  have hbound : ∀ t ∈ interior (Icc α β), -(ν * 3000 / R ^ 2) ≤
      deriv (fun s => capture R c ρ s - M s) t := by
    rw [interior_Icc]
    intro t ht
    have hd := ((hI t).hasDerivAt.sub (hM' t ht)).deriv
    change deriv (fun s => capture R c ρ s - M s) t = _ at hd
    rw [hd]
    have h := capture_deriv_lower hR hν hρ hc (ha t ht) (hg t ht)
      (hdiv t ht) (heq t ht) (hplateau t ht) (hρint t ht) (hρ0 t ht) (hmass t ht) (hsource t ht)
    linarith
  have h := (convex_Icc α β).mul_sub_le_image_sub_of_le_deriv hcont hdiff hbound
    α ⟨le_rfl, hαβ⟩ β ⟨hαβ, le_rfl⟩ hαβ
  linarith

end VelocityDetection.MovingCutoff
end

end OAI
