import OAI.Geometry.SurfaceImmersion.Whitney.ExactCollarRemainderBounds
import OAI.Geometry.SurfaceImmersion.Whitney.PerturbedCollarJets

namespace OAI

/-! A regular collar interpolating the actual inner and outer surface
maps, with exact agreement on open neighborhoods of both sides. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exact_regular_collar {f g : Base → W} {V : ℝ × ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hV : ContDiff ℝ ∞ V)
    (hc : ∀ t, f (crosscapAxis t) = g (crosscapAxis t))
    (hV0 : ∀ t, V (0,t) = axisTransverse f t)
    (hV1 : ∀ t, V (1,t) = axisTransverse g t)
    {a b R : ℝ} (hR : 0 < R)
    (hI : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b,
      Function.Injective (homotopyCollarJet (axisValue f) V s t 0 0)) :
    ∃ (r : ℝ) (F : Base → W), 0 < r ∧ r < R ∧ ContDiff ℝ ∞ F ∧
      (∀ u : ℝ, |u| < r → ∀ t ∈ Icc a b,
        Function.Injective (fderiv ℝ F ![u,t])) ∧
      (∀ t, F =ᶠ[𝓝 (crosscapAxis t)] g) ∧
      (∀ x : Base, g x = f x →
        (∀ s ∈ Icc (0:ℝ) 1, V (s,x 1) = axisTransverse f (x 1)) → F x = f x) ∧
      ∀ x : Base, r/2 < |x 0| → F =ᶠ[𝓝 x] f := by
  obtain ⟨δ,hδ,hstable⟩ := perturbed_collar_jets (axisValue_smooth hf) hV
    (isCompact_Icc.prod isCompact_Icc)
    (by rintro ⟨s,t⟩ ⟨hs,ht⟩; exact hI s hs t ht)
  let ρ := |a|+|b|+2
  obtain ⟨D,hD,hbound⟩ := collarInterpolationRemainder_bound hf hg ρ
  let r := min R (min 1 (min δ (δ/(D+1)))) / 2
  have hr : 0 < r := half_pos (lt_min hR (lt_min zero_lt_one
    (lt_min hδ (div_pos hδ (by positivity)))))
  have hrR : r < R := (half_lt_self (lt_min hR (lt_min zero_lt_one
    (lt_min hδ (div_pos hδ (by positivity)))))).trans_le (min_le_left _ _)
  have hr1 : r < 1 := (half_lt_self (lt_min hR (lt_min zero_lt_one
    (lt_min hδ (div_pos hδ (by positivity)))))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hrδ : r < δ := (half_lt_self (lt_min hR (lt_min zero_lt_one
    (lt_min hδ (div_pos hδ (by positivity)))))).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrdiv : r < δ/(D+1) := (half_lt_self (lt_min hR (lt_min zero_lt_one
    (lt_min hδ (div_pos hδ (by positivity)))))).trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hDr : D*r < δ := by
    have ht := (lt_div_iff₀ (by positivity : 0 < D+1)).mp hrdiv
    nlinarith
  obtain ⟨χ,hχ,_hcomp,hχg,hχs,hχrange,hχsmall⟩ :=
    exists_slow_collar_cutoff (half_pos hr) (lt_min hδ zero_lt_one)
  have hχb : ∀ t, |χ t| ≤ 1 := fun t => by
    rw [abs_of_nonneg (hχrange t).1]
    exact (hχrange t).2
  have hχd : ∀ t, |t*deriv χ t| ≤ 1 := fun t =>
    (hχsmall t).le.trans (min_le_right _ _)
  let F := exactCollarInterpolation f g V χ
  refine ⟨r,F,hr,hrR,exactCollarInterpolation_smooth hf hg hV hχ,?_,?_,?_,?_⟩
  · intro u hu t ht
    have hx : (![u,t] : Base) ∈ closedBall 0 ρ := by
      rw [mem_closedBall,dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg (by dsimp [ρ]; positivity)).mpr
      intro i
      fin_cases i
      · change |u| ≤ ρ
        have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith [abs_nonneg a, abs_nonneg b]
        exact (hu.trans hr1).le.trans hρ
      · change |t| ≤ ρ
        apply abs_le.mpr
        constructor
        · have ha := neg_abs_le a
          dsimp [ρ]
          linarith [abs_nonneg b, ht.1]
        · have hb := le_abs_self b
          dsimp [ρ]
          linarith [abs_nonneg a, ht.2]
    have hE : ‖fderiv ℝ (collarInterpolationRemainder f g χ) ![u,t]‖ < δ := by
      have hb := hbound χ hχ hχb hχd ![u,t] hx
      change ‖fderiv ℝ (collarInterpolationRemainder f g χ) ![u,t]‖ ≤ D*|u| at hb
      exact hb.trans_lt ((mul_lt_mul_of_pos_left hu hD).trans hDr)
    have hF : F = homotopyCollar (axisValue f) V χ + collarInterpolationRemainder f g χ := by
      funext x
      change homotopyCollar (axisValue f) V χ x + collarRemainder f x +
        χ (x 0) • (collarRemainder g x - collarRemainder f x) =
        homotopyCollar (axisValue f) V χ x +
          (collarRemainder f x + χ (x 0) • (collarRemainder g x - collarRemainder f x))
      exact add_assoc _ _ _
    rw [hF,fderiv_add ((homotopyCollar_smooth (axisValue_smooth hf) hV hχ).differentiable (by simp) _)
      ((collarInterpolationRemainder_smooth hf hg hχ).differentiable (by simp) _),
      homotopyCollar_fderiv (axisValue_smooth hf) hV hχ]
    exact hstable (χ u,t) ⟨hχrange u,ht⟩ u (u*deriv χ u) _
      (hu.trans hrδ) ((hχsmall u).trans_le (min_le_left _ _)) hE
  · intro t
    have hp : Tendsto (fun x : Base => x 0) (𝓝 (crosscapAxis t)) (𝓝 0) := by
      simpa [crosscapAxis_apply] using (continuous_apply (0 : Fin 2)).continuousAt.tendsto (x := crosscapAxis t)
    filter_upwards [hχg.comp_tendsto hp] with x hx
    change χ (x 0) = 1 at hx
    exact exactCollarInterpolation_one hc hV1 hx
  · intro x hx hVx
    exact exactCollarInterpolation_stationary hx (hc (x 1)).symm
      ((hV1 (x 1)).symm.trans (hVx 1 ⟨zero_le_one,le_rfl⟩))
      (hVx (χ (x 0)) (hχrange _))
  · intro x hx
    have hn : x 0 ∉ tsupport χ := by
      intro hh
      exact hx.not_ge (abs_le.mpr (hχs hh))
    have hp : Tendsto (fun y : Base => y 0) (𝓝 x) (𝓝 (x 0)) :=
      (continuous_apply (0 : Fin 2)).continuousAt.tendsto
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto hp] with y hy
    change χ (y 0) = 0 at hy
    exact exactCollarInterpolation_zero hV0 hy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
