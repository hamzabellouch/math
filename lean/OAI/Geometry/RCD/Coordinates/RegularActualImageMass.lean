import OAI.Geometry.RCD.Coordinates.RegularActualImageGoodSets
import OAI.Geometry.RCD.Coordinates.RegularImageMassEstimate
import OAI.Geometry.RCD.Metric.CoarseFineSourceMass
import OAI.Geometry.RCD.Metric.GoodSetInteriorPoint

namespace OAI

/-! # Absolute mass from the constructed inner-radius coordinate maps -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_actual_image_mass_estimate {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hK : K≤0) {p : X} (hp : IsRegular n p)
    {η ζ : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1/8192) (hζ : 0 < ζ)
    (hζsmall : ζ*((Real.cosh 1^(n-1)*2^n)*(16*16384)^n) < 1) :
    ∃ s : ℝ, 0 < s ∧ ∀ R : ℝ, 0 < R → R < s → -1 ≤ K*(163840*R)^2 →
      volume.real (ball (0 : Euclidean n) (R/4096)) -
        volume.real (ball (0 : Euclidean n) 1)*imageMassErrorConstant n*ζ*R^n ≤
      (1+32*η)^n*(hausdorff n X).real (ball p (R/4096+(2*R)*(η/4))) := by
  obtain ⟨s,hs,hsets⟩ := hX.regular_actual_image_good_sets hn hK hp hη hζ
  refine ⟨s,hs,?_⟩
  intro R hR hRs hcurvLarge
  have hcurv : -1≤K*(32*R)^2 := by
    have he : K*(163840*R)^2=(5120:ℝ)^2*(K*(32*R)^2) := by ring
    rw [he] at hcurvLarge
    nlinarith
  obtain ⟨v,U,hU,hUsub,hbad,hgood,hglobal,hcoarse,hfine⟩ := hsets R hR hRs hcurvLarge
  have hpoint := hX.good_set_inner_point hn hR hζ.le hζsmall hcurv hbad
  have hf : ∀ z ∈ U, ∀ r : ℝ, 0 < r → r < R →
      IsPointedApproximation z 0 r (1/16) (1/128) (fun x => r⁻¹ • (v x-v z)) := by
    intro z hz r hr hrR
    exact (hfine z hz r hr hrR).mono_error (by linarith only [hηsmall])
  have hh := hX.coarse_fine_source_mass hn (hX.regular_euclidean_hausdorff hn hp)
    (ρ := R/4096) (C := ⟨2*(n:ℝ),by positivity⟩) (L := ⟨1+32*η,by positivity⟩)
    hR (by positivity) (by linarith only [hR])
    (by change (1:ℝ)≤2*n
        have hn0 : (2:ℝ)≤n := by exact_mod_cast hn
        linarith only [hn0])
    hcurv (by nlinarith only [hηsmall,hR]) hU hUsub hgood hglobal hcoarse hf
    (by simpa only [show R/4096/4=R/16384 by ring] using hpoint)
  let M := (hausdorff n X).real (ball p (16*R))
  have hM : 0 < M := ENNReal.toReal_pos
    (hX.fullSupport p _ (by positivity)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hE : (2*5^n*volume.real (ball (0 : Euclidean n) 1))*
      (((4*(2*(n:ℝ)))^n*(Real.cosh 1^(n-1)*2^n)*(16*R)^n/M)*
        (hausdorff n X).real (ball p R \ U)) ≤
      volume.real (ball (0 : Euclidean n) 1)*imageMassErrorConstant n*ζ*R^n := by
    calc
      _ ≤ (2*5^n*volume.real (ball (0 : Euclidean n) 1))*
          (((4*(2*(n:ℝ)))^n*(Real.cosh 1^(n-1)*2^n)*(16*R)^n/M)*(ζ*M)) := by
        gcongr
      _ = _ := by
        dsimp only [imageMassErrorConstant]
        rw [show (8:ℝ)=4*2 by norm_num]
        simp only [mul_pow]
        field_simp [hM.ne']
  change volume.real (ball (0 : Euclidean n) (R/4096)) -
    (2*5^n*volume.real (ball (0 : Euclidean n) 1))*
      (((4*(2*(n:ℝ)))^n*(Real.cosh 1^(n-1)*2^n)*(16*R)^n/M)*
        (hausdorff n X).real (ball p R \ U)) ≤
      (1+32*η)^n*(hausdorff n X).real (ball p (R/4096+(2*R)*(η/4))) at hh
  linarith only [hh,hE]

end RegularPointCoordinates

end

end OAI
