import OAI.Geometry.RCD.Sobolev.LocalZeroSetCoercivity
import OAI.Geometry.RCD.Metric.FiniteCoverIntegral
import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Coercivity from uniformly large local zero sets

Separated nets cover the whole working ball. Enlarged energy balls have
uniform overlap by the CD packing estimate, so their local inequalities
sum to one global energy bound with the square of the net radius.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.covered_zero_set_coercivity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : X) (R ρ : ℝ), 0 < R → 0 < ρ → ρ ≤ R →
      -1 ≤ K*R^2 → ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ q : X, dist q p ≤ R →
        (hausdorff n X).real (ball q ρ) ≤
          2*(hausdorff n X).real (ball q ρ ∩
            {x | SobolevSpace.toLp (hausdorff n X) hX.quadratic w x = 0})) →
      (∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
        ∂hausdorff n X) ≤ C*ρ^2 * energyForm (hausdorff n X) hX.quadratic w w := by
  classical
  obtain ⟨C, hC, hlocal⟩ := hX.local_zero_set_coercivity hn (by norm_num : (0:ℝ)≤1)
  obtain ⟨N, hN⟩ := hX.rescaled_separated_card hn (by norm_num : (0:ℝ)<16)
  refine ⟨C*(N+1), by positivity, ?_⟩
  intro p R ρ hR hρ hρR hcurv w hhalf
  have hcurvsmall (s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) : -1 ≤ K*s^2 := by
    by_cases hK : 0 ≤ K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg s))
    · have hh := mul_le_mul_of_nonpos_left ((sq_le_sq₀ hs hR.le).mpr hsR)
        (le_of_not_ge hK)
      linarith
  have hcurvρ := hcurvsmall ρ hρ.le hρR
  have hcurvhalf := hcurvsmall (ρ/2) (by positivity) (by linarith)
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w
  let G := SobolevSpace.minimalSlope μ hX.quadratic w
  let δ : ℝ≥0 := ⟨ρ/2, by positivity⟩
  let s := maximalPatchNet δ (closedBall p R)
  have hs : (s : Set X) ⊆ closedBall p R := maximalPatchNet_subset _ _
  have hsep : (s : Set X).Pairwise (fun x y => ρ/2 ≤ dist x y) :=
    fun x hx y hy hxy => (maximalPatchNet_separated δ _ hx hy hxy).le
  have hcover : ball p R ⊆ ⋃ q ∈ s, ball q ρ := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := maximalPatchNet_covers_bounded
      (show δ ≠ 0 from ne_of_gt (show (0:ℝ≥0) < δ from (by change 0 < ρ/2; positivity)))
      isBounded_closedBall x (ball_subset_closedBall hx)
    exact mem_iUnion₂.mpr ⟨q, hq, hxq.trans_lt (by change ρ/2 < ρ; linarith)⟩
  have hoverlap (x : X) : (s.filter (fun q => x ∈ ball q (8*ρ))).card ≤ N+1 := by
    have hnear (q : X) (hq : q ∈ s.filter (fun q => x ∈ ball q (8*ρ))) :
        dist q x ≤ 16*(ρ/2) := by
      have hqx := (Finset.mem_filter.mp hq).2
      rw [mem_ball, dist_comm] at hqx
      linarith
    exact (hN x (ρ/2) (by positivity) hcurvhalf _
      (hsep.mono (by intro q hq; exact (Finset.mem_filter.mp hq).1)) hnear).trans
      (Nat.le_succ N)
  have hu : Integrable (fun x => u x^2) μ := (Lp.memLp u).integrable_sq
  have hG : Integrable (fun x => G x^2) μ := (Lp.memLp G).integrable_sq
  have hbound (q : X) (hq : q ∈ s) :
      (∫ x in ball q ρ, u x^2 ∂μ) ≤ C*ρ^2 * ∫ x in ball q (8*ρ), G x^2 ∂μ := by
    have hz : u =ᵐ[μ.restrict (ball q ρ ∩ {x | u x = 0})] 0 := by
      filter_upwards [ae_restrict_mem (measurableSet_ball.inter
        ((Lp.stronglyMeasurable u).measurable (measurableSet_singleton 0)))] with x hx
      exact hx.2
    have hh := hlocal q ρ hρ hcurvρ w (ball q ρ ∩ {x | u x = 0})
      (measurableSet_ball.inter ((Lp.stronglyMeasurable u).measurable (measurableSet_singleton 0)))
      inter_subset_left (hhalf q (hs hq)) hz
    have heq : (∫ x in ball q (8*ρ), localGamma μ hX.quadratic w w x ∂μ) =
        ∫ x in ball q (8*ρ), G x^2 ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (localGamma_self μ hX.quadratic w))
    rwa [heq] at hh
  have he : (∫ x, G x^2 ∂μ) = energyForm μ hX.quadratic w w := by
    rw [lp_integral_square_eq_norm_square]
    exact (SobolevSpace.minimalSlope_norm_sq μ hX.quadratic w).trans
      (energyForm_self μ hX.quadratic w).symm
  calc
    _ ≤ ∑ q ∈ s, ∫ x in ball q ρ, u x^2 ∂μ :=
      integral_le_sum_cover μ s _ (fun _ _ => measurableSet_ball) measurableSet_ball hcover
        hu (fun x => sq_nonneg (u x))
    _ ≤ ∑ q ∈ s, C*ρ^2 * ∫ x in ball q (8*ρ), G x^2 ∂μ :=
      Finset.sum_le_sum hbound
    _ = C*ρ^2 * ∑ q ∈ s, ∫ x in ball q (8*ρ), G x^2 ∂μ :=
      (Finset.mul_sum s _ _).symm
    _ ≤ C*ρ^2 * ((N+1) * ∫ x, G x^2 ∂μ) :=
      mul_le_mul_of_nonneg_left
        (sum_integral_le_overlap μ s _ (fun _ _ => measurableSet_ball) (N+1) hoverlap
          hG (fun x => sq_nonneg (G x)) |>.trans_eq (by push_cast; rfl)) (by positivity)
    _ = _ := by rw [he]; ring

end RegularPointCoordinates

end

end OAI
