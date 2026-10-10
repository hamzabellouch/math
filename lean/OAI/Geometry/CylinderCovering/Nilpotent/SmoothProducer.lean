import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.Grid
import OAI.Geometry.CylinderCovering.Physical.WeightLipschitz
import OAI.Geometry.CylinderCovering.Convexity.UniformTaylor

namespace OAI

noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace CylinderCovering.NilpotentRate

theorem gridUnion_subset_cthickening {δ ρ : ℝ} {D : Set Plane}
    (hδ : 0 ≤ δ) (hdiam : Real.sqrt 2 * δ ≤ ρ) :
    gridUnion δ D ⊆ cthickening ρ D := by
  intro b hb
  obtain ⟨i, hi⟩ := mem_iUnion.mp hb
  obtain ⟨hiD, hbi⟩ := mem_iUnion.mp hi
  obtain ⟨x, hxi, hxD⟩ := hiD
  apply closedBall_subset_cthickening hxD ρ
  rw [mem_closedBall, dist_eq_norm]
  exact (NilpotentGrid.same_cell_distance hδ hbi hxi).trans hdiam

theorem smooth_coarse_data {D : Set Plane} {G : Plane → Plane} (h : ℝ)
    (hD : IsCompact D) (hG : RuledApproximation.SmoothNear 2 D G) :
    ∃ M K W δ₀ : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ 0 ≤ W ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      W = max 1 |h| * (K + M * Real.sqrt 2) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b)) (gridUnion δ D) ∧
        ∀ i : Index, ∀ x ∈ cell δ i ∩ D,
          ‖fderiv ℝ G x‖ ≤ M ∧ ∀ b ∈ cell δ i,
            ‖G b - (G x + fderiv ℝ G x (b-x))‖ ≤ K * δ ^ 2 ∧
            ‖G b - G x‖ ≤ (K + M * Real.sqrt 2) * δ ∧
            |RuledApproximation.physicalWeight h (G b) -
              RuledApproximation.physicalWeight h (G x)| ≤ W * δ := by
  obtain ⟨U, hU, hDU, hGU⟩ := hG
  have hdG : ContDiffOn ℝ 1 (fderiv ℝ G) U :=
    hGU.fderiv_of_isOpen hU (by norm_num)
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn (hdG.continuousOn.mono hDU)
  obtain ⟨r, hr, C, hC, hrem⟩ :=
    CylinderUniformTaylor.uniform_remainder_near_compact hD hU hDU hGU
  obtain ⟨ρ, hρ, hρU⟩ := hD.exists_cthickening_subset_open hU hDU
  let M : ℝ := max B 0
  let K : ℝ := 2*C
  let W : ℝ := max 1 |h| * (K + M * Real.sqrt 2)
  let δ₀ : ℝ := min 1 (min r ρ / 2)
  have hM : 0 ≤ M := le_max_right _ _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hsqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  refine ⟨M,K,W,δ₀,hM,hK,hW,hδ₀,min_le_left _ _,rfl,?_⟩
  intro δ hδ hδsmall
  have hδ1 : δ ≤ 1 := hδsmall.le.trans (min_le_left _ _)
  have hδcut : δ ≤ min r ρ / 2 := hδsmall.le.trans (min_le_right _ _)
  have hdiam : Real.sqrt 2 * δ ≤ min r ρ := by
    have := mul_le_mul_of_nonneg_right hsqrt2 hδ.le
    linarith
  have hweight : ContinuousOn (fun b => RuledApproximation.physicalWeight h (G b))
      (cthickening ρ D) :=
    (RuledApproximation.physicalWeight_lipschitzWith h).continuous.comp_continuousOn
      (hGU.continuousOn.mono hρU)
  have hint : IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b))
      (cthickening ρ D) := hweight.integrableOn_compact hD.cthickening
  refine ⟨hint.mono_set (gridUnion_subset_cthickening hδ.le (hdiam.trans (min_le_right _ _))),?_⟩
  intro i x hx
  have hxM : ‖fderiv ℝ G x‖ ≤ M := (hB x hx.2).trans (le_max_left _ _)
  refine ⟨hxM,?_⟩
  intro b hb
  have hdist : ‖b-x‖ ≤ Real.sqrt 2 * δ :=
    NilpotentGrid.same_cell_distance hδ.le hb hx.1
  have hnear : ‖b-x‖ ≤ r := hdist.trans (hdiam.trans (min_le_left _ _))
  have hsq : ‖b-x‖^2 ≤ 2*δ^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (b-x)) (by positivity : 0 ≤ Real.sqrt 2 * δ)).mpr hdist
    simpa only [mul_pow, hsqrt] using hh
  have hTaylor : ‖G b - (G x + fderiv ℝ G x (b-x))‖ ≤ K * δ^2 := by
    have hh := (hrem x hx.2 b hnear).trans (mul_le_mul_of_nonneg_left hsq hC.le)
    simpa only [sub_add_eq_sub_sub] using hh.trans_eq
      (show C * (2*δ^2) = K*δ^2 by dsimp [K]; ring)
  have hlinear : ‖fderiv ℝ G x (b-x)‖ ≤ M * (Real.sqrt 2 * δ) :=
    ((fderiv ℝ G x).le_opNorm _).trans (mul_le_mul hxM hdist (norm_nonneg _) hM)
  have hvariation : ‖G b-G x‖ ≤ (K+M*Real.sqrt 2)*δ := by
    calc
      _ = ‖(G b-(G x+fderiv ℝ G x (b-x)))+fderiv ℝ G x (b-x)‖ := by congr 1; abel
      _ ≤ ‖G b-(G x+fderiv ℝ G x (b-x))‖+‖fderiv ℝ G x (b-x)‖ := norm_add_le _ _
      _ ≤ K*δ^2 + M*(Real.sqrt 2*δ) := add_le_add hTaylor hlinear
      _ ≤ (K+M*Real.sqrt 2)*δ := by
        have hδsq : δ^2 ≤ δ := by
          simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hδ1 hδ.le
        nlinarith [mul_le_mul_of_nonneg_left hδsq hK]
  refine ⟨hTaylor,hvariation,?_⟩
  calc
    _ ≤ max 1 |h| * ‖G b-G x‖ := RuledApproximation.physicalWeight_difference_le h _ _
    _ ≤ max 1 |h| * ((K+M*Real.sqrt 2)*δ) :=
      mul_le_mul_of_nonneg_left hvariation (by positivity)
    _ = W*δ := by dsimp [W]; ring

theorem bounded_second_coarse_data {D : Set Plane} {G : Plane → Plane} (h : ℝ)
    (hD : IsCompact D) (hG : ∃ U : Set Plane, IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ 1 G U ∧
      (∀ x ∈ U, DifferentiableAt ℝ (fderiv ℝ G) x) ∧
      ∃ H : ℝ, 0 ≤ H ∧ ∀ x ∈ U, ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ H) :
    ∃ M K W δ₀ : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ 0 ≤ W ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      W = max 1 |h| * (K + M * Real.sqrt 2) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b)) (gridUnion δ D) ∧
        ∀ i : Index, ∀ x ∈ cell δ i ∩ D,
          ‖fderiv ℝ G x‖ ≤ M ∧ ∀ b ∈ cell δ i,
            ‖G b - (G x + fderiv ℝ G x (b-x))‖ ≤ K * δ ^ 2 ∧
            ‖G b - G x‖ ≤ (K + M * Real.sqrt 2) * δ ∧
            |RuledApproximation.physicalWeight h (G b) -
              RuledApproximation.physicalWeight h (G x)| ≤ W * δ := by
  obtain ⟨U, hU, hDU, hGU, hdiffer, H, hH, hHbound⟩ := hG
  have hdG : ContinuousOn (fderiv ℝ G) U :=
    hGU.continuousOn_fderiv_of_isOpen hU (by norm_num)
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn (hdG.mono hDU)
  obtain ⟨ρ, hρ, hρU⟩ := hD.exists_cthickening_subset_open hU hDU
  let r : ℝ := ρ
  let C : ℝ := H+1
  have hr : 0 < r := hρ
  have hC : 0 < C := by dsimp [C]; linarith
  have hrem : ∀ x ∈ D, ∀ y : Plane, ‖y-x‖ ≤ r →
      ‖G y-G x-fderiv ℝ G x (y-x)‖ ≤ C*‖y-x‖^2 := by
    intro x hx y hy
    have hball : closedBall x ρ ⊆ U :=
      (closedBall_subset_cthickening hx ρ).trans hρU
    have hdiff : ∀ z ∈ closedBall x ρ, DifferentiableAt ℝ G z := by
      intro z hz
      exact ((hGU z (hball hz)).contDiffAt (hU.mem_nhds (hball hz))).differentiableAt (by norm_num)
    have hh := CylinderUniformTaylor.remainder_sq_of_hessian_bound hH
      (convex_closedBall x ρ) hdiff (fun z hz => hdiffer z (hball hz))
      (fun z hz => hHbound z (hball hz)) (mem_closedBall_self hρ.le)
      (show y ∈ closedBall x ρ by rw [mem_closedBall, dist_eq_norm]; exact hy)
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (sq_nonneg _))
  let M : ℝ := max B 0
  let K : ℝ := 2*C
  let W : ℝ := max 1 |h| * (K + M * Real.sqrt 2)
  let δ₀ : ℝ := min 1 (min r ρ / 2)
  have hM : 0 ≤ M := le_max_right _ _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hsqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  refine ⟨M,K,W,δ₀,hM,hK,hW,hδ₀,min_le_left _ _,rfl,?_⟩
  intro δ hδ hδsmall
  have hδ1 : δ ≤ 1 := hδsmall.le.trans (min_le_left _ _)
  have hδcut : δ ≤ min r ρ / 2 := hδsmall.le.trans (min_le_right _ _)
  have hdiam : Real.sqrt 2 * δ ≤ min r ρ := by
    have := mul_le_mul_of_nonneg_right hsqrt2 hδ.le
    linarith
  have hweight : ContinuousOn (fun b => RuledApproximation.physicalWeight h (G b))
      (cthickening ρ D) :=
    (RuledApproximation.physicalWeight_lipschitzWith h).continuous.comp_continuousOn
      (hGU.continuousOn.mono hρU)
  have hint : IntegrableOn (fun b => RuledApproximation.physicalWeight h (G b))
      (cthickening ρ D) := hweight.integrableOn_compact hD.cthickening
  refine ⟨hint.mono_set (gridUnion_subset_cthickening hδ.le (hdiam.trans (min_le_right _ _))),?_⟩
  intro i x hx
  have hxM : ‖fderiv ℝ G x‖ ≤ M := (hB x hx.2).trans (le_max_left _ _)
  refine ⟨hxM,?_⟩
  intro b hb
  have hdist : ‖b-x‖ ≤ Real.sqrt 2 * δ :=
    NilpotentGrid.same_cell_distance hδ.le hb hx.1
  have hnear : ‖b-x‖ ≤ r := hdist.trans (hdiam.trans (min_le_left _ _))
  have hsq : ‖b-x‖^2 ≤ 2*δ^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg (b-x)) (by positivity : 0 ≤ Real.sqrt 2 * δ)).mpr hdist
    simpa only [mul_pow, hsqrt] using hh
  have hTaylor : ‖G b - (G x + fderiv ℝ G x (b-x))‖ ≤ K * δ^2 := by
    have hh := (hrem x hx.2 b hnear).trans (mul_le_mul_of_nonneg_left hsq hC.le)
    simpa only [sub_add_eq_sub_sub] using hh.trans_eq
      (show C * (2*δ^2) = K*δ^2 by dsimp [K]; ring)
  have hlinear : ‖fderiv ℝ G x (b-x)‖ ≤ M * (Real.sqrt 2 * δ) :=
    ((fderiv ℝ G x).le_opNorm _).trans (mul_le_mul hxM hdist (norm_nonneg _) hM)
  have hvariation : ‖G b-G x‖ ≤ (K+M*Real.sqrt 2)*δ := by
    calc
      _ = ‖(G b-(G x+fderiv ℝ G x (b-x)))+fderiv ℝ G x (b-x)‖ := by congr 1; abel
      _ ≤ ‖G b-(G x+fderiv ℝ G x (b-x))‖+‖fderiv ℝ G x (b-x)‖ := norm_add_le _ _
      _ ≤ K*δ^2 + M*(Real.sqrt 2*δ) := add_le_add hTaylor hlinear
      _ ≤ (K+M*Real.sqrt 2)*δ := by
        have hδsq : δ^2 ≤ δ := by
          simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hδ1 hδ.le
        nlinarith [mul_le_mul_of_nonneg_left hδsq hK]
  refine ⟨hTaylor,hvariation,?_⟩
  calc
    _ ≤ max 1 |h| * ‖G b-G x‖ := RuledApproximation.physicalWeight_difference_le h _ _
    _ ≤ max 1 |h| * ((K+M*Real.sqrt 2)*δ) :=
      mul_le_mul_of_nonneg_left hvariation (by positivity)
    _ = W*δ := by dsimp [W]; ring

end CylinderCovering.NilpotentRate

end

end OAI
