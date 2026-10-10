import OAI.Analysis.C0Absorption.Coordinates

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

open Set Filter Topology
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E U Z : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def absorptionMap (Q : Z →L[ℝ] U) (K : E × U → Z) (x : Z × E) : Z :=
  x.1 + K (x.2, Q x.1)

theorem absorption_onto {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    (hg : Function.Surjective g)
    (hQK : ∀ x : E × U, Q (K x) = g x - x.2) :
    Function.Surjective (absorptionMap Q K) := by
  intro z
  obtain ⟨⟨t,u⟩, htu⟩ := hg (Q z)
  refine ⟨(z-K (t,u),t), ?_⟩
  have hQ : Q (z-K (t,u)) = u := by rw [map_sub, hQK, htu]; abel
  simp only [absorptionMap, hQ]
  abel

theorem absorption_upper {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) {LK : ℝ}
    (hLK : 0 ≤ LK) (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y) :
    ∀ x y, dist (absorptionMap Q K x) (absorptionMap Q K y) ≤
      (1+LK * max 1 ‖Q‖) * dist x y := by
  intro x y
  have hq : dist (Q x.1) (Q y.1) ≤ ‖Q‖ * dist x y :=
    (Q.lipschitzWith.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left ((by rw [Prod.dist_eq]; exact le_max_left _ _ : dist x.1 y.1 ≤ dist x y)) (norm_nonneg Q))
  have ht : dist x.2 y.2 ≤ max 1 ‖Q‖ * dist x y := by
    calc
      dist x.2 y.2 ≤ dist x y := (by rw [Prod.dist_eq]; exact le_max_right _ _ : dist x.2 y.2 ≤ dist x y)
      _ = 1 * dist x y := (one_mul _).symm
      _ ≤ max 1 ‖Q‖ * dist x y := mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  have hinput : dist (x.2, Q x.1) (y.2, Q y.1) ≤ max 1 ‖Q‖ * dist x y := by
    rw [Prod.dist_eq]
    exact max_le ht (hq.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))
  calc
    dist (absorptionMap Q K x) (absorptionMap Q K y)
      ≤ dist x.1 y.1 + dist (K (x.2,Q x.1)) (K (y.2,Q y.1)) := dist_add_add_le _ _ _ _
    _ ≤ dist x y + LK * (max 1 ‖Q‖ * dist x y) :=
      add_le_add ((by rw [Prod.dist_eq]; exact le_max_left _ _ : dist x.1 y.1 ≤ dist x y)) ((hK _ _).trans (mul_le_mul_of_nonneg_left hinput hLK))
    _ = _ := by ring

theorem absorption_inverse_bound {E U Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (Q : Z →L[ℝ] U) (K : E × U → Z) (g : E × U → U)
    {LK cg : ℝ} (hLK : 0 ≤ LK) (hcg : 0 < cg)
    (hK : ∀ x y, dist (K x) (K y) ≤ LK * dist x y)
    (hg : ∀ x y, cg * dist x y ≤ dist (g x) (g y))
    (hQK : ∀ x : E × U, Q (K x) = g x-x.2) :
    ∀ x y, dist x y ≤ max (1+LK*‖Q‖/cg) (‖Q‖/cg) *
      dist (absorptionMap Q K x) (absorptionMap Q K y) := by
  intro x y
  let F := absorptionMap Q K
  have hQF (a : Z × E) : Q (F a) = g (a.2, Q a.1) := by
    simp only [F, absorptionMap, map_add, hQK]
    abel
  have hinput : dist (x.2,Q x.1) (y.2,Q y.1) ≤ (‖Q‖/cg) * dist (F x) (F y) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hcg).mpr
    calc
      dist (x.2, Q x.1) (y.2, Q y.1) * cg
        = cg * dist (x.2, Q x.1) (y.2, Q y.1) := mul_comm _ _
      _ ≤ dist (g (x.2,Q x.1)) (g (y.2,Q y.1)) := hg _ _
      _ = dist (Q (F x)) (Q (F y)) := by rw [hQF, hQF]
      _ ≤ ‖Q‖ * dist (F x) (F y) := Q.lipschitzWith.dist_le_mul _ _
  have hf : dist x.1 y.1 ≤ (1+LK*‖Q‖/cg) * dist (F x) (F y) := by
    calc
      dist x.1 y.1 = dist (F x-K (x.2,Q x.1)) (F y-K (y.2,Q y.1)) := by
        simp [F, absorptionMap]
      _ ≤ dist (F x) (F y)+dist (K (x.2,Q x.1)) (K (y.2,Q y.1)) := dist_sub_sub_le _ _ _ _
      _ ≤ dist (F x) (F y)+LK*((‖Q‖/cg)*dist (F x) (F y)) :=
        add_le_add_right ((hK _ _).trans (mul_le_mul_of_nonneg_left hinput hLK)) _
      _ = _ := by ring
  have hs : dist x.2 y.2 ≤ (‖Q‖/cg)*dist (F x) (F y) :=
    (show dist x.2 y.2 ≤ dist (x.2,Q x.1) (y.2,Q y.1) by rw [Prod.dist_eq]; exact le_max_left _ _).trans hinput
  rw [Prod.dist_eq]
  exact max_le (hf.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg))
    (hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg))

end
end C0Absorption

open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

namespace C0Absorption
noncomputable section

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem normalize_norm_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (norm_normalize hx).le

theorem normalization_bound (x y : E) :
    ‖x‖ * dist (normalize x) (normalize y) ≤ 2 * dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) = x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖x‖ * ‖normalize x-normalize y‖ = ‖‖x‖ • (normalize x-normalize y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ = ‖x-y+(‖y‖-‖x‖) • normalize y‖ := by rw [he]
    _ ≤ ‖x-y‖ + ‖(‖y‖-‖x‖) • normalize y‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + |‖y‖-‖x‖| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add_right (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (normalize_norm_le_one y) (abs_nonneg (‖y‖-‖x‖))) _
    _ ≤ ‖x-y‖+‖x-y‖ := by
      apply add_le_add_right
      simpa only [abs_sub_comm] using abs_norm_sub_norm_le x y
    _ = 2*‖x-y‖ := by ring

def normalizedBall (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨normalize x, by simpa only [Metric.mem_closedBall, dist_zero_right] using normalize_norm_le_one x⟩

def zeroBall : Metric.closedBall (0 : E) 1 := ⟨0, by simp⟩

@[simp] theorem normalizedBall_zero : normalizedBall (0 : E) = zeroBall := by
  apply Subtype.ext
  simp [normalizedBall, zeroBall]

def radialLift (ζ : Metric.closedBall (0 : E) 1 → Z) (x : E) : Z :=
  ‖x‖ • ζ (normalizedBall x)

@[simp] theorem radialLift_zero (ζ : Metric.closedBall (0 : E) 1 → Z) : radialLift ζ 0 = 0 := by
  simp [radialLift]

theorem norm_pointMap_le_one {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) (s : Metric.closedBall (0 : E) 1) :
    ‖ζ s‖ ≤ 1 := by
  have hh := hζ.dist_le_mul s zeroBall
  rw [h0, dist_zero_right, NNReal.coe_one, one_mul] at hh
  have hb : dist s zeroBall ≤ 1 := s.property
  exact hh.trans hb

theorem radialLift_lipschitz (ζ : Metric.closedBall (0 : E) 1 → Z)
    (hζ : LipschitzWith 1 ζ) (h0 : ζ zeroBall = 0) : LipschitzWith 3 (radialLift ζ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : radialLift ζ x-radialLift ζ y =
      (‖x‖-‖y‖) • ζ (normalizedBall x) +
        ‖y‖ • (ζ (normalizedBall x)-ζ (normalizedBall y)) := by
    simp only [radialLift, sub_smul, smul_sub]
    abel
  have hdist : ‖ζ (normalizedBall x)-ζ (normalizedBall y)‖ ≤ dist (normalize x) (normalize y) := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq, normalizedBall, dist_eq_norm, Subtype.coe_mk] using
      hζ.dist_le_mul (normalizedBall x) (normalizedBall y)
  calc
    dist (radialLift ζ x) (radialLift ζ y) = ‖radialLift ζ x-radialLift ζ y‖ := dist_eq_norm _ _
    _ ≤ |‖x‖-‖y‖|+‖y‖*dist (normalize x) (normalize y) := by
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_smul, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
      exact add_le_add
        (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (norm_pointMap_le_one ζ hζ h0 (normalizedBall x)) (abs_nonneg (‖x‖-‖y‖)))
        (mul_le_mul_of_nonneg_left hdist (norm_nonneg y))
    _ ≤ dist x y + 2*dist x y := by
      apply add_le_add
      · simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y
      · simpa only [dist_comm] using normalization_bound y x
    _ = (3 : ℝ≥0)*dist x y := by norm_num; ring

theorem radialLift_homogeneous (ζ : Metric.closedBall (0 : E) 1 → Z) {r : ℝ}
    (hr : 0 ≤ r) (x : E) : radialLift ζ (r • x) = r • radialLift ζ x := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have he : normalizedBall (r • x) = normalizedBall x := by
    apply Subtype.ext
    exact normalize_smul_of_pos hr x
  simp only [radialLift, he, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_smul]

end
end C0Absorption

end OAI
