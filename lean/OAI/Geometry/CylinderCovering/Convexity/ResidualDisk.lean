import OAI.Geometry.CylinderCovering.Ruled.Projection
import OAI.Geometry.CylinderCovering.Ruled.LocalCylinder

namespace OAI

noncomputable section
open Set Metric MeasureTheory
namespace CylinderCovering.ResidualDisk
open RuledApproximation

theorem distance_le_sqrt_two {p q : Plane} {s : ℝ} (hs : 0 ≤ s)
    (h0 : |q 0-p 0| ≤ s) (h1 : |q 1-p 1| ≤ s) :
    ‖q-p‖ ≤ Real.sqrt 2*s := by
  have h0sq := (sq_le_sq₀ (abs_nonneg (q 0-p 0)) hs).2 h0
  have h1sq := (sq_le_sq₀ (abs_nonneg (q 1-p 1)) hs).2 h1
  have hn : ‖q-p‖^2 = (q 0-p 0)^2+(q 1-p 1)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hsqrt := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hpos : 0 ≤ Real.sqrt 2*s := by positivity
  rw [sq_abs] at h0sq h1sq
  nlinarith [norm_nonneg (q-p)]

lemma physicalWeight_le_one (h : ℝ) (g : Plane) : physicalWeight h g ≤ 1 := by
  have hrad : 1 ≤ 1+g 0^2+h^2*g 1^2 := by
    nlinarith [sq_nonneg (g 0), mul_nonneg (sq_nonneg h) (sq_nonneg (g 1))]
  have hsqrt := Real.one_le_sqrt.mpr hrad
  unfold physicalWeight
  exact (div_le_one (by linarith)).2 hsqrt

lemma disk_area (p : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (ball p r) = Real.pi*r^2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal Real.pi_nonneg]
  ring

theorem disk_cylinder_area (p g : Plane) {h M K s : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (hK : 0 ≤ K) (hs : 0 ≤ s) :
    (projectedCylinder h g (ball p (2*(1+M*K)*Real.sqrt 2*s))).area ≤
      8*Real.pi*h*(1+M*K)^2*s^2 := by
  rw [projectedCylinder_area hh, disk_area _ (by positivity)]
  calc
    h*(Real.pi*(2*(1+M*K)*Real.sqrt 2*s)^2)*physicalWeight h g
        ≤ h*(Real.pi*(2*(1+M*K)*Real.sqrt 2*s)^2)*1 :=
          mul_le_mul_of_nonneg_left (physicalWeight_le_one h g) (by positivity)
    _ = 8*Real.pi*h*(1+M*K)^2*s^2 := by
      simp only [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
      ring

theorem disk_cover_of_increment_bound {v : Plane → Plane} {G : Set Plane}
    (p : Plane) {h M K s : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hs : 0 < s)
    (hdist : ∀ q ∈ G, ‖q-p‖ ≤ Real.sqrt 2*s)
    (hinc : ∀ q ∈ G, ‖v q-v p‖ ≤ K*‖q-p‖) :
    let C := projectedCylinder h (v p) (ball p (2*(1+M*K)*Real.sqrt 2*s))
    C.openBounded ∧ physicalRuled h G v M ⊆ C.carrier ∧
      C.area ≤ 8*Real.pi*h*(1+M*K)^2*s^2 := by
  dsimp only
  let r := 2*(1+M*K)*Real.sqrt 2*s
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨⟨projectedCylinder_base_open hh _ isOpen_ball,
    projectedCylinder_base_bounded hh _ isBounded_ball,
    projectedCylinder_base_measurable hh _ isOpen_ball.measurableSet⟩, ?_, ?_⟩
  · apply ProductLocal.ruled_subset_projectedCylinder
    intro q hq x hx
    rw [mem_ball, dist_eq_norm]
    have hnorm : ‖q+x • (v q-v p)-p‖ ≤ (1+M*K)*(Real.sqrt 2*s) := by
      calc
        ‖q+x • (v q-v p)-p‖ = ‖(q-p)+x • (v q-v p)‖ := by congr 1; abel
        _ ≤ ‖q-p‖+‖x • (v q-v p)‖ := norm_add_le _ _
        _ = ‖q-p‖+|x| * ‖v q-v p‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ‖q-p‖+M*(K*‖q-p‖) := by
          gcongr
          exact hinc q hq
        _ = (1+M*K)*‖q-p‖ := by ring
        _ ≤ (1+M*K)*(Real.sqrt 2*s) := by gcongr; exact hdist q hq
    have hsmall : (1+M*K)*(Real.sqrt 2*s) < r := by
      dsimp [r]
      have : 0 < (1+M*K)*(Real.sqrt 2*s) := by positivity
      nlinarith
    exact hnorm.trans_lt hsmall
  · exact disk_cylinder_area p (v p) hh hM hK hs.le

theorem disk_cover_of_derivative_bound {v : Plane → Plane} {G : Set Plane}
    (p : Plane) {h M K s : ℝ} (hh : 0 < h) (hM : 0 ≤ M)
    (hK : 0 ≤ K) (hs : 0 < s)
    (hdist : ∀ q ∈ G, ‖q-p‖ ≤ Real.sqrt 2*s)
    (hv : ∀ q ∈ closedBall p (Real.sqrt 2*s), DifferentiableAt ℝ v q)
    (hder : ∀ q ∈ closedBall p (Real.sqrt 2*s), ‖fderiv ℝ v q‖ ≤ K) :
    let C := projectedCylinder h (v p) (ball p (2*(1+M*K)*Real.sqrt 2*s))
    C.openBounded ∧ physicalRuled h G v M ⊆ C.carrier ∧
      C.area ≤ 8*Real.pi*h*(1+M*K)^2*s^2 := by
  apply disk_cover_of_increment_bound p hh hM hK hs hdist
  intro q hq
  exact (convex_closedBall p (Real.sqrt 2*s)).norm_image_sub_le_of_norm_fderiv_le
    hv hder (mem_closedBall_self (by positivity))
    (by simpa only [mem_closedBall, dist_eq_norm] using hdist q hq)

theorem uniform_residual_disks {D : Set Plane} (hD : IsCompact D)
    {v : Plane → Plane} (hv : SmoothNear 1 D v) {h M : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) :
    ∃ a K : ℝ, 0 < a ∧ 0 < K ∧ ∀ p ∈ D, ∀ s : ℝ,
      0 < s → Real.sqrt 2*s ≤ a → ∀ G : Set Plane,
      (∀ q ∈ G, ‖q-p‖ ≤ Real.sqrt 2*s) →
      let C := projectedCylinder h (v p) (ball p (2*(1+M*K)*Real.sqrt 2*s))
      C.openBounded ∧ physicalRuled h G v M ⊆ C.carrier ∧
        C.area ≤ 8*Real.pi*h*(1+M*K)^2*s^2 := by
  obtain ⟨U,hU,hDU,hvU⟩ := hv
  obtain ⟨a,ha,haU⟩ := hD.exists_cthickening_subset_open hU hDU
  have hdf : ContinuousOn (fderiv ℝ v) (cthickening a D) := by
    intro p hp
    exact ((hvU.contDiffAt (hU.mem_nhds (haU hp))).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  obtain ⟨B,hB⟩ := (hD.cthickening (r := a)).exists_bound_of_continuousOn hdf
  refine ⟨a,max B 1,ha,lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (le_max_right _ _),?_⟩
  intro p hp s hs hsa G hdist
  have hball : closedBall p (Real.sqrt 2*s) ⊆ cthickening a D :=
    (closedBall_subset_cthickening hp _).trans (cthickening_mono hsa D)
  apply disk_cover_of_derivative_bound p hh hM (by positivity) hs hdist
  · intro q hq
    exact (hvU.contDiffAt (hU.mem_nhds (haU (hball hq)))).differentiableAt (by norm_num)
  · intro q hq
    exact (hB q (hball hq)).trans (le_max_left _ _)

theorem summable_residual_cost {ι : Type*} (p g : ι → Plane) (s : ι → ℝ)
    {h M K alpha : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hs : ∀ i, 0 ≤ s i) (hsum : Summable (fun i => (s i)^2))
    (hsmall : (∑' i, (s i)^2) < 2*alpha) :
    let C := fun i => projectedCylinder h (g i)
      (ball (p i) (2*(1+M*K)*Real.sqrt 2*s i))
    Summable (fun i => (C i).area) ∧
      (∑' i, (C i).area) < 16*Real.pi*h*(1+M*K)^2*alpha := by
  dsimp only
  let C := fun i => projectedCylinder h (g i)
    (ball (p i) (2*(1+M*K)*Real.sqrt 2*s i))
  let A := 8*Real.pi*h*(1+M*K)^2
  have hA : 0 < A := by dsimp [A]; positivity
  have hbound (i : ι) : (C i).area ≤ A*(s i)^2 :=
    disk_cylinder_area (p i) (g i) hh hM hK (hs i)
  have hnonneg (i : ι) : 0 ≤ (C i).area := measureReal_nonneg
  have hmajor : Summable (fun i => A*(s i)^2) := hsum.mul_left A
  have hcost : Summable (fun i => (C i).area) :=
    Summable.of_nonneg_of_le hnonneg hbound hmajor
  refine ⟨hcost, ?_⟩
  calc
    (∑' i, (C i).area) ≤ ∑' i, A*(s i)^2 :=
      Summable.tsum_le_tsum hbound hcost hmajor
    _ = A*(∑' i, (s i)^2) := tsum_mul_left
    _ < A*(2*alpha) := mul_lt_mul_of_pos_left hsmall hA
    _ = 16*Real.pi*h*(1+M*K)^2*alpha := by dsimp [A]; ring

theorem logarithmic_summable_cost {ι : Type*} (p : ι → Plane) (v : Plane → Plane)
    (s : ι → ℝ) {X k Kv alpha : ℝ} (hX : 0 ≤ X) (hk : 0 ≤ k) (hKv : 0 ≤ Kv)
    (hs : ∀ i, 0 ≤ s i) (hsum : Summable (fun i => (s i)^2))
    (hsmall : (∑' i, (s i)^2) < 2*alpha) :
    let C := fun i => projectedCylinder 1 (k • v (p i))
      (ball (p i) (2*(1+X*k*Kv)*Real.sqrt 2*s i))
    Summable (fun i => (C i).area) ∧
      (∑' i, (C i).area) < 16*Real.pi*(1+X*k*Kv)^2*alpha := by
  simpa only [mul_assoc X k Kv, mul_one] using
    summable_residual_cost p (fun i => k • v (p i)) s (h := 1)
      (by norm_num) hX (mul_nonneg hk hKv) hs hsum hsmall

end CylinderCovering.ResidualDisk

end

end OAI
