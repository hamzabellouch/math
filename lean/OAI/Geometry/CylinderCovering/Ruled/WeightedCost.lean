import OAI.Geometry.CylinderCovering.Ruled.SquareArea
import OAI.Geometry.CylinderCovering.Ruled.Patch
import OAI.Geometry.CylinderCovering.Ruled.RetentionArea
import OAI.Geometry.CylinderCovering.Physical.WeightLipschitz

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RuledApproximation.OrthogonalRetention

lemma retained_velocity_bound {S : Set Plane} (p v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane)
    {κ ell M radius : ℝ} (hA : ‖A‖ ≤ κ) (hell : 0 < ell)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M) {ij : ℤ × ℤ}
    (hij : ij ∈ retained S p R ell M radius) :
    ‖affineVelocity p v₀ A (center p R ell ij) - v₀‖ ≤ κ * (M + radius) := by
  obtain ⟨w, hw, hcw⟩ := (mem_retained_iff p R hell hM ij).mp hij
  have hcp : ‖center p R ell ij - p‖ ≤ M + radius := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (center p R ell ij) w p
    have hwM := hM w hw
    linarith
  have hκ0 : 0 ≤ κ := (norm_nonneg A).trans hA
  simp only [affineVelocity, add_sub_cancel_left]
  exact (A.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hcp hκ0))

lemma retained_weight_bound {S : Set Plane} (p v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane)
    (h : ℝ) {κ ell M radius : ℝ} (hA : ‖A‖ ≤ κ) (hell : 0 < ell)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M) {ij : ℤ × ℤ}
    (hij : ij ∈ retained S p R ell M radius) :
    |physicalWeight h (affineVelocity p v₀ A (center p R ell ij)) - physicalWeight h v₀| ≤
      max 1 |h| * κ * (M + radius) := by
  have hL : 0 ≤ max 1 |h| := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  exact (physicalWeight_difference_le h _ _).trans ((mul_le_mul_of_nonneg_left
    (retained_velocity_bound p v₀ R A hA hell hM hij) hL).trans_eq (by ring))

lemma physicalFamily_totalArea {h : ℝ} (hh : 0 < h) (p v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane) (ell : ℝ)
    (F : Finset (ℤ × ℤ)) :
    familyArea (physicalFamily h p v₀ R A ell F) = h * ell ^ 2 *
      ∑ ij ∈ F, physicalWeight h (affineVelocity p v₀ A (center p R ell ij)) := by
  classical
  let f : ℤ × ℤ → ℝ := fun ij => physicalWeight h (affineVelocity p v₀ A (center p R ell ij))
  have hs : (∑ i : Fin F.card, f (F.equivFin.symm i)) = ∑ ij ∈ F, f ij := by
    rw [F.equivFin.symm.sum_comp (fun ij : F => f ij), Finset.sum_coe_sort]
  unfold familyArea
  simp_rw [physicalFamily_area_exact hh]
  rw [← Finset.mul_sum]
  exact congrArg (fun x => h * ell ^ 2 * x) hs

theorem retained_local_cost {S : Set Plane} (p q v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane)
    {h κ ell M radius a : ℝ} (hh : 0 < h) (hA : ‖A‖ ≤ κ)
    (hell : 0 < ell) (hM0 : 0 ≤ M) (hr : 0 ≤ radius) (ha : 0 ≤ a)
    (hM : ∀ w ∈ S, ‖w - p‖ ≤ M)
    (hS : ∀ w ∈ S, ∀ k, |w k - q k| ≤ a / 2) :
    familyArea (physicalFamily h p v₀ R A ell (retained S p R ell M radius)) ≤
      h * (a + 2 * radius + 2 * ell) ^ 2 *
        (physicalWeight h v₀ + max 1 |h| * κ * (M + radius)) := by
  classical
  let F := retained S p R ell M radius
  let B := physicalWeight h v₀ + max 1 |h| * κ * (M + radius)
  have hκ0 : 0 ≤ κ := (norm_nonneg A).trans hA
  have hB : 0 ≤ B := by
    have hw := (physicalWeight_pos h v₀).le
    dsimp [B]
    positivity
  have hsum : (∑ ij ∈ F, physicalWeight h
      (affineVelocity p v₀ A (center p R ell ij))) ≤ (F.card : ℝ) * B := by
    calc
      _ ≤ ∑ _ij ∈ F, B := by
        apply Finset.sum_le_sum
        intro ij hij
        have hw := (abs_le.mp (retained_weight_bound p v₀ R A h hA hell hM hij)).2
        dsimp [B]
        linarith
      _ = _ := by simp
  have hcount := retained_card_area_bound p q R ha hell hr hM hS
  rw [physicalFamily_totalArea hh]
  calc
    _ ≤ h * ell ^ 2 * ((F.card : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = h * ((F.card : ℝ) * ell ^ 2) * B := by ring
    _ ≤ h * (a + 2 * radius + 2 * ell) ^ 2 * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hh.le) hB

lemma coarse_patch_norm_bound {S : Set Plane} (p q : Plane) {a : ℝ}
    (ha : 0 ≤ a) (hp : ∀ k, |p k - q k| ≤ a / 2)
    (hS : ∀ w ∈ S, ∀ k, |w k - q k| ≤ a / 2) :
    ∀ w ∈ S, ‖w - p‖ ≤ Real.sqrt 2 * a := by
  intro w hw
  have hc (k : Fin 2) : |w k - p k| ≤ a := by
    have htriangle := abs_sub_le (w k) (q k) (p k)
    rw [abs_sub_comm (q k) (p k)] at htriangle
    linarith [hS w hw k, hp k]
  have h0 : (w 0 - p 0) ^ 2 ≤ a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (hc 0)
  have h1 : (w 1 - p 1) ^ 2 ≤ a ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr (hc 1)
  have hn := norm_plane_sq (w - p)
  simp only [PiLp.sub_apply] at hn
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hsA : (Real.sqrt 2 * a)^2 = 2*a^2 := by rw [mul_pow, hs]
  have hp0 : 0 ≤ Real.sqrt 2 * a := mul_nonneg (Real.sqrt_nonneg _) ha
  nlinarith [norm_nonneg (w-p)]

theorem retained_local_cost_eventually {h κ : ℝ} (hh : 0 < h) (_ : 0 ≤ κ)
    {r : ℝ → ℝ} (hr : r =o[𝓝[>] (0:ℝ)] (fun a => a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in 𝓝[>] (0:ℝ), ∀ (p q v₀ : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
      (A : Plane →L[ℝ] Plane) (S : Set Plane), ‖A‖ ≤ κ → 0 ≤ r a →
      (∀ w ∈ S, ‖w-p‖ ≤ Real.sqrt 2 * a) →
      (∀ w ∈ S, ∀ k, |w k-q k| ≤ a/2) →
      familyArea (physicalFamily h p v₀ R A (a^2)
        (retained S p R (a^2) (Real.sqrt 2*a) (r a))) ≤
          h * a^2 * (physicalWeight h v₀ + ε) := by
  let E : ℝ → ℝ := fun a => (a + 2*r a + 2*a^2)^2 / a^2
  let W : ℝ → ℝ := fun a => max 1 |h| * κ * (Real.sqrt 2*a + r a)
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hr0 : Tendsto r (𝓝[>] (0:ℝ)) (𝓝 0) := hr.trans_tendsto hid
  have hE : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 1) := retained_area_factor_tendsto hr
  have hW : Tendsto W (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa [W] using ((hid.const_mul (Real.sqrt 2)).add hr0).const_mul (max 1 |h| * κ)
  have hlim : Tendsto (fun a => E a * (1 + W a) - 1) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (hE.mul (hW.const_add 1)).sub_const 1
  have hsmall := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hsmall] with a ha hsmall
  intro p q v₀ R A S hA hrpos hM hS
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hane : a ≠ 0 := ne_of_gt ha
  have hanonneg : 0 ≤ a := le_of_lt ha
  have hbound := retained_local_cost p q v₀ R A hh hA ha2
    (mul_nonneg (Real.sqrt_nonneg _) ha.le) hrpos ha.le hM hS
  have hEa : 1 ≤ E a := by
    apply (le_div_iff₀ ha2).2
    have hbase : a ≤ a + 2*r a + 2*a^2 := by nlinarith [sq_nonneg a]
    have hs := (sq_le_sq₀ ha.le (by positivity : 0 ≤ a + 2*r a + 2*a^2)).mpr hbase
    simpa using hs
  have hJ := physicalWeight_le_one h v₀
  have hscalar : E a * (physicalWeight h v₀ + W a) ≤ physicalWeight h v₀ + ε := by
    have hextra := mul_nonneg (sub_nonneg.mpr hEa) (sub_nonneg.mpr hJ)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hscalar (by positivity : 0 ≤ h * a^2)
  have heq : h * a^2 * (E a * (physicalWeight h v₀ + W a)) =
      h * (a + 2*r a + 2*a^2)^2 *
        (physicalWeight h v₀ + max 1 |h| * κ * (Real.sqrt 2*a + r a)) := by
    dsimp [E, W]
    field_simp [hane]
  exact hbound.trans (heq ▸ hmul)

theorem local_orthogonal_approximation {h κ : ℝ} (hh : 0 < h)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) {η : ℝ → ℝ}
    (hη : Tendsto η (𝓝[>] (0:ℝ)) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in 𝓝[>] (0:ℝ), ∀ (p q v₀ : Plane)
      (A : Plane →L[ℝ] Plane) (v : Plane → Plane) (D S : Set Plane),
      D ⊆ S → (∀ k, |p k-q k| ≤ a/2) →
      (∀ w ∈ S, ∀ k, |w k-q k| ≤ a/2) →
      LinearMap.trace ℝ Plane A.toLinearMap = 0 →
      LinearMap.det A.toLinearMap < 0 → ‖A‖ ≤ κ → 0 ≤ η a →
      (∀ w ∈ D, ‖v w-affineVelocity p v₀ A w‖ ≤ η a*a) →
      ∃ R : Plane ≃ₗᵢ[ℝ] Plane,
        let F := retained S p R (a^2) (Real.sqrt 2*a) (meshRadius κ η a)
        (∀ i, (physicalFamily h p v₀ R A (a^2) F i).parallelogram) ∧
        physicalRuled h D v 1 ⊆ familySet (physicalFamily h p v₀ R A (a^2) F) ∧
        familyArea (physicalFamily h p v₀ R A (a^2) F) ≤
          h*a^2*(physicalWeight h v₀+ε) ∧
        (F.card : ℝ)*(a^2)^2 ≤ (a+2*meshRadius κ η a+2*a^2)^2 := by
  have hcost := retained_local_cost_eventually hh hκ0 (meshRadius_isLittleO κ hη) hε
  filter_upwards [self_mem_nhdsWithin, hcost] with a ha hcost
  intro p q v₀ A v D S hDS hp hS htrace hdet hA hη0 herror
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hM := coarse_patch_norm_bound p q ha.le hp hS
  have hr : 0 ≤ meshRadius κ η a := by
    unfold meshRadius
    exact div_nonneg (add_nonneg (sq_nonneg a) (mul_nonneg hη0 ha.le)) (by linarith)
  obtain ⟨R, hshape, hcover, _hcount⟩ := physical_patch_cover hDS p v₀ A v
    htrace hdet hA hκ1 ha2 hh hM herror
  refine ⟨R, hshape, hcover, hcost p q v₀ R A S hA hr hM hS, ?_⟩
  exact retained_card_area_bound p q R ha.le ha2 hr hM hS

end RuledApproximation.OrthogonalRetention

end

end OAI
