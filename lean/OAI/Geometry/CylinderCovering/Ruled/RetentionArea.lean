import OAI.Geometry.CylinderCovering.Ruled.Retention
import OAI.Geometry.CylinderCovering.Nilpotent.RetainedArea

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace RuledApproximation.OrthogonalRetention

private def coarseBox (q : Plane) (r : ℝ) : Set Plane :=
  {x | ∀ k, |x k - q k| ≤ r}

private lemma coarseBox_eq (q : Plane) (r : ℝ) :
    coarseBox q r = WithLp.ofLp ⁻¹' Set.pi univ (fun k => Icc (q k-r) (q k+r)) := by
  ext x
  simp only [coarseBox, mem_ofPred_eq, mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  constructor <;> intro h k <;> have hk := h k <;> rw [abs_le] at * <;>
    constructor <;> linarith

private lemma coarseBox_volume (q : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coarseBox q r) = (2*r)^2 := by
  rw [coarseBox_eq, measureReal_def,
    (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage_emb
      (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.measurableEmbedding,
    volume_pi_pi]
  simp only [Real.volume_Icc, Fin.prod_univ_two]
  rw [ENNReal.toReal_mul]
  simp only [show ∀ a : ℝ, a+r-(a-r)=2*r by intro a; ring,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*r)]
  ring

private lemma coarseBox_compact (q : Plane) (r : ℝ) : IsCompact (coarseBox q r) := by
  rw [coarseBox_eq]
  exact (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem finite_grid_card_area_bound (p q : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
    {a ell r : ℝ} (ha : 0 ≤ a) (hell : 0 < ell) (hr : 0 ≤ r)
    (F : Finset (ℤ × ℤ))
    (hF : ∀ ij ∈ F, ∃ w : Plane,
      (∀ k, |w k - q k| ≤ a/2) ∧ ‖center p R ell ij - w‖ ≤ r) :
    (F.card : ℝ) * ell^2 ≤ (a + 2*r + 2*ell)^2 := by
  have hsub : ∀ ij ∈ F, CylinderCovering.NilpotentRate.tile R ell ij ⊆
      coarseBox (q-p) (a/2+r+ell) := by
    intro ij hij
    obtain ⟨w, hw, hdist⟩ := hF ij hij
    rintro x ⟨u, hu, rfl⟩ k
    have heq : ell • R (CylinderCovering.NilpotentRate.integerVector ij + u) - (w-p) =
        ell • R u + (center p R ell ij - w) := by
      simp only [CylinderCovering.NilpotentRate.integerVector, center, map_add, smul_add]
      module
    have hnorm : ‖ell • R (CylinderCovering.NilpotentRate.integerVector ij + u) - (w-p)‖ ≤
        ell + r := by
      rw [heq]
      exact (norm_add_le _ _).trans (add_le_add (square_error_bound R hell.le hu) hdist)
    have hcoord := (plane_coordinate_le
      (ell • R (CylinderCovering.NilpotentRate.integerVector ij + u) - (w-p)) k).trans hnorm
    change |(ell • R (CylinderCovering.NilpotentRate.integerVector ij + u)) k -
      (q-p) k| ≤ a/2+r+ell
    calc
      _ = |(ell • R (CylinderCovering.NilpotentRate.integerVector ij + u) - (w-p)) k +
          (w k-q k)| := by congr 1; simp only [PiLp.sub_apply]; ring
      _ ≤ |(ell • R (CylinderCovering.NilpotentRate.integerVector ij + u) - (w-p)) k| +
          |w k-q k| := abs_add_le _ _
      _ ≤ (ell+r)+a/2 := add_le_add hcoord (hw k)
      _ = _ := by ring
  have harea := CylinderCovering.NilpotentRate.sum_tile_area_le_container R hell F
    ((coarseBox_compact (q-p) (a/2+r+ell)).measure_ne_top (μ := volume)) hsub
  simp only [CylinderCovering.NilpotentRate.tile_area R hell, Finset.sum_const,
    nsmul_eq_mul] at harea
  rw [coarseBox_volume _ (by positivity)] at harea
  convert harea using 1
  ring

theorem retained_card_area_bound {S : Set Plane} (p q : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) {a ell M r : ℝ}
    (ha : 0 ≤ a) (hell : 0 < ell) (hr : 0 ≤ r)
    (hM : ∀ w ∈ S, ‖w-p‖ ≤ M)
    (hS : ∀ w ∈ S, ∀ k, |w k-q k| ≤ a/2) :
    ((retained S p R ell M r).card : ℝ) * ell^2 ≤ (a+2*r+2*ell)^2 := by
  apply finite_grid_card_area_bound p q R ha hell hr
  intro ij hij
  obtain ⟨w, hw, hdist⟩ := (mem_retained_iff p R hell hM ij).mp hij
  exact ⟨w, hS w hw, hdist⟩

theorem retained_area_factor_tendsto {r : ℝ → ℝ}
    (hr : r =o[𝓝[>] (0:ℝ)] (fun a => a)) :
    Tendsto (fun a => (a+2*r a+2*a^2)^2/a^2) (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have ha : Tendsto (fun a : ℝ => a) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h := ((hr.tendsto_div_nhds_zero.const_mul 2).const_add 1).add (ha.const_mul 2)
  have hlim : Tendsto (fun a => (1+2*(r a/a)+2*a)^2) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    simpa using h.pow 2
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hane : a ≠ 0 := ne_of_gt ha
  field_simp

theorem retained_card_area_eventually {r : ℝ → ℝ}
    (hr : r =o[𝓝[>] (0:ℝ)] (fun a => a)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℝ in 𝓝[>] (0:ℝ), ∀ (p q : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane)
      (S : Set Plane) (M : ℝ), 0 ≤ r a →
      (∀ w ∈ S, ‖w-p‖ ≤ M) → (∀ w ∈ S, ∀ k, |w k-q k| ≤ a/2) →
      ((retained S p R (a^2) M (r a)).card : ℝ) * (a^2)^2 ≤ (1+ε)*a^2 := by
  have hf := (retained_area_factor_tendsto hr).eventually
    (gt_mem_nhds (by linarith : (1:ℝ) < 1+ε))
  filter_upwards [self_mem_nhdsWithin, hf] with a ha hf
  intro p q R S M hr0 hM hS
  have hbound := retained_card_area_bound p q R (le_of_lt ha) (sq_pos_of_pos ha) hr0 hM hS
  have hfactor := (div_lt_iff₀ (sq_pos_of_pos ha)).mp hf
  exact hbound.trans hfactor.le

end RuledApproximation.OrthogonalRetention

end

end OAI
