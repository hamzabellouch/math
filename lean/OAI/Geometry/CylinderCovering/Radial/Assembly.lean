import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions
import OAI.Geometry.CylinderCovering.Radial.Intercept
import OAI.Geometry.CylinderCovering.Radial.Integral
import OAI.Geometry.CylinderCovering.Radial.Riemann
import OAI.Geometry.CylinderCovering.Radial.AreaConvergence
import OAI.Geometry.CylinderCovering.Radial.Projection
import OAI.Geometry.CylinderCovering.Radial.Freezing

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace CylinderCovering.RadialSweep

theorem velocity_difference_integral (D : Data) {c t : ℝ}
    (hc : c ∈ Icc D.α D.β) (ht : t ∈ Icc D.α D.β) :
    D.w t - D.w c = ∫ x in c..t, D.lam x • (D.a + x • D.b) := by
  have hsub : uIcc c t ⊆ Icc D.α D.β := uIcc_subset_Icc hc ht
  have hcont : ContinuousOn (fun x => D.lam x • (D.a + x • D.b)) (Icc D.α D.β) :=
    D.scalar_continuous.smul (continuous_const.continuousOn.add
      (continuous_id.continuousOn.smul continuous_const.continuousOn))
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (D.velocity_continuous.mono hsub) _ ((hcont.mono hsub).intervalIntegrable)
  intro x hx
  have hα : D.α < x := lt_of_le_of_lt (le_min hc.1 ht.1) hx.1
  have hβ : x < D.β := lt_of_lt_of_le hx.2 (max_le hc.2 ht.2)
  exact ((D.aligned x ⟨le_of_lt hα, le_of_lt hβ⟩).hasDerivAt
    (Icc_mem_nhds hα hβ)).hasDerivWithinAt

lemma scalar_le_bound (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    |D.lam t| ≤ scalarBound D := by
  exact le_csSup (isCompact_Icc.bddAbove_image D.scalar_continuous.abs) ⟨t, ht, rfl⟩

lemma cell_midpoint_bound (D : Data) {N : ℕ} {i : Fin N} {t : ℝ}
    (ht : t ∈ RadialRiemann.cell D.α D.β N i) :
    |t - midpoint D N i| ≤ RadialRiemann.step D.α D.β N / 2 := by
  have hstep := RadialRiemann.point_succ D.α D.β N i
  rw [abs_le]
  unfold midpoint
  constructor <;> linarith [ht.1, ht.2]

lemma frozenTriangle_eq (D : Data) (N : ℕ) (i : Fin N) :
    frozenTriangle D N i = TriangularCovering.triangle
      (coordinateMap D (leftTip D N, midpoint D N i * leftTip D N))
      (coordinateMap D (rightEdge D N i, midpoint D N i * rightEdge D N i -
        RadialRiemann.step D.α D.β N / 2 * (rightEdge D N i - leftTip D N)))
      (coordinateMap D (rightEdge D N i, midpoint D N i * rightEdge D N i +
        RadialRiemann.step D.α D.β N / 2 * (rightEdge D N i - leftTip D N))) := rfl

theorem localSweep_frozen_enclosure (D : Data) {N : ℕ} (i : Fin N) {c : ℝ}
    (hc : c ∈ RadialRiemann.cell D.α D.β N i) {z : Space}
    (hz : z ∈ localSweep D N i) :
    ∃ p ∈ frozenTriangle D N i, ∃ s : ℝ, z = p + s • (D.e + D.w c) := by
  obtain ⟨t, ht, ρ, hρ, s, hs, rfl⟩ := hz
  have hci := RadialRiemann.cell_subset D.interval_nonempty i hc
  have hti := RadialRiemann.cell_subset D.interval_nonempty i ht
  have hd := RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt)
  have htc : |t - c| ≤ RadialRiemann.step D.α D.β N := by
    simpa only [Real.dist_eq] using RadialRiemann.cell_dist_le ht hc
  have hR : ρ ≤ RadialRiemann.capMax D.R D.α D.β N i :=
    hρ.2.trans (RadialRiemann.le_capMax D.interval_nonempty D.cap_continuous ht)
  obtain ⟨u, v, huv, hu₀, hu₁, hv⟩ := RadialIntegral.aligned_footprint
    (p0 := D.p₀) D.velocity_continuous D.scalar_continuous D.aligned hci hti
    (scalarBound_nonneg D) D.length_pos.le hd.le (fun x hx => scalar_le_bound D hx)
    htc (cell_midpoint_bound D ht) hs hρ.1 hR
  have htri := RadialFreezing.footprint_subset_triangle
    (radialError_nonneg D) (div_nonneg (radialError_nonneg D) (by norm_num)) hd.le
    hu₀ hu₁ hv
  have hcollar : 2 * (radialError D + radialError D / 2) + 1 = collar D := by
    unfold collar
    ring
  rw [hcollar] at htri
  refine ⟨coordinateMap D (u, v), ?_, s, ?_⟩
  · rw [frozenTriangle_eq]
    simp only [coordinateMap]
    rw [← RadialProjection.coordinate_region_image D.p₀ D.a D.b
      (m := midpoint D N i) (leftTip_lt_rightEdge D (Nat.zero_lt_of_lt i.isLt) i) hd]
    refine ⟨(u, v), ?_, rfl⟩
    change leftTip D N ≤ u ∧ u ≤ rightEdge D N i ∧
      |v - midpoint D N i * u| ≤ RadialRiemann.step D.α D.β N / 2 * (u - leftTip D N)
    simpa only [leftTip, rightEdge, neg_mul, sub_neg_eq_add] using htri
  · dsimp [coordinateMap] at *
    calc
      D.p₀ + ρ • (D.a + t • D.b) + s • (D.e + D.w t) =
          (D.p₀ + ρ • (D.a + t • D.b) + s • (D.w t - D.w c)) +
            s • (D.e + D.w c) := by module
      _ = D.p₀ + u • D.a + v • D.b + s • (D.e + D.w c) := by rw [huv]

lemma direction_ne_zero (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    D.e + D.w t ≠ 0 :=
  RadialProjection.sideways_ne_zero D.normal_unit (D.velocity_perp t ht)

lemma direction_unit (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    ‖direction D t‖ = 1 :=
  TriangularCovering.unit_norm (direction_ne_zero D ht)

lemma frozen_nondegenerate (D : Data) {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    inner ℝ (direction D (tag i))
      (TriangularCovering.cross3 (frozenVertices D N i 1 - frozenVertices D N i 0)
        (frozenVertices D N i 2 - frozenVertices D N i 0)) ≠ 0 := by
  have h := RadialProjection.collar_projection_nondegenerate
    D.p₀ D.e D.a D.b (D.w (tag i))
    (leftTip D N) (rightEdge D N i) (midpoint D N i) (RadialRiemann.step D.α D.β N)
    D.normal_unit D.a_perp D.b_perp
    (D.velocity_perp (tag i) (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt))
    (leftTip_lt_rightEdge D (Nat.zero_lt_of_lt i.isLt) i) (RadialProjection.gram_sqrt_pos D.independent)
  simpa [direction, TriangularCovering.unit, frozenVertices, coordinateMap] using h

def frozenCylinder (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) : TriangularCovering.TriCylinder :=
  TriangularCovering.projectedCylinder (direction D (tag i))
    (direction_unit D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (frozenVertices D N i 0) (frozenVertices D N i 1) (frozenVertices D N i 2)
    (frozen_nondegenerate D tag htag i)

lemma frozenCylinder_axis (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    (frozenCylinder D N tag htag i).axis = direction D (tag i) := rfl

lemma frozenCylinder_base (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    (frozenCylinder D N tag htag i).base = frozenBase D N tag i := rfl

lemma frozenCylinder_area (D : Data) (N : ℕ) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    TriangularCovering.area (frozenCylinder D N tag htag i).base = frozenArea D N tag i := by
  rw [frozenCylinder_base]
  have h := RadialProjection.collar_projection_area D.p₀ D.e D.a D.b (D.w (tag i))
    (leftTip D N) (rightEdge D N i) (midpoint D N i) (RadialRiemann.step D.α D.β N)
    D.normal_unit D.a_perp D.b_perp
    (D.velocity_perp (tag i) (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt)).le
  change TriangularCovering.area (TriangularCovering.projection _ '' frozenTriangle D N i) = _
  rw [frozenTriangle_eq]
  change TriangularCovering.area (TriangularCovering.projection
    (TriangularCovering.unit (D.e + D.w (tag i))) '' _) = _
  simp only [coordinateMap]
  rw [show TriangularCovering.area
      (TriangularCovering.projection (TriangularCovering.unit (D.e + D.w (tag i))) ''
        TriangularCovering.triangle _ _ _) = _ from h]
  unfold frozenArea kappa leftTip rightEdge
  ring

lemma localSweep_mem_frozenCylinder (D : Data) {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) {z : Space}
    (hz : z ∈ localSweep D N i) : z ∈ (frozenCylinder D N tag htag i).carrier := by
  obtain ⟨p, hp, s, hz⟩ := localSweep_frozen_enclosure D i (htag i) hz
  exact TriangularCovering.projectedCylinder_mem_direction
    (D.e + D.w (tag i))
    (direction_ne_zero D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
    (frozenVertices D N i 0) (frozenVertices D N i 1) (frozenVertices D N i 2)
    (frozen_nondegenerate D tag htag i) hp s hz

lemma localSweep_subset_sweep (D : Data) {N : ℕ} (i : Fin N) :
    localSweep D N i ⊆ sweep D := by
  rintro z ⟨t, ht, ρ, hρ, s, hs, hz⟩
  exact ⟨t, RadialRiemann.cell_subset D.interval_nonempty i ht, ρ, hρ, s, hs, hz⟩

lemma sweep_eq_iUnion_localSweep (D : Data) {N : ℕ} (hN : 0 < N) :
    sweep D = ⋃ i : Fin N, localSweep D N i := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, ρ, hρ, s, hs, hz⟩
    obtain ⟨i, hi⟩ := RadialRiemann.exists_cell hN ht
    exact Set.mem_iUnion.mpr ⟨i, t, hi, ρ, hρ, s, hs, hz⟩
  · intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    exact localSweep_subset_sweep D i hi

theorem aligned_radial_sweep : AlignedStatement := by
  intro D tag htag
  refine ⟨fun N => frozenCylinder D N (tag N) (htag N), ?_, ?_⟩
  · intro N hN
    constructor
    · intro i
      exact ⟨frozenCylinder_axis D N (tag N) (htag N) i,
        frozenCylinder_base D N (tag N) (htag N) i,
        frozenCylinder_area D N (tag N) (htag N) i⟩
    · rintro z ⟨t, ht, ρ, hρ, s, hs, hz⟩
      obtain ⟨i, hi⟩ := RadialRiemann.exists_cell hN ht
      exact ⟨i, localSweep_mem_frozenCylinder D (tag N) (htag N) i
        ⟨t, hi, ρ, hρ, s, hs, hz⟩⟩
  · convert frozenArea_tendsto D tag htag using 1
    funext N
    apply Finset.sum_congr rfl
    intro i _
    exact frozenCylinder_area D N (tag N) (htag N) i

end CylinderCovering.RadialSweep

end

end OAI
