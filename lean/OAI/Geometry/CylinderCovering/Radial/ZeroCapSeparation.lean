import OAI.Geometry.CylinderCovering.Radial.ZeroCapDefinitions
import OAI.Geometry.CylinderCovering.Radial.ActualEndpoint

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace CylinderCovering.RadialSweep

@[simp] theorem zeroCapData_kappa (D : Data) : kappa (zeroCapData D) = kappa D := rfl

@[simp] theorem zeroCapData_direction (D : Data) (t : ℝ) :
    direction (zeroCapData D) t = D.e := by
  simp [direction, zeroCapData, D.normal_unit]

@[simp] theorem zeroCapData_scalarBound (D : Data) : scalarBound (zeroCapData D) = 0 := by
  simp only [scalarBound, zeroCapData, abs_zero]
  rw [(nonempty_Icc.mpr D.interval_nonempty.le).image_const, csSup_singleton]

@[simp] theorem zeroCapData_radialError (D : Data) : radialError (zeroCapData D) = 0 := by
  simp [radialError]

@[simp] theorem zeroCapData_collar (D : Data) : collar (zeroCapData D) = 1 := by
  simp [collar]

@[simp] theorem zeroCapData_capMax (D : Data) {N : ℕ} (i : Fin N) :
    RadialRiemann.capMax (zeroCapData D).R D.α D.β N i = 0 := by
  change sSup ((fun _ : ℝ => (0 : ℝ)) '' RadialRiemann.cell D.α D.β N i) = 0
  rw [(RadialRiemann.cell_nonempty D.interval_nonempty i).image_const, csSup_singleton]

@[simp] theorem zeroCapData_weightedArea (D : Data) : weightedArea (zeroCapData D) = 0 := by
  simp [weightedArea, zeroCapData]

theorem zeroCapData_sweep (D : Data) :
    sweep (zeroCapData D) = {z | ∃ s : ℝ, |s| ≤ D.L ∧ z = s • D.e} := by
  ext z
  constructor
  · rintro ⟨t, ht, ρ, hρ, s, hs, hz⟩
    have hρ0 : ρ = 0 := le_antisymm hρ.2 hρ.1
    exact ⟨s, hs, by simpa [zeroCapData, hρ0] using hz⟩
  · rintro ⟨s, hs, hz⟩
    refine ⟨D.α, ⟨le_rfl, D.interval_nonempty.le⟩, 0, ⟨le_rfl, le_rfl⟩, s, hs, ?_⟩
    simpa [zeroCapData] using hz

theorem zeroCapData_localSweep (D : Data) {N : ℕ} (i : Fin N) :
    localSweep (zeroCapData D) N i = {z | ∃ s : ℝ, |s| ≤ D.L ∧ z = s • D.e} := by
  ext z
  constructor
  · rintro ⟨t, ht, ρ, hρ, s, hs, hz⟩
    have hρ0 : ρ = 0 := le_antisymm hρ.2 hρ.1
    exact ⟨s, hs, by simpa [zeroCapData, hρ0] using hz⟩
  · rintro ⟨s, hs, hz⟩
    obtain ⟨t, ht⟩ := RadialRiemann.cell_nonempty D.interval_nonempty i
    refine ⟨t, ht, 0, ⟨le_rfl, le_rfl⟩, s, hs, ?_⟩
    simpa [zeroCapData] using hz

theorem zeroCapData_actualBase (D : Data) {N : ℕ} (tag : Fin N → ℝ) (i : Fin N) :
    actualBase (zeroCapData D) N tag i = {0} := by
  rw [actualBase, zeroCapData_direction, zeroCapData_localSweep]
  ext z
  constructor
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    simp [TriangularCovering.projection, inner_smul_right, D.normal_unit]
  · intro hz
    have hz0 : z = 0 := mem_singleton_iff.mp hz
    subst z
    refine ⟨0, ⟨0, ?_, by simp⟩, ?_⟩
    · simpa using D.length_pos.le
    · simp [TriangularCovering.projection]

theorem zeroCapData_frozenArea (D : Data) {N : ℕ} (tag : Fin N → ℝ) (i : Fin N) :
    frozenArea (zeroCapData D) N tag i = kappa D * (RadialRiemann.step D.α D.β N)^3 / 2 := by
  unfold frozenArea
  simp only [zeroCapData_kappa, zeroCapData_radialError, zeroCapData_collar,
    zero_add, one_mul]
  change kappa D * RadialRiemann.step D.α D.β N *
    (RadialRiemann.capMax (zeroCapData D).R D.α D.β N i +
      RadialRiemann.step D.α D.β N)^2 / (2 * Real.sqrt (1 + ‖(0 : Space)‖^2)) = _
  rw [zeroCapData_capMax]
  simp only [zero_add, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, Real.sqrt_one, mul_one]
  ring

@[simp] theorem zeroCapData_actualBase_area (D : Data) {N : ℕ}
    (tag : Fin N → ℝ) (i : Fin N) :
    TriangularCovering.area (actualBase (zeroCapData D) N tag i) = 0 := by
  rw [zeroCapData_actualBase]
  let : NullSingletonClass (Measure.hausdorffMeasure (2 : ℝ) : Measure Space) :=
    Measure.nullSingletonClass_hausdorff Space (by norm_num)
  simp [TriangularCovering.area, Measure.euclideanHausdorffMeasure, Measure.smul_apply]

@[simp] theorem zeroCapData_actualCost (D : Data) (N : ℕ) (tag : Fin N → ℝ) :
    actualCost (zeroCapData D) N tag = 0 := by
  simp [actualCost]

theorem zeroCapData_frozenArea_pos (D : Data) {N : ℕ}
    (tag : Fin N → ℝ) (i : Fin N) :
    0 < frozenArea (zeroCapData D) N tag i := by
  rw [zeroCapData_frozenArea]
  have hκ : 0 < kappa D := RadialProjection.gram_sqrt_pos D.independent
  have hd := RadialRiemann.step_pos D.interval_nonempty (Nat.zero_lt_of_lt i.isLt)
  positivity

theorem zeroCapData_frozenArea_sum (D : Data) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) :
    (∑ i : Fin N, frozenArea (zeroCapData D) N tag i) =
      kappa D * (D.β - D.α)^3 / (2 * (N : ℝ)^2) := by
  simp_rw [zeroCapData_frozenArea]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
  unfold RadialRiemann.step
  field_simp

theorem zeroCapData_frozenBase_area (D : Data) {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    TriangularCovering.area (frozenBase (zeroCapData D) N tag i) =
      kappa D * (RadialRiemann.step D.α D.β N)^3 / 2 := by
  change RadialRiemann.IsTagged (zeroCapData D).α (zeroCapData D).β N tag at htag
  rw [← frozenCylinder_base (zeroCapData D) N tag htag i,
    frozenCylinder_area, zeroCapData_frozenArea]

theorem zeroCapData_actualBase_ssubset (D : Data) {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    actualBase (zeroCapData D) N tag i ⊂ frozenBase (zeroCapData D) N tag i := by
  change RadialRiemann.IsTagged (zeroCapData D).α (zeroCapData D).β N tag at htag
  refine ssubset_iff_subset_ne.mpr ⟨actualBase_subset_frozenBase (zeroCapData D) tag htag i, ?_⟩
  intro heq
  have harea := congrArg TriangularCovering.area heq
  rw [zeroCapData_actualBase_area, ← frozenCylinder_base (zeroCapData D) N tag htag i,
    frozenCylinder_area] at harea
  exact (ne_of_gt (zeroCapData_frozenArea_pos D tag i)) harea.symm

theorem zeroCapData_totalArea (D : Data) {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged D.α D.β N tag) :
    TriangularCovering.totalArea (frozenCylinder (zeroCapData D) N tag htag) =
      kappa D * (D.β - D.α)^3 / (2 * (N : ℝ)^2) := by
  change RadialRiemann.IsTagged (zeroCapData D).α (zeroCapData D).β N tag at htag
  unfold TriangularCovering.totalArea
  simp_rw [frozenCylinder_area]
  exact zeroCapData_frozenArea_sum D hN tag

theorem zeroCapData_actualCost_lt_totalArea (D : Data) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) (htag : RadialRiemann.IsTagged D.α D.β N tag) :
    actualCost (zeroCapData D) N tag <
      TriangularCovering.totalArea (frozenCylinder (zeroCapData D) N tag htag) := by
  rw [zeroCapData_actualCost, zeroCapData_totalArea D hN]
  have hκ : 0 < kappa D := RadialProjection.gram_sqrt_pos D.independent
  have hinterval : 0 < D.β - D.α := sub_pos.mpr D.interval_nonempty
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  positivity

theorem zeroCapData_totalArea_tendsto (D : Data) (tag : (N : ℕ) → Fin N → ℝ)
    (htag : ∀ N, RadialRiemann.IsTagged D.α D.β N (tag N)) :
    Tendsto (fun N => TriangularCovering.totalArea
      (frozenCylinder (zeroCapData D) N (tag N) (htag N))) atTop (𝓝 0) := by
  change ∀ N, RadialRiemann.IsTagged (zeroCapData D).α (zeroCapData D).β N (tag N) at htag
  have h := frozenArea_tendsto (zeroCapData D) tag htag
  simpa only [TriangularCovering.totalArea, frozenCylinder_area,
    zeroCapData_weightedArea] using h

end CylinderCovering.RadialSweep

end

end OAI
