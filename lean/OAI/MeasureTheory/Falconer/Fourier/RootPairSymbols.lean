import OAI.MeasureTheory.Falconer.Estimates.RootPairDerivatives

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

noncomputable def rootPairSymbol (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (dir : UnitCircle) : ℂ :=
  (d.mask N sig z.1 dir : ℂ)*(e.mask N sig z.2 dir : ℂ)

noncomputable def rootPairMask (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) : ℝ :=
  d.mask N sig z.1 (sourceRadialUnit z.2 z.1) *
    e.mask N sig z.2 (sourceRadialUnit z.2 z.1)

noncomputable def rootSpatialWeight (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) : ℝ :=
  (dist z.1 z.2)^(-(1/2:ℝ)) * rootPairMask d e N sig z

theorem rootPairSymbol_inherited (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) (dir : UnitCircle) :
    rootPairSymbol d e N sig z dir =
      d.symbol N sig (fun _ => 0) (fun _ => 1) z.1 dir *
      conj (e.symbol N sig (fun _ => 0) (fun _ => 1) z.2 dir) := by
  rw [RootEndpointData.symbol_zero,RootEndpointData.symbol_zero,Complex.conj_ofReal]
  rfl

theorem rootPairSymbol_radial (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (z : Plane × Plane) :
    rootPairSymbol d e N sig z (sourceRadialUnit z.2 z.1) = (rootPairMask d e N sig z : ℂ) := by
  simp only [rootPairSymbol,rootPairMask,Complex.ofReal_mul]

theorem rootPairMask_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measurable (rootPairMask d e N sig) := by
  have h₁ := (d.mask_measurable N sig).comp
    (f := fun z : Plane × Plane => (z.1,sourceRadialUnit z.2 z.1))
    (measurable_fst.prodMk measurable_pairRadialUnit)
  have h₂ := (e.mask_measurable N sig).comp
    (f := fun z : Plane × Plane => (z.2,sourceRadialUnit z.2 z.1))
    (measurable_snd.prodMk measurable_pairRadialUnit)
  exact h₁.mul h₂

theorem rootPairMask_bounds (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) :
    0 ≤ rootPairMask d e N sig z ∧ rootPairMask d e N sig z ≤ 1 := by
  have h₁ := d.mask_bounds hd N sig z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := e.mask_bounds he N sig z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,(mul_le_of_le_one_left h₂.1 h₁.2).trans h₂.2⟩

theorem rootSpatialWeight_measurable (d e : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measurable (rootSpatialWeight d e N sig) :=
  ((continuous_fst.dist continuous_snd).measurable.pow_const _).mul (rootPairMask_measurable d e N sig)

theorem rootSpatialWeight_nonneg (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) : 0 ≤ rootSpatialWeight d e N sig z :=
  mul_nonneg (Real.rpow_nonneg dist_nonneg _) (rootPairMask_bounds d e hd he N sig z).1

theorem rootSpatialWeight_le (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) {δ : ℝ} (hδ : 0 < δ) {z : Plane × Plane} (hz : δ ≤ dist z.1 z.2) :
    rootSpatialWeight d e N sig z ≤ δ^(-(1/2:ℝ)) := by
  apply (mul_le_of_le_one_right (Real.rpow_nonneg dist_nonneg _)
    (rootPairMask_bounds d e hd he N sig z).2).trans
  exact Real.rpow_le_rpow_of_nonpos hδ hz (by norm_num)

end PlanarFalconer

end OAI
