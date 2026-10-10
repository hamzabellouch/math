import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions
import OAI.Geometry.CylinderCovering.Radial.Nilpotent

namespace OAI

open Set

namespace CylinderCovering.RadialSweep

theorem velocity_derivWithin (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    derivWithin D.w (Icc D.α D.β) t = D.lam t • (D.a + t • D.b) :=
  (D.aligned t ht).derivWithin (uniqueDiffOn_Icc D.interval_nonempty t ht)

theorem velocity_contDiffOn (D : Data) : ContDiffOn ℝ 1 D.w (Icc D.α D.β) := by
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc D.interval_nonempty)).mpr
  refine ⟨fun t ht => (D.aligned t ht).differentiableWithinAt, ?_⟩
  have hc : ContinuousOn (fun t => D.lam t • (D.a + t • D.b)) (Icc D.α D.β) :=
    D.scalar_continuous.smul (continuous_const.continuousOn.add
      (continuous_id.continuousOn.smul continuous_const.continuousOn))
  exact hc.congr (fun t ht => velocity_derivWithin D ht)

theorem velocity_hasDerivAt (D : Data) {t : ℝ} (ht : t ∈ Ioo D.α D.β) :
    HasDerivAt D.w (D.lam t • (D.a + t • D.b)) t :=
  (D.aligned t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem velocity_contDiffOn_interior (D : Data) :
    ContDiffOn ℝ 1 D.w (Ioo D.α D.β) :=
  (velocity_contDiffOn D).mono Ioo_subset_Icc_self

end CylinderCovering.RadialSweep

namespace RadialNilpotent

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isOpen_radialSector (e : (ℝ × ℝ) ≃L[ℝ] F) (α β : ℝ) :
    IsOpen {z : F | 0 < (e.symm z).1 ∧
      (e.symm z).2 / (e.symm z).1 ∈ Ioo α β} := by
  have heq : {z : F | 0 < (e.symm z).1 ∧
      (e.symm z).2 / (e.symm z).1 ∈ Ioo α β} =
      {z : F | 0 < (e.symm z).1 ∧
        α * (e.symm z).1 < (e.symm z).2 ∧
        (e.symm z).2 < β * (e.symm z).1} := by
    ext z
    constructor
    · rintro ⟨hz, hα, hβ⟩
      exact ⟨hz, (lt_div_iff₀ hz).mp hα, (div_lt_iff₀ hz).mp hβ⟩
    · rintro ⟨hz, hα, hβ⟩
      exact ⟨hz, (lt_div_iff₀ hz).mpr hα, (div_lt_iff₀ hz).mpr hβ⟩
  rw [heq]
  have hu : Continuous (fun z : F => (e.symm z).1) :=
    continuous_fst.comp e.symm.continuous
  have hv : Continuous (fun z : F => (e.symm z).2) :=
    continuous_snd.comp e.symm.continuous
  exact (isOpen_lt continuous_const hu).inter
    ((isOpen_lt (continuous_const.mul hu) hv).inter
      (isOpen_lt hv (continuous_const.mul hu)))

theorem positive_radial_parameters_unique {a b : F}
    (e : (ℝ × ℝ) ≃L[ℝ] F)
    (he : ∀ u v : ℝ, e (u, v) = u • a + v • b)
    {ρ σ t s : ℝ} (hρ : 0 < ρ)
    (h : ρ • (a + t • b) = σ • (a + s • b)) :
    ρ = σ ∧ t = s := by
  have hc := congrArg e.symm h
  rw [basis_coordinates_radial e he, basis_coordinates_radial e he] at hc
  have hr : ρ = σ := congrArg Prod.fst hc
  have ht : ρ * t = σ * s := congrArg Prod.snd hc
  refine ⟨hr, ?_⟩
  rw [← hr] at ht
  exact (mul_left_cancel₀ (ne_of_gt hρ)) ht

end RadialNilpotent

end OAI
