import OAI.Geometry.CylinderCovering.Radial.SweepDefinitions
import OAI.Geometry.CylinderCovering.Radial.ActualSweep
import OAI.Geometry.CylinderCovering.Radial.PartitionCover
import OAI.Geometry.CylinderCovering.Radial.Assembly

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace CylinderCovering.RadialSweep

theorem raw_direction_ne_zero (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    D.e + D.w t ≠ 0 := by
  intro h
  have hh := congrArg (fun x => inner ℝ D.e x) h
  simp only [inner_add_right, real_inner_self_eq_norm_sq, D.normal_unit,
    one_pow, D.velocity_perp t ht, add_zero, inner_zero_right] at hh
  norm_num at hh

theorem actual_direction_unit (D : Data) {t : ℝ} (ht : t ∈ Icc D.α D.β) :
    ‖direction D t‖ = 1 := by
  have hn : ‖D.e + D.w t‖ ≠ 0 := norm_ne_zero_iff.mpr (raw_direction_ne_zero D ht)
  rw [direction, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hn]

theorem sweep_compact (D : Data) : IsCompact (sweep D) := by
  simpa only [sweep, mem_Icc, and_assoc] using
    _root_.OAI.RadialActualSweep.compact_radial_sweep isCompact_Icc D.R D.w
      D.cap_continuous D.velocity_continuous D.cap_nonneg D.p₀ D.a D.b D.e D.L

theorem localSweep_compact (D : Data) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    IsCompact (localSweep D N i) := by
  have hsub := RadialPartitionCover.cell_subset_interval D.interval_nonempty.le hN i
  simpa only [localSweep, mem_Icc, and_assoc] using
    _root_.OAI.RadialActualSweep.compact_radial_sweep
      (show IsCompact (RadialRiemann.cell D.α D.β N i) from isCompact_Icc)
      D.R D.w (D.cap_continuous.mono hsub) (D.velocity_continuous.mono hsub)
      (fun t ht => D.cap_nonneg t (hsub ht)) D.p₀ D.a D.b D.e D.L

theorem iUnion_localSweep (D : Data) {N : ℕ} (hN : 0 < N) :
    (⋃ i : Fin N, localSweep D N i) = sweep D := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, t, ht, ρ, hρ, s, hs, hz⟩ := mem_iUnion.mp hz
    exact ⟨t, RadialPartitionCover.cell_subset_interval D.interval_nonempty.le hN i ht,
      ρ, hρ, s, hs, hz⟩
  · rintro ⟨t, ht, ρ, hρ, s, hs, hz⟩
    rw [← RadialPartitionCover.equal_cells_cover D.interval_nonempty.le hN] at ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨i, t, hi, ρ, hρ, s, hs, hz⟩

theorem actualBase_compact (D : Data) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) (i : Fin N) : IsCompact (actualBase D N tag i) :=
  _root_.OAI.RadialActualSweep.compact_projected_image _ (localSweep_compact D hN i)

theorem actualBase_covers (D : Data) {N : ℕ} (hN : 0 < N) (tag : Fin N → ℝ) :
    ∀ z ∈ sweep D, ∃ i : Fin N,
      z ∈ cylinder (direction D (tag i)) (actualBase D N tag i) := by
  intro z hz
  rw [← iUnion_localSweep D hN] at hz
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  exact ⟨i, _root_.OAI.RadialActualSweep.subset_projected_cylinder _ _ hi⟩

theorem actualSweepStatement_of_aligned
    (hAligned : AlignedStatement)
    (hlocal : ∀ (D : Data) (N : ℕ), 0 < N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag → ∀ i : Fin N,
        actualBase D N tag i ⊆ frozenBase D N tag i) :
    ActualSweepStatement := by
  intro D tag htag
  obtain ⟨C, hC, hlim⟩ := hAligned D tag htag
  have hbase (N : ℕ) (hN : 0 < N) (i : Fin N) :
      (C N i).base = frozenBase D N (tag N) i := ((hC N hN).1 i).2.1
  have hinc (N : ℕ) (hN : 0 < N) (i : Fin N) :
      actualBase D N (tag N) i ⊆ (C N i).base := by
    rw [hbase N hN i]
    exact hlocal D N hN (tag N) (htag N) i
  have hle (N : ℕ) (hN : 0 < N) :
      actualCost D N (tag N) ≤ TriangularCovering.totalArea (C N) := by
    apply Finset.sum_le_sum
    intro i _
    exact ENNReal.toReal_mono (C N i).finite_area (measure_mono (hinc N hN i))
  have hle_eventually : (fun N => actualCost D N (tag N)) ≤ᶠ[atTop]
      (fun N => TriangularCovering.totalArea (C N)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact hle N hN
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    refine ⟨?_, actualBase_covers D hN (tag N)⟩
    intro i
    have ht : tag N i ∈ Icc D.α D.β :=
      RadialPartitionCover.cell_subset_interval D.interval_nonempty.le hN i (htag N i)
    have hu : ‖direction D (tag N i)‖ = 1 := actual_direction_unit D ht
    have hc := actualBase_compact D hN (tag N) i
    refine ⟨hu, hc, hc.measurableSet, ?_, ?_, hlocal D N hN (tag N) (htag N) i⟩
    · exact ne_top_of_le_ne_top (C N i).finite_area (measure_mono (hinc N hN i))
    · exact _root_.OAI.RadialActualSweep.projected_image_perpendicular hu (localSweep D N i)
  · intro ε hε
    have hupper : ∀ᶠ N in atTop, TriangularCovering.totalArea (C N) < weightedArea D + ε :=
      hlim.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
    filter_upwards [hle_eventually, hupper] with N hN hupperN
    exact hN.trans hupperN.le
  · apply _root_.OAI.RadialActualSweep.limsup_le_of_nonneg_of_le_tendsto
    · intro N
      exact Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
    · exact hle_eventually
    · exact hlim

theorem actualBase_subset_frozenBase (D : Data) {N : ℕ}
    (tag : Fin N → ℝ) (htag : RadialRiemann.IsTagged D.α D.β N tag) (i : Fin N) :
    actualBase D N tag i ⊆ frozenBase D N tag i := by
  apply _root_.OAI.RadialActualSweep.projected_image_subset_of_intercepts
    (direction_unit D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
  intro z hz
  obtain ⟨p, hp, s, hz⟩ := localSweep_frozen_enclosure D i (htag i) hz
  refine ⟨p, hp, s * ‖D.e + D.w (tag i)‖, ?_⟩
  rw [hz, direction, smul_smul]
  congr 1
  congr 1
  have hn : ‖D.e + D.w (tag i)‖ ≠ 0 := norm_ne_zero_iff.mpr
    (direction_ne_zero D (RadialRiemann.cell_subset D.interval_nonempty i (htag i)))
  field_simp

theorem actual_radial_sweep : ActualSweepStatement := by
  apply actualSweepStatement_of_aligned aligned_radial_sweep
  intro D N hN tag htag i
  exact actualBase_subset_frozenBase D tag htag i

end CylinderCovering.RadialSweep

end

end OAI
