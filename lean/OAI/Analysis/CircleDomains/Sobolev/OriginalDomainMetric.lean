import OAI.Analysis.CircleDomains.Transfer.FilledMetric
import OAI.Analysis.CircleDomains.Uniformization.ConformalMetric

namespace OAI

/-!
# Charging the completed surface to the original domain

Inside every added disk the coordinate differential has rank at most one.
Consequently the completed surface's wedge integral is bounded by the
original-domain integral; no extension or integrability of the original
coordinates in the missing disks is needed.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem coordinateWedges_nonneg (f : ℕ → (ℝ × ℝ) → ℝ) (n : ℕ) (z : ℝ × ℝ) :
    0 ≤ coordinateWedges f n z := by
  unfold coordinateWedges covectorWedges
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem IsFilledCoordinateFamily.coordinateWedges_eq_zero
    {I : Type*} {n : ℕ} {D : I → Set (ℝ × ℝ)} {Ω : Set (ℝ × ℝ)}
    {v F : Fin n → (ℝ × ℝ) → ℝ} (hF : IsFilledCoordinateFamily D Ω v F)
    {i : I} {z : ℝ × ℝ} (hz : z ∈ D i) :
    coordinateWedges (natCoordinateFamily F) n z = 0 := by
  unfold coordinateWedges covectorWedges
  apply sum_eq_zero
  intro j hj
  have hjn := mem_range.mp hj
  apply sum_eq_zero
  intro k hk
  have hkj := mem_range.mp hk
  have hkn := hkj.trans hjn
  have hne : (⟨k, hkn⟩ : Fin n) ≠ ⟨j, hjn⟩ :=
    fun heq => (Nat.ne_of_lt hkj) (congrArg Fin.val heq)
  have hw := hF.2.2.2 i ⟨k, hkn⟩ ⟨j, hjn⟩ hne z hz
  simpa only [natCoordinateFamily, dite_eq_left hkn, dite_eq_left hjn,
    planarWedge, mul_comm, abs_eq_zero] using hw

/-- The added rank-one pieces have no cost. Only the raw coordinates on
`G \ K` enter the estimate. -/
theorem IsFilledCoordinateFamily.integral_wedges_le_original
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily D Ω v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hG : MeasurableSet G) (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * coordinateWedges (natCoordinateFamily v) n z) (G \ K)) :
    (∫ z in Q \ K, 2 * coordinateWedges (natCoordinateFamily F) n z) ≤
      ∫ z in G \ K, 2 * coordinateWedges (natCoordinateFamily v) n z := by
  let S := (Q \ K) ∩ G
  have hSt : S ⊆ Q \ K := inter_subset_left
  have hSG : S ⊆ G \ K := fun z hz => ⟨hz.2, hz.1.2⟩
  have hS : MeasurableSet S := (hQ.isClosed.measurableSet.diff hK.measurableSet).inter hG
  have hFi : IntegrableOn (fun z => 2 * coordinateWedges (natCoordinateFamily F) n z) (Q \ K) :=
    (((continuousOn_coordinateWedges hΩ _ (contDiffOn_natCoordinateFamily hF.1) n).const_mul 2).mono hQΩ
      |>.integrableOn_compact hQ).mono_set sdiff_subset
  have heq : (∫ z in Q \ K, 2 * coordinateWedges (natCoordinateFamily F) n z) =
      ∫ z in S, 2 * coordinateWedges (natCoordinateFamily F) n z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hQ.isClosed.measurableSet.diff hK.measurableSet) hSt
    intro z hz
    have hzG : z ∉ G := fun hzG => hz.2 ⟨hz.1, hzG⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ((hcover hz.1.1).resolve_left hzG)
    rw [hF.coordinateWedges_eq_zero hi, mul_zero]
  calc
    _ = ∫ z in S, 2 * coordinateWedges (natCoordinateFamily F) n z := heq
    _ ≤ ∫ z in S, 2 * coordinateWedges (natCoordinateFamily v) n z :=
      setIntegral_mono_on (hFi.mono_set hSt) (hv.mono_set hSG) hS
        (fun z _ => mul_le_mul_of_nonneg_left (hF.coordinateWedges_le hD z) (by norm_num))
    _ ≤ _ := setIntegral_mono_set hv
      (Eventually.of_forall fun z => mul_nonneg (by norm_num) (coordinateWedges_nonneg _ _ z))
      (Eventually.of_forall hSG)

/-- The original-domain cost produces a metric retaining the spherical
background near the closed core and near infinity. -/
theorem IsFilledCoordinateFamily.exists_spherical_metric_of_original_cost
    {I : Type*} [Fintype I] {n : ℕ} {D : I → Set (ℝ × ℝ)}
    {Ω Q K G : Set (ℝ × ℝ)} {v F : Fin n → (ℝ × ℝ) → ℝ}
    (hF : IsFilledCoordinateFamily D Ω v F) (hD : ∀ i, IsOpen (D i))
    (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hG : MeasurableSet G) (hcover : Q ⊆ G ∪ ⋃ i, D i)
    (hv : IntegrableOn (fun z => 2 * coordinateWedges (natCoordinateFamily v) n z) (G \ K))
    {ε : ℝ} (hε : (∫ z in G \ K, 2 * coordinateWedges (natCoordinateFamily v) n z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∫ z in Q \ K, matrixEnergy (coordinateGram (natCoordinateFamily F) n z) (g z)) < ε := by
  exact exists_supported_spherical_metric_for_coordinates _ n hΩ hQ hQΩ
    (contDiffOn_natCoordinateFamily hF.1) hK
    ((hF.integral_wedges_le_original hD hΩ hQ hQΩ hK hG hcover hv).trans_lt hε)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
