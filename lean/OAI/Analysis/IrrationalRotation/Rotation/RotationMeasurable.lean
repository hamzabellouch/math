import OAI.Analysis.IrrationalRotation.Model.RotationMeasurable
import OAI.Analysis.IrrationalRotation.Rotation.RotationAlgebra
import OAI.Analysis.IrrationalRotation.Analysis.BoundedLusinApproximation
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonalConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem vonNeumannAlgebra_mem_of_strong_tendsto
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) {l : Filter ι} [l.NeBot]
    {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H}
    (hA : ∀ i, A i ∈ M) (hAB : ∀ v, Tendsto (fun i => A i v) l (𝓝 (B v))) :
    B ∈ M := by
  rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro T hT
  apply ContinuousLinearMap.ext
  intro v
  have ht := T.continuous.continuousAt.tendsto.comp (hAB v)
  have ha := hAB (T v)
  have heq : (fun i => T (A i v)) = (fun i => A i (T v)) := by
    funext i
    exact (DFunLike.congr_fun ((VonNeumannAlgebra.mem_commutant_iff.mp hT) (A i) (hA i)) v).symm
  change T (B v) = B (T v)
  change Tendsto (fun i => T (A i v)) l (𝓝 (T (B v))) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht ha

namespace Rotation

theorem measurableRepresentation_coordinates_ae
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (v : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      measurableRepresentation θ g C hC hg hb v x k = g (action θ k x) * v x k :=
  WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ v

theorem measurableRepresentation_norm_le
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    ‖measurableRepresentation θ g C hC hg hb‖ ≤ C :=
  WeightedShift.norm_fieldDiagonal_le _ _ _ _ _

theorem measurableRepresentation_continuous
    (θ : ℝ) (a : C(Circle, ℂ)) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x, ‖a x‖ ≤ C) :
    measurableRepresentation θ a C hC a.continuous.measurable hb = representation θ a := by
  apply WeightedShift.fieldDiagonal_congr
  exact Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

theorem measurableRepresentation_congr_ae
    (θ : ℝ) {g h : Circle → ℂ} {C D : ℝ} {hC : 0 ≤ C} {hD : 0 ≤ D}
    {hg : Measurable g} {hh : Measurable h}
    {hgb : ∀ x, ‖g x‖ ≤ C} {hhb : ∀ x, ‖h x‖ ≤ D}
    (heq : g =ᵐ[circleMeasure] h) :
    measurableRepresentation θ g C hC hg hgb = measurableRepresentation θ h D hD hh hhb := by
  apply WeightedShift.fieldDiagonal_congr
  have hall : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, g (action θ k x) = h (action θ k x) := by
    rw [ae_all_iff]
    intro k
    exact (action_measurePreserving θ k).quasiMeasurePreserving.ae (p := fun x => g x = h x) heq
  filter_upwards [hall] with x hx
  exact lp.ext (funext hx)

theorem measurableRepresentation_tendsto_apply
    (θ : ℝ) (g : ℕ → Circle → ℂ) (h : Circle → ℂ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ n, Measurable (g n)) (hh : Measurable h)
    (hgb : ∀ n x, ‖g n x‖ ≤ C) (hhb : ∀ x, ‖h x‖ ≤ D)
    (hgh : ∀ᵐ x ∂circleMeasure, Tendsto (fun n => g n x) atTop (𝓝 (h x)))
    (v : Hilbert) :
    Tendsto (fun n => measurableRepresentation θ (g n) C hC (hg n) (hgb n) v)
      atTop (𝓝 (measurableRepresentation θ h D hD hh hhb v)) := by
  apply WeightedShift.fieldDiagonal_tendsto_apply
  have hall : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      Tendsto (fun n => g n (action θ k x)) atTop (𝓝 (h (action θ k x))) := by
    rw [ae_all_iff]
    intro k
    exact (action_measurePreserving θ k).quasiMeasurePreserving.ae
      (p := fun x => Tendsto (fun n => g n x) atTop (𝓝 (h x))) hgh
  exact hall

theorem measurableRepresentation_mem_algebra
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    measurableRepresentation θ g C hC hg hb ∈ algebra θ := by
  obtain ⟨a, ha, hae⟩ := Lusin.exists_bounded_continuous_eventuallyEq circleMeasure hg hC hb
  have hconv : ∀ᵐ x ∂circleMeasure, Tendsto (fun n => a n x) atTop (𝓝 (g x)) := by
    filter_upwards [hae] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun _ hn => hn.symm)
  apply vonNeumannAlgebra_mem_of_strong_tendsto (algebra θ) (l := (atTop : Filter ℕ))
    (A := fun n => measurableRepresentation θ (a n) (2 * C) (by positivity)
      (a n).continuous.measurable (ha n))
  · intro n
    rw [measurableRepresentation_continuous]
    exact representation_mem_algebra θ (a n)
  · intro v
    exact measurableRepresentation_tendsto_apply θ (fun n => a n) g (2 * C) C
      (by positivity) hC (fun n => (a n).continuous.measurable) hg ha hb hconv v

theorem exists_bounded_borel_representative
    {g : Circle → ℂ} (hg : AEStronglyMeasurable g circleMeasure)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂circleMeasure, ‖g x‖ ≤ C) :
    ∃ h : Circle → ℂ, Measurable h ∧ (∀ x, ‖h x‖ ≤ C) ∧ g =ᵐ[circleMeasure] h := by
  let f : Circle → ℂ := hg.mk g
  have hfm : Measurable f := hg.stronglyMeasurable_mk.measurable
  let h : Circle → ℂ := fun x => if ‖f x‖ ≤ C then f x else 0
  have hhm : Measurable h := hfm.piecewise (measurableSet_le hfm.norm measurable_const) measurable_const
  refine ⟨h, hhm, ?_, ?_⟩
  · intro x
    dsimp [h]
    split_ifs with hx
    · exact hx
    · simpa using hC
  · filter_upwards [hg.ae_eq_mk, hb] with x hx hbx
    change g x = if ‖f x‖ ≤ C then f x else 0
    change g x = f x at hx
    rw [← hx, ite_eq_left hbx]

theorem exists_mem_algebra_of_ae_bound
    (θ : ℝ) {g : Circle → ℂ} (hg : AEStronglyMeasurable g circleMeasure)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂circleMeasure, ‖g x‖ ≤ C) :
    ∃ A : Hilbert →L[ℂ] Hilbert, A ∈ algebra θ ∧ ‖A‖ ≤ C ∧
      ∀ v : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
        A v x k = g (action θ k x) * v x k := by
  obtain ⟨h, hhm, hhb, heq⟩ := exists_bounded_borel_representative hg hC hb
  refine ⟨measurableRepresentation θ h C hC hhm hhb,
    measurableRepresentation_mem_algebra θ h C hC hhm hhb,
    measurableRepresentation_norm_le θ h C hC hhm hhb, ?_⟩
  intro v
  have hall : ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, g (action θ k x) = h (action θ k x) := by
    rw [ae_all_iff]
    intro k
    exact (action_measurePreserving θ k).quasiMeasurePreserving.ae
      (p := fun x => g x = h x) heq
  filter_upwards [measurableRepresentation_coordinates_ae θ h C hC hhm hhb v, hall]
    with x hx he
  intro k
  rw [hx k, he k]

theorem exists_mem_algebra_of_memLp_top
    (θ : ℝ) {g : Circle → ℂ} (hg : MemLp g ∞ circleMeasure) :
    ∃ A : Hilbert →L[ℂ] Hilbert, A ∈ algebra θ ∧
      ‖A‖ ≤ lpNorm g ∞ circleMeasure ∧
      ∀ v : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
        A v x k = g (action θ k x) * v x k := by
  apply exists_mem_algebra_of_ae_bound θ hg.aestronglyMeasurable
  · exact lpNorm_nonneg
  · exact ae_le_lpNorm_exponent_top hg

theorem exists_unique_mem_algebra_of_memLp_top
    (θ : ℝ) {g : Circle → ℂ} (hg : MemLp g ∞ circleMeasure) :
    ∃! A : Hilbert →L[ℂ] Hilbert, A ∈ algebra θ ∧
      ‖A‖ ≤ lpNorm g ∞ circleMeasure ∧
      ∀ v : Hilbert, ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
        A v x k = g (action θ k x) * v x k := by
  obtain ⟨A, hA, hnorm, hcoord⟩ := exists_mem_algebra_of_memLp_top θ hg
  refine ⟨A, ⟨hA, hnorm, hcoord⟩, ?_⟩
  intro B hB
  apply operator_ext_of_coordinates
  intro v
  filter_upwards [hB.2.2 v, hcoord v] with x hx hy
  intro k
  exact (hx k).trans (hy k).symm

theorem U_mul_measurableRepresentation_coordinates_ae
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (v : Hilbert) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      (U * measurableRepresentation θ g C hC hg hb) v x k =
        g (action θ (k - 1) x) * v x (k - 1) := by
  filter_upwards [U_coordinates_ae (measurableRepresentation θ g C hC hg hb v),
    measurableRepresentation_coordinates_ae θ g C hC hg hb v] with x hU hg
  intro k
  exact (hU k).trans (hg (k - 1))

theorem U_mul_measurableRepresentation_mem_algebra
    (θ : ℝ) (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    U * measurableRepresentation θ g C hC hg hb ∈ algebra θ :=
  mul_mem (U_mem_algebra θ) (measurableRepresentation_mem_algebra θ g C hC hg hb)

end Rotation
end Invariant233

end

end OAI
