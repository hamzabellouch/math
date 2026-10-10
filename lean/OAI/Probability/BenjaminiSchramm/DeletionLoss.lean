import OAI.Probability.BenjaminiSchramm.DeletionBound

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem connection_measure_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} = law p {ω | Conn G ω y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G ω,conn_symm G ω⟩

noncomputable def openTriangle (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' z, law p {ω | Conn G ω x a} * law p {ω | Conn G ω a z} *
    law p {ω | Conn G ω z y}

theorem lintegral_clusterMass_conn [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x z : V) :
    (∫⁻ ω, (if Conn G ω x z then clusterMass G ω x else 0) ∂law p) =
      ∑' u, law p {ω | Conn G ω x u ∧ Conn G ω x z} := by
  have he (ω : Set E) : (if Conn G ω x z then clusterMass G ω x else 0) =
      ∑' u, if Conn G ω x u ∧ Conn G ω x z then (1 : ℝ≥0∞) else 0 := by
    by_cases hz : Conn G ω x z
    · simp only [hz,ite_true,and_true,clusterMass]
    · simp only [hz,ite_false,and_false,tsum_zero]
  have hm (u : V) : Measurable (fun ω : Set E =>
      if Conn G ω x u ∧ Conn G ω x z then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite ((measurableSet_conn G x u).inter (measurableSet_conn G x z))
      measurable_const measurable_const
  simp_rw [he]
  rw [lintegral_tsum (fun u => (hm u).aemeasurable)]
  apply tsum_congr
  intro u
  have hs : MeasurableSet {ω : Set E | Conn G ω x u ∧ Conn G ω x z} :=
    (measurableSet_conn G x u).inter (measurableSet_conn G x z)
  simpa only [Set.indicator,Pi.one_apply,Set.mem_ofPred_eq] using
    lintegral_indicator_one (μ := law p) hs

theorem three_arm_first_moment_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ a, (∑' u, law p {ω | Conn G ω a u}) ≤ C) (x z : V) :
    (∑' u, law p {ω | Conn G ω x u ∧ Conn G ω x z}) ≤
      C * ∑' a, law p {ω | Conn G ω x a} * law p {ω | Conn G ω a z} := by
  calc
    _ ≤ ∑' u, ∑' a, law p {ω | Conn G ω x a} * law p {ω | Conn G ω a u} *
        law p {ω | Conn G ω a z} := ENNReal.tsum_le_tsum (fun u => three_arm_bound G p x u z)
    _ = ∑' a, law p {ω | Conn G ω x a} * (∑' u, law p {ω | Conn G ω a u}) *
        law p {ω | Conn G ω a z} := by
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ ∑' a, law p {ω | Conn G ω x a} * C * law p {ω | Conn G ω a z} :=
      ENNReal.tsum_le_tsum (fun a => mul_le_mul' (mul_le_mul' le_rfl (hC a)) le_rfl)
    _ = _ := by
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro a
      ring

noncomputable def clusterDeletionLoss (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ≥0∞ :=
  clusterMass G ω x * ∑' z, if Conn G ω x z then law p {η | Conn G η y z} else 0

theorem measurable_clusterDeletionLoss [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Measurable (clusterDeletionLoss G p x y) :=
  (measurable_clusterMass G x).mul (Measurable.tsum (fun z =>
    Measurable.ite (measurableSet_conn G x z) measurable_const measurable_const))

theorem lintegral_clusterDeletionLoss [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (∫⁻ ω, clusterDeletionLoss G p x y ω ∂law p) =
      ∑' z, law p {ω | Conn G ω y z} *
        ∑' u, law p {ω | Conn G ω x u ∧ Conn G ω x z} := by
  have hm (z : V) : Measurable (fun ω : Set E =>
      if Conn G ω x z then clusterMass G ω x else 0) :=
    Measurable.ite (measurableSet_conn G x z) (measurable_clusterMass G x) measurable_const
  have he (ω : Set E) : clusterDeletionLoss G p x y ω =
      ∑' z, law p {η | Conn G η y z} * (if Conn G ω x z then clusterMass G ω x else 0) := by
    dsimp only [clusterDeletionLoss]
    rw [←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro z
    split_ifs <;> ring
  have hm' (z : V) : Measurable (fun ω : Set E =>
      law p {η | Conn G η y z} * (if Conn G ω x z then clusterMass G ω x else 0)) :=
    measurable_const.mul (hm z)
  simp_rw [he]
  rw [lintegral_tsum (fun z => (hm' z).aemeasurable)]
  apply tsum_congr
  intro z
  rw [lintegral_const_mul _ (hm z),lintegral_clusterMass_conn]

theorem clusterDeletionLoss_openTriangle_bound [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ a, (∑' u, law p {ω | Conn G ω a u}) ≤ C) (x y : V) :
    (∫⁻ ω, clusterDeletionLoss G p x y ω ∂law p) ≤ C * openTriangle G p x y := by
  rw [lintegral_clusterDeletionLoss]
  calc
    _ ≤ ∑' z, law p {ω | Conn G ω y z} *
        (C * ∑' a, law p {ω | Conn G ω x a} * law p {ω | Conn G ω a z}) :=
      ENNReal.tsum_le_tsum (fun z =>
        mul_le_mul' le_rfl (three_arm_first_moment_bound G p C hC x z))
    _ = ∑' z, ∑' a, C * (law p {ω | Conn G ω x a} * law p {ω | Conn G ω a z} *
        law p {ω | Conn G ω z y}) := by
      apply tsum_congr
      intro z
      rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left,connection_measure_symm G p y z]
      apply tsum_congr
      intro a
      ring
    _ = _ := by
      rw [ENNReal.tsum_comm]
      simp_rw [ENNReal.tsum_mul_left]
      rfl

end Percolation.BenjaminiSchramm

end OAI
