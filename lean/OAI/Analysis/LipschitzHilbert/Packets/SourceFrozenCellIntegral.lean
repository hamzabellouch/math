import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenLongInterval
import OAI.Analysis.LipschitzHilbert.Trees.SourceLongCellEnergy

namespace OAI

/-! Actual frozen long sums are measurable, have finite cell suprema,
and integrate against the original common angular-support mask. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

/-- A bounded measurable function on a finite cell integrates over its
mask with the exact mass of the intersection. -/
theorem masked_cell_norm_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (C A : Set X) (hC : MeasurableSet C) (hA : MeasurableSet A)
    (hfin : μ C≠∞) (f : X → E) (hf : AEStronglyMeasurable f μ)
    (M : ℝ) (hbound : ∀ z∈C, ‖f z‖≤M) :
    IntegrableOn (A.indicator f) C μ ∧
      (∫ z in C, ‖A.indicator f z‖ ∂μ)≤M*μ.real (C∩A) := by
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hfin
  have hpoint (z : X) (hz : z∈C) :
      ‖A.indicator f z‖≤A.indicator (fun _ => M) z := by
    by_cases ha : z∈A
    · simp only [indicator_of_mem ha]
      exact hbound z hz
    · simp only [indicator_of_notMem ha,norm_zero,le_refl]
  have hi : IntegrableOn (A.indicator f) C μ := by
    apply ((integrable_const M).indicator hA).mono' ((hf.indicator hA).restrict)
    filter_upwards [ae_restrict_mem hC] with z hz
    exact hpoint z hz
  refine ⟨hi,?_⟩
  have hle := integral_mono_ae hi.norm ((integrable_const M).indicator hA)
    (by filter_upwards [ae_restrict_mem hC] with z hz; exact hpoint z hz)
  apply hle.trans_eq
  rw [integral_indicator hA,integral_const]
  simp only [measureReal_def,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter,Measure.restrict_apply hA]
  rw [Set.inter_comm,mul_comm]

namespace SourceLabeledLattice
open SourceWhitney DyadicLineGrid
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable

theorem physicalLongInterval_uniform_bound (t : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    ∃ B : ℝ, 0≤B ∧ ∀ r lo hi z, ‖P.physicalLongIntervalSchwartz t r c lo hi z‖≤B := by
  let v : Fin (N+1) → ℝ := fun n =>
    SchwartzMap.seminorm ℝ 0 0 (P.physicalTreePartialSchwartz t c n)
  let S := ∑ n, v n
  have hv (n : Fin (N+1)) : 0≤v n := apply_nonneg _ _
  have hS : 0≤S := Finset.sum_nonneg (fun n _ => hv n)
  have hb (n : ℕ) (hn : n≤N) (z : ℝ×ℝ) : ‖P.physicalTreePartialSchwartz t c n z‖≤S := by
    have hn' : n<N+1 := by omega
    have hsingle := Finset.single_le_sum (f:=v) (fun n _ => hv n)
      (Finset.mem_univ (⟨n,hn'⟩ : Fin (N+1)))
    exact (SchwartzMap.norm_le_seminorm ℝ (P.physicalTreePartialSchwartz t c n) z).trans hsingle
  refine ⟨2*S,by positivity,?_⟩
  intro r lo hi z
  rw [physicalLongIntervalSchwartz,sub_apply]
  exact (norm_sub_le _ _).trans (by
    have hhi := hb (min hi (P.longPrefix r)) ((min_le_right _ _).trans (P.longPrefix_le r)) z
    have hlo := hb (min lo (P.longPrefix r)) ((min_le_right _ _).trans (P.longPrefix_le r)) z
    linarith)

def longCellSup (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (b : ℝ) (p : (ℤ×ℤ)×ℤ) : ℝ :=
  packetNormSup (fun a : ℕ×ℕ => P.physicalLongIntervalSchwartz 0 (DyadicLineGrid.scale p.1.1) c a.1 a.2)
    (coordinateBox (center p.1.1 p.1.2) (b+(p.2:ℝ)*P.width)
      (DyadicLineGrid.scale p.1.1/2) (P.width/2))

theorem longCellSup_nonneg
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (b : ℝ) (p : (ℤ×ℤ)×ℤ) :
    0≤P.longCellSup c b p := by
  obtain ⟨B,hB,hbound⟩ := P.physicalLongInterval_uniform_bound 0 c
  exact packetNormSup_nonneg _ _ B hB (fun a z _ => hbound _ a.1 a.2 z)

theorem frozenLongValue_measurable (t r w : ℝ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) :
    Measurable (fun z => P.frozenLongValue t r w (u z) c z) := by
  unfold frozenLongValue
  apply Finset.measurable_sum
  intro j _
  by_cases hj : 32*r<P.length j
  · simp only [hj,true_and]
    have hset : MeasurableSet {z | |u z-t|≤w/P.length j} :=
      measurableSet_le (show Measurable (fun z => |u z-t|) by fun_prop) measurable_const
    have hc := (planarSynthesisSchwartz
      (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
      (fun a k => P.physicalPacket t j a.1 a.2 k)).continuous.measurable
    have hc' : Measurable (fun z => planarFixedSynthesis
        (fun a : Σ l : P.labels j, Item j l => c j a.1 a.2)
        (fun a k => P.physicalPacket t j a.1 a.2 k) z) := by
      convert hc using 1
      funext z
      exact (planarSynthesisSchwartz_apply _ _ z).symm
    exact Measurable.ite hset hc' measurable_const
  · simp only [hj,false_and,ite_false]
    exact measurable_const

/-- Pointwise interval extraction controls the actual variable frozen
selector on every half-open cell. -/
theorem frozenLongValue_le_cell_sup (w : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (b : ℝ) (p : (ℤ×ℤ)×ℤ) {z : ℝ×ℝ}
    (hz : z∈partitionCell b P.width p) :
    ‖P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z‖≤P.longCellSup c b p := by
  obtain ⟨B,hB,hbound⟩ := P.physicalLongInterval_uniform_bound 0 c
  apply le_csSup (packetNormValues_bddAbove _ _ B hB (fun a x _ => hbound _ a.1 a.2 x))
  refine Or.inr ⟨(P.angularStart w |u z-0|,N),z,partitionCell_subset_box b P.width p hz,?_⟩
  rw [P.frozenLongValue_eq_interval 0 _ w (u z) hw c z]

theorem frozen_cell_integral (w : ℝ) (hw : 0≤w)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (b : ℝ) (p : (ℤ×ℤ)×ℤ)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A) :
    IntegrableOn (A.indicator (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z))
      (partitionCell b P.width p) (volume.prod volume) ∧
    (∫ z in partitionCell b P.width p,
      ‖A.indicator (fun z => P.frozenLongValue 0 (DyadicLineGrid.scale p.1.1) w (u z) c z) z‖
        ∂volume.prod volume)≤
      P.longCellSup c b p*(volume.prod volume).real (partitionCell b P.width p∩A) :=
  masked_cell_norm_integral (volume.prod volume) _ A (partitionCell_measurable b P.width p)
    hA (partitionCell_finite b P.width p) _ (P.frozenLongValue_measurable 0 _ w c u hu).aestronglyMeasurable
    (P.longCellSup c b p)
    (fun _ hz => P.frozenLongValue_le_cell_sup w hw c u b p hz)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
