import OAI.Geometry.CylinderCovering.Radial.PairedActualDefinitions
import OAI.Geometry.CylinderCovering.Radial.PairedSweep
import OAI.Geometry.CylinderCovering.Radial.ActualEndpoint

namespace OAI

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section
namespace CylinderCovering.RadialPairedSweep

variable (h ε : ℝ) (hh : 0 < h) (R : ℝ → ℝ)
  (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
  (hR0 : ∀ q ∈ Icc (-1 : ℝ) 1, 0 ≤ R q)

lemma upperData_localSweep (N : ℕ) (i : Fin N) :
    RadialSweep.localSweep (upperData h ε hh R hR hR0) N i =
      upperLocalSweep h ε R N i := by
  ext z
  constructor
  · rintro ⟨q,hq,ρ,hρ,s,hs,hz⟩
    refine ⟨q,hq,ρ,hρ,s,hs,?_⟩
    rw [hz]
    ext j
    fin_cases j <;> simp [upperData,upperW_eq,point] <;> ring
  · rintro ⟨q,hq,ρ,hρ,s,hs,hz⟩
    refine ⟨q,hq,ρ,hρ,s,hs,?_⟩
    rw [hz]
    ext j
    fin_cases j <;> simp [upperData,upperW_eq,point] <;> ring

lemma lowerData_localSweep (N : ℕ) (i : Fin N) :
    RadialSweep.localSweep (lowerData h ε hh R hR hR0) N i =
      lowerLocalSweep h ε R N i := by
  ext z
  constructor
  · rintro ⟨q,hq,ρ,hρ,s,hs,hz⟩
    refine ⟨q,hq,ρ,hρ,s,hs,?_⟩
    rw [hz]
    ext j
    fin_cases j <;> simp [lowerData,lowerW_eq,point] <;> ring
  · rintro ⟨q,hq,ρ,hρ,s,hs,hz⟩
    refine ⟨q,hq,ρ,hρ,s,hs,?_⟩
    rw [hz]
    ext j
    fin_cases j <;> simp [lowerData,lowerW_eq,point] <;> ring

lemma upperData_actualBase (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.actualBase (upperData h ε hh R hR hR0) N tag i =
      upperActualBase h ε R N tag i := by
  unfold RadialSweep.actualBase upperActualBase
  rw [upperData_direction,upperData_localSweep]

lemma lowerData_actualBase (N : ℕ) (tag : Fin N → ℝ) (i : Fin N) :
    RadialSweep.actualBase (lowerData h ε hh R hR hR0) N tag i =
      lowerActualBase h ε R N tag i := by
  unfold RadialSweep.actualBase lowerActualBase
  rw [lowerData_direction,lowerData_localSweep]

lemma pairedActualCost_eq (N : ℕ) (tagU tagL : Fin N → ℝ) :
    pairedActualCost h ε R N tagU tagL =
      RadialSweep.actualCost (upperData h ε hh R hR hR0) N tagU +
      RadialSweep.actualCost (lowerData h ε hh R hR hR0) N tagL := by
  simp only [pairedActualCost,RadialSweep.actualCost,
    upperData_actualBase,lowerData_actualBase]

lemma upperLocalSweep_subset_frozenCylinder {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-1) 1 N tag) (i : Fin N) :
    upperLocalSweep h ε R N i ⊆
      (RadialSweep.frozenCylinder (upperData h ε hh R hR hR0) N tag htag i).carrier := by
  rw [← upperData_localSweep h ε hh R hR hR0]
  exact fun _ hz => RadialSweep.localSweep_mem_frozenCylinder _ tag htag i hz

lemma lowerLocalSweep_subset_frozenCylinder {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-1) 1 N tag) (i : Fin N) :
    lowerLocalSweep h ε R N i ⊆
      (RadialSweep.frozenCylinder (lowerData h ε hh R hR hR0) N tag htag i).carrier := by
  rw [← lowerData_localSweep h ε hh R hR hR0]
  exact fun _ hz => RadialSweep.localSweep_mem_frozenCylinder _ tag htag i hz

lemma upperActualBase_subset_frozenBase {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-1) 1 N tag) (i : Fin N) :
    upperActualBase h ε R N tag i ⊆
      RadialSweep.frozenBase (upperData h ε hh R hR hR0) N tag i := by
  rw [← upperData_actualBase h ε hh R hR hR0]
  exact RadialSweep.actualBase_subset_frozenBase _ tag htag i

lemma lowerActualBase_subset_frozenBase {N : ℕ} (tag : Fin N → ℝ)
    (htag : RadialRiemann.IsTagged (-1) 1 N tag) (i : Fin N) :
    lowerActualBase h ε R N tag i ⊆
      RadialSweep.frozenBase (lowerData h ε hh R hR hR0) N tag i := by
  rw [← lowerData_actualBase h ε hh R hR hR0]
  exact RadialSweep.actualBase_subset_frozenBase _ tag htag i

lemma pairedActualCost_nonneg (N : ℕ) (tagU tagL : Fin N → ℝ) :
    0 ≤ pairedActualCost h ε R N tagU tagL := by
  unfold pairedActualCost TriangularCovering.area
  exact add_nonneg (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)

theorem paired_actual_sweeps : ActualPairedStatement := by
  intro h ε hh R hR hR0 tagU tagL htagU htagL
  obtain ⟨hU,hUb,_hUlim⟩ := RadialSweep.actual_radial_sweep
    (upperData h ε hh R hR hR0) tagU htagU
  obtain ⟨hL,hLb,_hLlim⟩ := RadialSweep.actual_radial_sweep
    (lowerData h ε hh R hR hR0) tagL htagL
  have hbound : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      pairedActualCost h ε R N (tagU N) (tagL N) ≤
        2*h*physicalCost h ε R + δ := by
    intro δ hδ
    filter_upwards [hUb (δ/2) (by linarith),hLb (δ/2) (by linarith)] with N hUN hLN
    rw [pairedActualCost_eq h ε hh R hR hR0]
    rw [upperData_weightedArea] at hUN
    rw [lowerData_weightedArea] at hLN
    linarith
  refine ⟨?_,hbound,?_⟩
  · intro N hN
    refine ⟨?_,?_,?_⟩
    · intro i
      have hUi := (hU N hN).1 i
      have hLi := (hL N hN).1 i
      simp only [upperData_direction,upperData_actualBase] at hUi
      simp only [lowerData_direction,lowerData_actualBase] at hLi
      exact ⟨⟨hUi.1,hUi.2.1,hUi.2.2.1,hUi.2.2.2.1,hUi.2.2.2.2.1⟩,
        ⟨hLi.1,hLi.2.1,hLi.2.2.1,hLi.2.2.2.1,hLi.2.2.2.2.1⟩⟩
    · simpa only [upperData_sweep,upperData_direction,upperData_actualBase] using (hU N hN).2
    · simpa only [lowerData_sweep,lowerData_direction,lowerData_actualBase] using (hL N hN).2
  · apply le_of_forall_pos_le_add
    intro δ hδ
    exact _root_.OAI.RadialActualSweep.limsup_le_of_nonneg_of_le_tendsto
      (fun N => pairedActualCost_nonneg h ε R N (tagU N) (tagL N))
      (hbound δ hδ) tendsto_const_nhds

end CylinderCovering.RadialPairedSweep

end

end OAI
