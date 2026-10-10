import Mathlib
import OAI.Analysis.HardSphere.Geometry.SubsetPointLinear

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma sector_active_capacity {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0≤l) {ι : Type*} [Fintype ι]
    (b : ι → Point) (σ : Fin n → ι)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ((activeLabels σ).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (particleGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  classical
  cases n with
  | zero => simp [activeLabels]
  | succ n =>
    let μ := Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))
    let M := ∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂μ
    let G := fun i ↦ ∫⁻ X, ENNReal.ofReal (particleGradSq F i X) ∂μ
    let C := ENNReal.ofReal (Real.sqrt 3*l^3/r)
    have hi (i : Fin (n+1)) (hi : i∈activeLabels σ) : M≤C*G i := by
      obtain ⟨j,hji,hs⟩ := (mem_activeLabels σ i).mp hi
      obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
      exact sector_coordinate_capacity hF hr hl (fun a ↦ b (σ a)) i k (congrArg b hs) hz
    calc
      _ = ∑ _ ∈ activeLabels σ, M := by simp only [Finset.sum_const,nsmul_eq_mul]; rfl
      _ ≤ ∑ i ∈ activeLabels σ, C*G i := Finset.sum_le_sum hi
      _ = C*∑ i ∈ activeLabels σ, G i := (Finset.mul_sum _ _ _).symm
      _ ≤ C*∑ i, G i := by gcongr; exact Finset.subset_univ _
      _ = _ := rfl

lemma activeLabels_reindex_card {I J C : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (σ : I → C) : (activeLabels (σ ∘ e.symm)).card=(activeLabels σ).card := by
  classical
  have he : (activeLabels (σ ∘ e.symm)).map e.symm.toEmbedding=activeLabels σ := by
    ext i
    simp only [Finset.mem_map,Equiv.toEmbedding_apply,mem_activeLabels,Function.comp_apply]
    constructor
    · rintro ⟨j,⟨k,hkj,hσ⟩,rfl⟩
      exact ⟨e.symm k,fun h ↦ hkj (e.symm.injective h),hσ⟩
    · rintro ⟨k,hki,hσ⟩
      refine ⟨e i,⟨e k,fun h ↦ hki (e.injective h),?_⟩,e.symm_apply_apply i⟩
      simpa only [Equiv.symm_apply_apply] using hσ
  rw [←he,Finset.card_map]

lemma finite_sector_active_capacity {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F)
    {r l : ℝ} (hr : 0<r) (hl : 0≤l) (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ((activeLabels σ).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i, (∫⁻ X, ENNReal.ofReal (indexGradSq F i X)
          ∂Measure.pi (fun a ↦ volume.restrict (cube (b (σ a)) l))) := by
  let e := Fintype.equivFin I
  let T := reindexPoint e
  have h := sector_active_capacity (hF.comp T.contDiff) hr hl b (σ ∘ e.symm) (F := F ∘ T) (by
    intro X a c hac hd
    apply hz (T X) (e.symm a) (e.symm c) (fun h ↦ hac (e.symm.injective h))
    simpa only [T,reindexPoint_apply,Equiv.apply_symm_apply] using hd)
  rw [activeLabels_reindex_card] at h
  let μ := fun i ↦ volume.restrict (cube (b (σ i)) l)
  have hp := reindexPoint_preserving e μ
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn : (∫⁻ X,ENNReal.ofReal (‖(F ∘ T) X‖^2) ∂Measure.pi (fun j ↦ μ (e.symm j)))=
      ∫⁻ X,ENNReal.ofReal (‖F X‖^2) ∂Measure.pi μ := hp.lintegral_comp hm
  change _ * (∫⁻ X,ENNReal.ofReal (‖(F ∘ T) X‖^2) ∂Measure.pi (fun j ↦ μ (e.symm j))) ≤ _ at h
  rw [hn] at h
  apply h.trans_eq
  congr 1
  calc
    _ = ∑ j,∫⁻ X,ENNReal.ofReal (indexGradSq F (e.symm j) X) ∂Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro j _
      change (∫⁻ X,ENNReal.ofReal (indexGradSq (F ∘ T) j X) ∂Measure.pi (fun j ↦ μ (e.symm j)))=_
      dsimp only [T]
      simp_rw [indexGradSq_reindex hF]
      exact hp.lintegral_comp (continuous_indexGradSq hF _).measurable.ennreal_ofReal
    _ = _ := Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

lemma selected_sector_active_capacity {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (I → Point) → E} (hF : ContDiff ℝ 1 F) (p : I → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0<r) (hl : 0≤l) (b : C → Point) (σ : I → C)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2) ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
        ∑ i : {i // p i}, (∫⁻ X, ENNReal.ofReal (indexGradSq F i.val X)
          ∂Measure.pi (fun i ↦ volume.restrict (cube (b (σ i)) l))) := by
  let μ := fun i ↦ (volume : Measure Point).restrict (cube (b (σ i)) l)
  have hslice (Y : {i // ¬p i} → Point) := finite_sector_active_capacity
    (hF.comp (contDiff_subsetPointFill p Y)) hr hl b (fun i : {i // p i} ↦ σ i.val)
    (F := F ∘ subsetPointFill p Y) (by
      intro X a c hac hd
      apply hz (subsetPointFill p Y X) a.val c.val (fun h ↦ hac (Subtype.ext h))
      simpa only [subsetPointFill,dite_eq_left a.property,dite_eq_left c.property] using hd)
  have hm : Measurable (fun X ↦ ENNReal.ofReal (‖F X‖^2)) := by
    simpa only [Pi.pow_apply] using (hF.continuous.norm.pow 2).measurable.ennreal_ofReal
  have hn := lintegral_subsetPointFill μ p (fun X ↦ ENNReal.ofReal (‖F X‖^2)) hm
  rw [hn,← lintegral_const_mul' _ _ (by simp)]
  have hi := lintegral_mono hslice (μ := Measure.pi (fun i : {i // ¬p i} ↦ μ i.val))
  simp only [Function.comp_apply,indexGradSq_subset hF] at hi
  apply hi.trans_eq
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (lintegral_subsetPointFill μ p _
      (continuous_indexGradSq hF i.val).measurable.ennreal_ofReal).symm
  · intro i _
    have he := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I ↦ Point) p).symm.measurable
    exact (((continuous_indexGradSq hF i.val).measurable.ennreal_ofReal.comp he).lintegral_prod_left')

lemma selected_subdivided_active_capacity {n j : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin n → Point) → E} (hF : ContDiff ℝ 1 F) (p : Fin n → Prop) [DecidablePred p]
    {r l : ℝ} (hr : 0<r) (hl : 0≤l) (b : Point)
    (hz : ∀X a c, a≠c → sqRadius (X a-X c)≤r^2 → F X=0) :
    (∑ σ : Fin n → (Fin j × Fin j × Fin j),
      ((activeLabels (fun i : {i // p i} ↦ σ i.val)).card : ℝ≥0∞)*
      (∫⁻ X, ENNReal.ofReal (‖F X‖^2)
        ∂Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b l (σ i)) l)))) ≤
      ENNReal.ofReal (Real.sqrt 3*l^3/r)*
      ∑ i : {i // p i}, ∫⁻ X,ENNReal.ofReal (particleGradSq F i.val X)
        ∂Measure.pi (fun _ ↦ volume.restrict (cube b ((j:ℝ)*l))) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n → (Fin j × Fin j × Fin j))))
    (fun σ _ ↦ selected_sector_active_capacity hF p hr hl (subcubeBase b l) σ hz)
  apply h.trans_eq
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [cube_configuration_subdivision b hl,Measure.sum_fintype,MeasureTheory.lintegral_finsetSum_measure]
  rfl

end HardSphere.SphericalCoordinates

open Set Function MeasureTheory
open scoped ENNReal

end

end OAI
