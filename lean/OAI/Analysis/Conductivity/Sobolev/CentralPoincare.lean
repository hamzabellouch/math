import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralAnchor

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma centralTop_subset_anchor (i : Fin 4) : centralTop i ⊆ centralAnchor := by
  have h : centralTop i=centralAnchorPiece i.val := by fin_cases i <;> rfl
  rw [h]
  exact (subset_patchCluster centralAnchorPiece i.val).trans (patchCluster_mono _ (by omega))

lemma centralBottom_subset_anchor (i : Fin 4) : centralBottom i ⊆ centralAnchor := by
  have h : centralBottom i=centralAnchorPiece (i.val+5) := by fin_cases i <;> rfl
  rw [h]
  exact (subset_patchCluster centralAnchorPiece (i.val+5)).trans (patchCluster_mono _ (by omega))

lemma centralColumn_overlaps_anchor (i : Fin 4) (j k : Fin 5)
    (hx : (centralColumn i j k).xl < (centralColumn i j k).xu)
    (hy : (centralColumn i j k).yl < (centralColumn i j k).yu) :
    0 < volume.real (centralAnchor ∩ (centralColumn i j k).prism (-centralHeight) centralHeight) := by
  have hh : centralChildHeight < centralHeight := by
    norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
  apply ((centralColumn i j k).prism_real_pos _ _ hx hy hh).trans_le
  refine measureReal_mono ?_ ?_
  · rintro z ⟨hz,ht⟩
    refine ⟨centralTop_subset_anchor i ⟨?_,ht⟩,hz,?_,ht.2⟩
    · have hh := hz
      simp only [centralColumn,RectFootprint.inter_carrier,mem_inter_iff] at hh
      exact hh.1.1
    · have hp : 0 ≤ centralChildHeight+centralHeight := by
        norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
      linarith [ht.1]
  · exact ((centralCluster_compact 8).inter ((centralColumn i j k).prism_compact _ _)).measure_ne_top

def centralColumnConstant (i : Fin 4) (j k : Fin 5) : ℝ :=
  let B := (centralColumn i j k).poincareConstant (-centralHeight) centralHeight
  let R := (centralColumn i j k).prism (-centralHeight) centralHeight
  centralAnchorConstant+2*B+4*volume.real R/(volume.real (centralAnchor∩R))*(centralAnchorConstant+B)

lemma centralColumnConstant_nonneg (i : Fin 4) (j k : Fin 5) : 0 ≤ centralColumnConstant i j k := by
  have hA := centralAnchorConstant_nonneg
  have hB := (centralColumn i j k).poincareConstant_nonneg (-centralHeight) centralHeight
  dsimp [centralColumnConstant]
  positivity

lemma centralColumn_poincare (i : Fin 4) (j k : Fin 5) {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume ((centralColumn i j k).prism (-centralHeight) centralHeight) f
      (centralAnchorAverage 0 f) ≤ centralColumnConstant i j k*(∫ z in centralClosed,cubeEnergyDensity f z) := by
  let R := (centralColumn i j k).prism (-centralHeight) centralHeight
  have hc : IsCompact R := (centralColumn i j k).prism_compact _ _
  have hint : ∀ c : ℝ, IntegrableOn (fun z => (f z-c)^2) R := fun c =>
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact hc
  by_cases h : (centralColumn i j k).xl<(centralColumn i j k).xu ∧
      (centralColumn i j k).yl<(centralColumn i j k).yu
  · have hiA : IntegrableOn (fun z => (f z-centralAnchorAverage 0 f)^2) centralAnchor :=
      ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact (centralCluster_compact 8)
    have hglue := overlap_poincare_glue volume (integral_nonneg (cubeEnergyDensity_nonneg f))
      centralAnchorConstant_nonneg ((centralColumn i j k).poincareConstant_nonneg (-centralHeight) centralHeight)
      (centralCluster_compact 8).measure_ne_top hc.measure_ne_top (centralColumn_overlaps_anchor i j k h.1 h.2)
      hiA (hint _) (hint _) (centralAnchor_poincare hf)
      ((centralColumn i j k).poincare_in _ _ centralClosed_compact (centralColumn_subset i j k) hf)
    exact (localVariance_mono volume (hiA.union (hint _)) (subset_union_right : R⊆centralAnchor∪R)).trans hglue
  · have hz : volume R=0 := by
      apply nonpos_iff_eq_zero.mp
      apply le_of_not_gt
      intro hp
      have hh := ((centralColumn i j k).prism_volume_pos _ _).mp hp
      exact h ⟨hh.1,hh.2.1⟩
    have hv : localVariance volume R f (centralAnchorAverage 0 f)=0 := by
      simp [localVariance,Measure.restrict_eq_zero.mpr hz]
    change localVariance volume R f (centralAnchorAverage 0 f) ≤ _
    rw [hv]
    exact mul_nonneg (centralColumnConstant_nonneg i j k) (integral_nonneg (cubeEnergyDensity_nonneg f))

lemma localVariance_finset_union_le {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (Q : ι → Set X) {f : X → ℝ} {a : ℝ}
    (hi : ∀ i∈s,IntegrableOn (fun z => (f z-a)^2) (Q i) μ) :
    localVariance μ (⋃ i∈s,Q i) f a ≤ ∑ i∈s,localVariance μ (Q i) f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localVariance]
  | @insert i s hin ih =>
    have his : ∀ j∈s,IntegrableOn (fun z => (f z-a)^2) (Q j) μ := fun j hj => hi j (Finset.mem_insert_of_mem hj)
    have h_union : IntegrableOn (fun z => (f z-a)^2) (⋃ j∈s,Q j) μ := by
      exact integrableOn_finset_iUnion.mpr his
    simpa only [Finset.set_biUnion_insert,Finset.sum_insert hin] using
      (localVariance_union_le μ (hi i (Finset.mem_insert_self _ _)) h_union).trans
        (add_le_add_right (ih his) _)

def centralPoincareConstant : ℝ := centralAnchorConstant+
  ∑ i : Fin 4,∑ j : Fin 5,∑ k : Fin 5,centralColumnConstant i j k

lemma centralPoincareConstant_nonneg : 0 ≤ centralPoincareConstant := by
  apply add_nonneg centralAnchorConstant_nonneg
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun k _ => centralColumnConstant_nonneg i j k)))

theorem central_physical_poincare {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume centralClosed f (centralAnchorAverage 0 f) ≤
      centralPoincareConstant*(∫ z in centralClosed,cubeEnergyDensity f z) := by
  let Q : (Fin 4×Fin 5×Fin 5) → Set Box3 := fun p =>
    (centralColumn p.1 p.2.1 p.2.2).prism (-centralHeight) centralHeight
  let U := ⋃ p,Q p
  have hu : IsCompact U := isCompact_iUnion (fun p => (centralColumn p.1 p.2.1 p.2.2).prism_compact _ _)
  have hiu : IntegrableOn (fun z => (f z-centralAnchorAverage 0 f)^2) U :=
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact hu
  have hia : IntegrableOn (fun z => (f z-centralAnchorAverage 0 f)^2) centralAnchor :=
    ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact (centralCluster_compact 8)
  have hsub : centralClosed⊆centralAnchor∪U := by
    rw [centralClosed_cover]
    rintro z ((ht|hb)|hc)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp ht
      exact Or.inl (centralTop_subset_anchor i hi)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hb
      exact Or.inl (centralBottom_subset_anchor i hi)
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hc
      obtain ⟨j,hj⟩ := mem_iUnion.mp hi
      obtain ⟨k,hk⟩ := mem_iUnion.mp hj
      exact Or.inr (mem_iUnion.mpr ⟨(i,j,k),hk⟩)
  have hv := localVariance_finset_union_le volume Finset.univ Q
    (fun p _ => ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      ((centralColumn p.1 p.2.1 p.2.2).prism_compact _ _)) (a := centralAnchorAverage 0 f)
  simp only [Finset.mem_univ,iUnion_true, Fintype.sum_prod_type] at hv
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun k _ => centralColumn_poincare i j k hf)))
  calc localVariance volume centralClosed f (centralAnchorAverage 0 f)
      ≤ localVariance volume centralAnchor f (centralAnchorAverage 0 f)+localVariance volume U f (centralAnchorAverage 0 f) :=
        (localVariance_mono volume (hia.union hiu) hsub).trans (localVariance_union_le volume hia hiu)
    _ ≤ centralAnchorConstant*(∫ z in centralClosed,cubeEnergyDensity f z)+
        (∑ i : Fin 4,∑ j : Fin 5,∑ k : Fin 5,centralColumnConstant i j k*(∫ z in centralClosed,cubeEnergyDensity f z)) :=
      add_le_add (centralAnchor_poincare hf) (hv.trans hb)
    _ = centralPoincareConstant*(∫ z in centralClosed,cubeEnergyDensity f z) := by
      simp only [centralPoincareConstant,add_mul,Finset.sum_mul]

open Set MeasureTheory
open scoped ENNReal

def centralMeasure : Measure Box3 := volume.restrict centralClosed

instance centralMeasure_finite : IsFiniteMeasure centralMeasure := by
  constructor
  simpa [centralMeasure] using centralClosed_compact.measure_lt_top

def centralSmoothFunctions : Submodule ℝ (Box3 → ℝ) where
  carrier := {f | ContDiff ℝ (↑(⊤ : ℕ∞)) f}
  zero_mem' := by change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun _ : Box3 => (0 : ℝ)); exact contDiff_const
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) f from hf).add (show ContDiff ℝ (↑(⊤ : ℕ∞)) g from hg)
  smul_mem' := by
    intro c f hf
    exact (show ContDiff ℝ (↑(⊤ : ℕ∞)) f from hf).const_smul c

instance : CoeFun centralSmoothFunctions (fun _ => Box3 → ℝ) := ⟨fun f => f.val⟩

lemma central_smooth (f : centralSmoothFunctions) : ContDiff ℝ (↑(⊤ : ℕ∞)) f := f.property

abbrev CentralL2 := Lp ℝ 2 centralMeasure
abbrev CentralJets := PiLp 2 (fun _ : Fin 4 => CentralL2)
abbrev CentralGradients := PiLp 2 (fun _ : Fin 3 => CentralL2)

lemma central_continuous_memLp {f : Box3 → ℝ} (hf : Continuous f) : MemLp f 2 centralMeasure := by
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact centralClosed_compact)

def centralJetField (f : Box3 → ℝ) (i : Fin 4) : Box3 → ℝ :=
  ![f,cubePartial f ((1,0),0),cubePartial f ((0,1),0),cubePartial f ((0,0),1)] i

lemma centralJetField_continuous (f : centralSmoothFunctions) (i : Fin 4) :
    Continuous (centralJetField f i) := by
  fin_cases i
  · exact (central_smooth f).continuous
  · exact continuous_cubePartial (central_smooth f) _
  · exact continuous_cubePartial (central_smooth f) _
  · exact continuous_cubePartial (central_smooth f) _

def centralSmoothJet (f : centralSmoothFunctions) : CentralJets :=
  WithLp.toLp 2 (fun i => (central_continuous_memLp (centralJetField_continuous f i)).toLp (centralJetField f i))

lemma centralSmoothJet_ae (f : centralSmoothFunctions) (i : Fin 4) :
    centralSmoothJet f i=ᵐ[centralMeasure] centralJetField f i := (central_continuous_memLp (centralJetField_continuous f i)).coeFn_toLp

lemma centralJetField_add (f g : centralSmoothFunctions) (i : Fin 4) :
    centralJetField (f+g) i=centralJetField f i+centralJetField g i := by
  funext z
  have he := fderiv_add ((central_smooth f).differentiable (by simp) z) ((central_smooth g).differentiable (by simp) z)
  change fderiv ℝ (fun y => f y+g y) z=_ at he
  fin_cases i
  · rfl
  · change (fderiv ℝ (fun y => f y+g y) z) ((1,0),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => f y+g y) z) ((0,1),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => f y+g y) z) ((0,0),1)=_
    rw [he]; rfl

lemma centralJetField_smul (c : ℝ) (f : centralSmoothFunctions) (i : Fin 4) :
    centralJetField (c•f) i=c•centralJetField f i := by
  funext z
  have he := fderiv_const_smul ((central_smooth f).differentiable (by simp) z) c
  change fderiv ℝ (fun y => c • f y) z=_ at he
  fin_cases i
  · rfl
  · change (fderiv ℝ (fun y => c • f y) z) ((1,0),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => c • f y) z) ((0,1),0)=_
    rw [he]; rfl
  · change (fderiv ℝ (fun y => c • f y) z) ((0,0),1)=_
    rw [he]; rfl

def centralSmoothJetL : centralSmoothFunctions →ₗ[ℝ] CentralJets where
  toFun := centralSmoothJet
  map_add' := by
    intro f g
    apply PiLp.ext; intro i; apply Lp.ext
    filter_upwards [centralSmoothJet_ae (f+g) i,centralSmoothJet_ae f i,centralSmoothJet_ae g i,
      Lp.coeFn_add (centralSmoothJet f i) (centralSmoothJet g i)] with z hz hf hg ha
    change (centralSmoothJet (f+g) i) z=((centralSmoothJet f i)+(centralSmoothJet g i)) z
    rw [hz,ha]
    simp only [Pi.add_apply,hf,hg]
    exact congrFun (centralJetField_add f g i) z
  map_smul' := by
    intro c f
    apply PiLp.ext; intro i; apply Lp.ext
    filter_upwards [centralSmoothJet_ae (c•f) i,centralSmoothJet_ae f i,
      Lp.coeFn_smul c (centralSmoothJet f i)] with z hz hf ha
    change (centralSmoothJet (c•f) i) z=(c•(centralSmoothJet f i)) z
    rw [hz,ha]
    simp only [Pi.smul_apply,hf]
    exact congrFun (centralJetField_smul c f i) z

def centralJetD : CentralJets →L[ℝ] CentralGradients :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => CentralL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : Fin 3 => PiLp.proj 2 (fun _ : Fin 4 => CentralL2) i.succ))

lemma centralSmoothJet_norm_coordinate (f : centralSmoothFunctions) (i : Fin 4) :
    ‖centralSmoothJet f i‖^2=∫ z in centralClosed,(centralJetField f i z)^2 := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [centralSmoothJet_ae f i] with z hz
  simp [hz,pow_two]

lemma centralSmoothJet_gradient_norm (f : centralSmoothFunctions) :
    ‖centralJetD (centralSmoothJet f)‖^2=∫ z in centralClosed,cubeEnergyDensity f z := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 3,‖centralSmoothJet f i.succ‖^2)=_
  simp only [centralSmoothJet_norm_coordinate]
  have h0 := (central_continuous_memLp (continuous_cubePartial (central_smooth f) ((1,0),0))).integrable_sq
  have h1 := (central_continuous_memLp (continuous_cubePartial (central_smooth f) ((0,1),0))).integrable_sq
  have h2 := (central_continuous_memLp (continuous_cubePartial (central_smooth f) ((0,0),1))).integrable_sq
  dsimp [centralMeasure] at h0 h1 h2
  simp only [Fin.sum_univ_succ,Fin.isValue,centralJetField,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero]
  unfold cubeEnergyDensity
  have ha := integral_add h0 h1
  have hb := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at ha hb
  rw [hb,ha]
  ring

lemma centralSmoothJet_norm (f : centralSmoothFunctions) :
    ‖centralSmoothJet f‖^2=(∫ z in centralClosed,(f z)^2)+‖centralJetD (centralSmoothJet f)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ]
  rw [centralSmoothJet_norm_coordinate]
  congr 1
  exact (PiLp.norm_sq_eq_of_L2 _ (centralJetD (centralSmoothJet f))).symm

end ScalarConductivity

end

end OAI
