import OAI.Geometry.PlaneColoring.BinaryPalettes

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
def fourGroup (s : Fin 3) : Finset (Fin 5) := if s=0 then {4} else if s=1 then {0,2} else {1,3}
def fourEdge (e : Fin 4) : Finset (Fin 5) :=
  if e=0 then {0,1} else if e=1 then {1,2} else if e=2 then {2,3} else {3,0}
def fourCanonical (p : Finset (Fin 5)) : Fin 3 := if 4∈p then 0 else if 0∈p then 1 else 2
def FourAdmissible (p : Finset (Fin 5)) : Prop :=
  p.Nonempty ∧ p.card≤2 ∧ ∀ e : Fin 4, ¬p⊆fourEdge e
lemma fourGroup_nonempty (s : Fin 3) : (fourGroup s).Nonempty := by
  fin_cases s <;> simp [fourGroup]
lemma four_admissible_group : ∀ p : Finset (Fin 5), FourAdmissible p → fourGroup (fourCanonical p)⊆p := by
  unfold FourAdmissible
  decide
lemma four_group_unique : ∀ p : Finset (Fin 5), p.card≤2 → ∀ s t : Fin 3,
    fourGroup s⊆p → fourGroup t⊆p → s=t := by decide
lemma four_admissible_character : ∀ p : Finset (Fin 5), FourAdmissible p → ∀ s : Fin 3,
    fourGroup s⊆p ↔ fourCanonical p=s := by
  intro p hp s
  constructor
  · intro hs
    exact (four_group_unique p hp.2.1 s (fourCanonical p) hs (four_admissible_group p hp)).symm
  · rintro rfl
    exact four_admissible_group p hp
lemma four_trace_edge : ∀ p : Finset (Fin 5), FourAdmissible p → ∀ i∈fourGroup (fourCanonical p),
    ∃ e : Fin 4, i∉fourEdge e ∧ p\{i}⊆fourEdge e := by
  unfold FourAdmissible
  decide
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma LineDensityZero.mono_ae {A B : Set ℝ} {t : ℝ}
    (hB : LineDensityZero B t) (hAB : A≤ᵐ[volume] B) : LineDensityZero A t := by
  apply squeeze_zero' ?_ ?_ hB
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact div_nonneg measureReal_nonneg (le_of_lt hr)
  · filter_upwards [self_mem_nhdsWithin] with r hr
    apply div_le_div_of_nonneg_right _ (le_of_lt hr)
    apply ENNReal.toReal_mono
    · exact ne_top_of_le_ne_top (isCompact_closedBall t r).measure_ne_top (measure_mono inter_subset_right)
    · exact measure_mono_ae (hAB.mono fun _ hz h => ⟨hz h.1,h.2⟩)
def DensityZero (A : Set ℂ) (x : ℂ) : Prop :=
  Tendsto (fun r : ℝ => volume (A∩Metric.closedBall x r)/volume (Metric.closedBall x r))
    (𝓝[>] 0) (𝓝 (0:ENNReal))
lemma DensityZero.mono {A B : Set ℂ} {x : ℂ} (hB : DensityZero B x) (hAB : A⊆B) :
    DensityZero A x := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun _ => zero_le)
  intro r
  exact ENNReal.div_le_div_right (measure_mono (inter_subset_inter_left _ hAB)) _
lemma DensityZero.union {A B : Set ℂ} {x : ℂ} (hA : DensityZero A x) (hB : DensityZero B x) :
    DensityZero (A∪B) x := by
  have hh := hA.add hB
  rw [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => zero_le)
  intro r
  dsimp only
  rw [← ENNReal.add_div,union_inter_distrib_right]
  exact ENNReal.div_le_div_right (measure_union_le _ _) _
lemma densityZero_empty (x : ℂ) : DensityZero ∅ x := by
  simp only [DensityZero,empty_inter,measure_empty,ENNReal.zero_div]
  exact tendsto_const_nhds
lemma DensityZero.biUnion_finset {ι : Type*} (J : Finset ι) {A : ι → Set ℂ} {x : ℂ}
    (hA : ∀ i∈J,DensityZero (A i) x) : DensityZero (⋃ i∈J,A i) x := by
  classical
  induction J using Finset.induction_on with
  | empty => simpa using densityZero_empty x
  | @insert i J hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (hA i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))
lemma DensityZero.compl {A : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (hz : DensityZero A x) :
    DensityOne Aᶜ x := by
  have ht := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ENNReal))) hz (Or.inl (by finiteness))
  rw [tsub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hfin : volume (A∩Metric.closedBall x r)≠⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top (measure_mono inter_subset_right)
  have hp := (Metric.measure_closedBall_pos volume x hr).ne'
  have he : Aᶜ∩Metric.closedBall x r=Metric.closedBall x r\(A∩Metric.closedBall x r) := by
    ext z; simp; tauto
  rw [he,measure_sdiff inter_subset_right (hA.inter measurableSet_closedBall).nullMeasurableSet hfin,
    ENNReal.sub_div (fun _ _ => hp),ENNReal.div_self hp (isCompact_closedBall x r).measure_ne_top]
variable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
def RealState (x : ℂ) (A : Set ℝ) (J : Finset (Fin k)) : Prop :=
  MeasurableSet A ∧ ∀ i∈J, A≤ᵐ[volume] liftPalette c hc x i
lemma state_densityZero (hw : WeakColoring k c) {x : ℂ} {A : Set ℝ} {J : Finset (Fin k)}
    (hA : RealState hc x A J) {t u : ℝ} (ht : LineDensityZero Aᶜ t)
    (hu : Real.sin (u-t)≠0) {i : Fin k} (hi : i∈J) :
    DensityZero {z | c z=i} (angularSum x 1 (angleChart (t,u))) := by
  apply palette_spatial_densityZero c hc hw _ hu
  apply ht.mono_ae
  filter_upwards [hA.2 i hi] with v hv
  exact mt hv
lemma angularSum_swap (x : ℂ) (t u : ℝ) :
    angularSum x 1 (angleChart (u,t))=angularSum x 1 (angleChart (t,u)) := by
  simp only [angularSum,angleChart,Complex.ofReal_one,one_mul]
  ring
lemma states_densityOne (hw : WeakColoring k c) {x : ℂ} {A B : Set ℝ} {J K : Finset (Fin k)}
    (hA : RealState hc x A J) (hB : RealState hc x B K) {t u : ℝ}
    (ht : LineDensityZero Aᶜ t) (hu : LineDensityZero Bᶜ u) (hne : Real.sin (u-t)≠0) :
    DensityOne {z | c z∉J∪K} (angularSum x 1 (angleChart (t,u))) := by
  have hz : DensityZero (⋃ i∈J∪K, {z | c z=i}) (angularSum x 1 (angleChart (t,u))) := by
    apply DensityZero.biUnion_finset
    intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact state_densityZero hc hw hA ht hne hi
    · rw [← angularSum_swap x t u]
      apply state_densityZero hc hw hB hu _ hi
      rwa [← neg_sub u t,Real.sin_neg,neg_ne_zero]
  have hm : MeasurableSet (⋃ i∈J∪K, {z | c z=i}) :=
    (J∪K).measurableSet_biUnion fun _ _ => measurableSet_eq_fun hc measurable_const
  convert hz.compl hm using 1
  ext z
  simp only [mem_compl_iff,mem_iUnion,mem_ofPred_eq]
  aesop
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma DensityOne.compl {A : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (h : DensityOne A x) :
    DensityZero Aᶜ x := by
  have ht := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1:ENNReal))) h (Or.inl (by finiteness))
  rw [tsub_self] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hfin : volume (A∩Metric.closedBall x r)≠⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall x r).measure_ne_top (measure_mono inter_subset_right)
  have hp := (Metric.measure_closedBall_pos volume x hr).ne'
  have he : Aᶜ∩Metric.closedBall x r=Metric.closedBall x r\(A∩Metric.closedBall x r) := by
    ext z; simp; tauto
  rw [he,measure_sdiff inter_subset_right (hA.inter measurableSet_closedBall).nullMeasurableSet hfin,
    ENNReal.sub_div (fun _ _ => hp),ENNReal.div_self hp (isCompact_closedBall x r).measure_ne_top]
lemma DensityOne.inter {A B : Set ℂ} {x : ℂ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (ha : DensityOne A x) (hb : DensityOne B x) : DensityOne (A∩B) x := by
  have hh := ((ha.compl hA).union (hb.compl hB)).compl (hA.compl.union hB.compl)
  simpa using hh
lemma DensityOne.measure_ne_zero {A : Set ℂ} {x : ℂ} (h : DensityOne A x) : volume A≠0 := by
  intro hz
  have hzero : (fun r => volume (A∩Metric.closedBall x r)/volume (Metric.closedBall x r))=fun _ : ℝ => (0:ENNReal) := by
    funext r
    rw [measure_mono_null inter_subset_left hz,ENNReal.zero_div]
  change Tendsto _ _ _ at h
  rw [hzero] at h
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h)
lemma densityOne_univ (x : ℂ) : DensityOne univ x := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [univ_inter]
  exact (ENNReal.div_self (Metric.measure_closedBall_pos volume x hr).ne'
    (isCompact_closedBall x r).measure_ne_top).symm
lemma DensityOne.iInter {ι : Type*} [Finite ι] {A : ι → Set ℂ} {x : ℂ}
    (hm : ∀i,MeasurableSet (A i)) (h : ∀i,DensityOne (A i) x) : DensityOne (⋂i,A i) x := by
  classical
  let := Fintype.ofFinite ι
  have hh (J : Finset ι) : DensityOne (⋂i∈J,A i) x := by
    induction J using Finset.induction_on with
    | empty => simpa using densityOne_univ x
    | @insert i J hi ih =>
      simp only [Finset.set_biInter_insert]
      exact (h i).inter (hm i) (J.measurableSet_biInter fun j _ => hm j) ih
  simpa using hh Finset.univ
variable {k : ℕ} {c : ℂ → Fin k}
lemma finite_density_realization (hc : Measurable c) (hw : WeakColoring k c)
    {ι : Type*} [Finite ι] (z : ι → ℂ) (J : ι → Finset (Fin k))
    (hz : ∀v,DensityOne {q | c q∈J v} (z v)) :
    ∃q : ℂ, (∀v,c (q+z v)∈J v) ∧
      ∀v w, ‖z v-z w‖=1 → c (q+z v)≠c (q+z w) := by
  have hmem : DensityOne (⋂v,{q | c (q+z v)∈J v}) 0 := by
    apply DensityOne.iInter
    · intro v
      exact (J v).finite_toSet.measurableSet.preimage (hc.comp (measurable_id.add_const _))
    · intro v
      simpa only [zero_add,preimage_ofPred_eq] using (densityOne_translate (A := {q | c q∈J v}) (x := 0) (u := z v)).mpr (by simpa using hz v)
  have hproper : ∀ᵐ q : ℂ ∂volume, ∀v w, ‖z v-z w‖=1 → c (q+z v)≠c (q+z w) := by
    apply ae_all_iff.mpr
    intro v
    apply ae_all_iff.mpr
    intro w
    by_cases hh : ‖z v-z w‖=1
    · obtain ⟨t,ht⟩ := direction_exists (u := z w-z v) (by simpa only [norm_sub_rev] using hh)
      have hd := (measurePreserving_add_right volume (z v)).quasiMeasurePreserving.ae
        (weak_all_directions c hc hw t)
      filter_upwards [hd] with q hq _
      simpa only [ht,show q+z v+(z w-z v)=q+z w by ring] using hq
    · exact Eventually.of_forall fun _ => fun h => (hh h).elim
  obtain ⟨q,hq,hqp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmem.measure_ne_zero (ae_restrict_of_ae hproper)
  exact ⟨q,fun v => mem_iInter.mp hq v,hqp⟩
lemma two_label_triangle_impossible (hc : Measurable c) (hw : WeakColoring k c)
    (z : Fin 3 → ℂ) (J : Finset (Fin k)) (hJ : J.card≤2)
    (hd : ∀v w,v≠w → ‖z v-z w‖=1) :
    ¬(∀v,DensityOne {q | c q∈J} (z v)) := by
  intro hz
  obtain ⟨q,hq,hp⟩ := finite_density_realization hc hw z (fun _ => J) hz
  have hinj : Function.Injective (fun v : Fin 3 => (⟨c (q+z v),hq v⟩ : J)) := by
    intro v w he
    by_contra hne
    exact hp v w (hd v w hne) (congrArg Subtype.val he)
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin,Fintype.card_coe] at hcard
  omega
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma bool_flip_two {s : ℝ → Bool} {κ : ℝ}
    (h : ∀ᵐt∂volume,s (t+κ)= !(s t)) : ∀ᵐt∂volume,s (t+2*κ)=s t := by
  have h' := (measurePreserving_add_right volume κ).quasiMeasurePreserving.ae h
  filter_upwards [h,h'] with t ht ht'
  rw [show t+κ+κ=t+2*κ by ring,ht,Bool.not_not] at ht'
  exact ht'
lemma bool_flip_three {s : ℝ → Bool} {κ : ℝ}
    (h : ∀ᵐt∂volume,s (t+κ)= !(s t)) : ∀ᵐt∂volume,s (t+3*κ)= !(s t) := by
  have h' := (measurePreserving_add_right volume (2*κ)).quasiMeasurePreserving.ae h
  filter_upwards [bool_flip_two h,h'] with t ht ht'
  rwa [show t+2*κ+κ=t+3*κ by ring,ht] at ht'
lemma bool_flip_even {s : ℝ → Bool} {κ : ℝ}
    (h : ∀ᵐt∂volume,s (t+κ)= !(s t)) (n : ℕ) : ∀ᵐt∂volume,s (t+2*n*κ)=s t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' := (measurePreserving_add_right volume (2*n*κ)).quasiMeasurePreserving.ae (bool_flip_two h)
    filter_upwards [ih,h'] with t ht ht'
    rw [ht] at ht'
    convert ht' using 1
    norm_num
    congr 1
    ring
lemma triangleAngle_nonparallel : Real.sin (Real.pi+triangleAngle)≠0 := by
  rw [add_comm,Real.sin_add_pi,neg_ne_zero]
  exact (Real.sin_pos_of_pos_of_lt_pi triangleAngle_pos triangleAngle_lt_pi).ne'
lemma two_state_impossible {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℂ) (J K : Finset (Fin k)) (hcard : (Finset.univ\(J∪K)).card≤2)
    (s : Angles → Bool) (hs : Measurable s)
    (hJ : RealState hc x {t : ℝ | s (t : Angles)=false} J)
    (hK : RealState hc x {t : ℝ | s (t : Angles)=true} K)
    (hflip : ∀ᵐt∂angularMeasure,s (t+(Real.pi/3 : ℝ))= !(s t)) : False := by
  let f : ℝ → Bool := fun t => s (t : Angles)
  have hf : Measurable f := hs.comp angleMk_quasiMeasurePreserving.measurable
  have hflip' : ∀ᵐt : ℝ ∂volume, f (t+Real.pi/3)= !(f t) := by
    have hh := angleMk_quasiMeasurePreserving.ae hflip
    simpa only [← AddCircle.coe_add] using hh
  have heven (n : ℕ) := bool_flip_even hflip' n
  have hπ : ∀ᵐt : ℝ ∂volume, f (t+Real.pi)= !(f t) := by
    simpa only [show 3*(Real.pi/3)=Real.pi by ring] using bool_flip_three hflip'
  have hden : ∀ᵐt : ℝ ∂volume, ∀b : Bool, f t=b → LineDensityZero {a : ℝ | f a≠b} t := by
    apply ae_all_iff.mpr
    intro b
    exact ae_lineDensityZero_compl (measurableSet_eq_fun hf measurable_const)
  have hgood : ∀ᵐt : ℝ ∂volume, ∀j : Fin 3,
      f (t+2*(j:ℝ)*(Real.pi/3))=f t ∧
      f (t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)= !(f (t+triangleAngle)) ∧
      (∀b : Bool,f (t+2*(j:ℝ)*(Real.pi/3))=b →
        LineDensityZero {a : ℝ | f a≠b} (t+2*(j:ℝ)*(Real.pi/3))) ∧
      (∀b : Bool,f (t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)=b →
        LineDensityZero {a : ℝ | f a≠b} (t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)) := by
    apply ae_all_iff.mpr
    intro j
    have h₁ := heven j.val
    have h₂ := (measurePreserving_add_right volume triangleAngle).quasiMeasurePreserving.ae (heven j.val)
    have h₃ := (measurePreserving_add_right volume (triangleAngle+2*(j:ℝ)*(Real.pi/3))).quasiMeasurePreserving.ae hπ
    have h₄ := (measurePreserving_add_right volume (2*(j:ℝ)*(Real.pi/3))).quasiMeasurePreserving.ae hden
    have h₅ := (measurePreserving_add_right volume (2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)).quasiMeasurePreserving.ae hden
    filter_upwards [h₁,h₂,h₃,h₄,h₅] with t ht₁ ht₂ ht₃ ht₄ ht₅
    refine ⟨ht₁,?_,ht₄,?_⟩
    · change f (t+(triangleAngle+2*(j:ℝ)*(Real.pi/3))+Real.pi)= !(f (t+(triangleAngle+2*(j:ℝ)*(Real.pi/3)))) at ht₃
      rw [show t+(triangleAngle+2*(j:ℝ)*(Real.pi/3))=t+triangleAngle+2*(j:ℝ)*(Real.pi/3) by ring,ht₂] at ht₃
      simpa only [show t+triangleAngle+2*(j:ℝ)*(Real.pi/3)+Real.pi = t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle by ring] using ht₃
    · simpa only [show t+(2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)=t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle by ring] using ht₅
  have hfreq : ∃ᶠt : ℝ in ae volume, f t=f (t+triangleAngle) := by
    by_contra hh
    have hn : ∀ᵐt : ℝ ∂volume, f t≠f (t+triangleAngle) := not_frequently.mp hh
    have ha : ∀ᵐt∂angularMeasure,s t≠s (t+(triangleAngle : Angles)) := by
      apply ae_angular_of_ae_line
      · exact (measurableSet_eq_fun hs (hs.comp (measurable_id.add_const _))).compl
      · simpa only [f,← AddCircle.coe_add] using hn
    exact (ne_of_gt (equal_triangleAngle_positive hs hflip))
      (measure_eq_zero_iff_ae_notMem.mpr ha)
  obtain ⟨t,hteq,htgood⟩ := (hfreq.and_eventually hgood).exists
  apply two_label_triangle_impossible hc hw (sourceTriangle x t) (Finset.univ\(J∪K)) hcard
    (sourceTriangle_pair x t)
  intro j
  obtain ⟨h₁,h₂,h₃,h₄⟩ := htgood j
  rw [← hteq] at h₂
  have hne : Real.sin ((t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)-(t+2*(j:ℝ)*(Real.pi/3)))≠0 := by
    rw [show (t+2*(j:ℝ)*(Real.pi/3)+Real.pi+triangleAngle)-(t+2*(j:ℝ)*(Real.pi/3))=Real.pi+triangleAngle by ring]
    exact triangleAngle_nonparallel
  have hd : DensityOne {q | c q∉J∪K} (sourceTriangle x t j) := by
    cases hb : f t
    · have ha := h₃ false (h₁.trans hb)
      have hb' := h₄ true (by simpa [hb] using h₂)
      exact states_densityOne hc hw hJ hK ha hb' hne
    · have ha := h₃ true (h₁.trans hb)
      have hb' := h₄ false (by simpa [hb] using h₂)
      simpa only [Finset.union_comm,sourceTriangle] using states_densityOne hc hw hK hJ ha hb' hne
  simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and] using hd
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def FourCenter (x : ℂ) : Prop :=
  TransitionEdge c 0 1 x ∧ TransitionEdge c 1 2 x ∧ TransitionEdge c 2 3 x ∧ TransitionEdge c 3 0 x
lemma four_palette_admissible (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∀ᵐ t∂angularMeasure, FourAdmissible (palette c hc x t) := by
  filter_upwards [palette_nonempty c hc x,palette_cardinality c hc hw x,
    edge_palette_not_pair c hc hw hx.1,edge_palette_not_pair c hc hw hx.2.1,
    edge_palette_not_pair c hc hw hx.2.2.1,edge_palette_not_pair c hc hw hx.2.2.2] with t ht hcard h01 h12 h23 h30
  refine ⟨ht,hcard.2,?_⟩
  intro e
  fin_cases e <;> simp only [fourEdge] <;> assumption
def fourState (x : ℂ) (t : Angles) : Fin 3 := fourCanonical (palette c hc x t)
lemma fourState_measurable (x : ℂ) : Measurable (fourState c hc x) := by
  change Measurable (fun t => if 4∈palette c hc x t then (0:Fin 3) else if 0∈palette c hc x t then 1 else 2)
  exact Measurable.ite (by simpa only [mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x 4) measurable_const
    (Measurable.ite (by simpa only [mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x 0) measurable_const measurable_const)
lemma fourState_group (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∀ᵐ t∂angularMeasure, fourGroup (fourState c hc x t)⊆palette c hc x t :=
  (four_palette_admissible c hc hw hx).mono fun _ ht => four_admissible_group _ ht
lemma fourState_represents (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) (s : Fin 3) :
    RealState hc x {t : ℝ | fourState c hc x (t : Angles)=s} (fourGroup s) := by
  refine ⟨measurableSet_eq_fun ((fourState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) measurable_const,?_⟩
  intro i hi
  have hh := angleMk_quasiMeasurePreserving.ae (fourState_group c hc hw hx)
  filter_upwards [hh] with t ht hts
  change fourState c hc x (t : Angles)=s at hts
  exact (mem_palette c hc x (t : Angles) i).mp (ht (by simpa only [hts] using hi))
lemma fourState_changes (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∀ᵐ t∂angularMeasure, fourState c hc x t≠fourState c hc x (t+(Real.pi/3 : ℝ)) := by
  have hgp := fourState_group c hc hw hx
  filter_upwards [hgp,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hgp,
    palette_sixty_disjoint c hc hw x] with t ht hu hd he
  obtain ⟨i,hi⟩ := fourGroup_nonempty (fourState c hc x t)
  have hi' : i∈palette c hc x (t+(sixty : Angles)) := hu (by simpa only [sixty,he] using hi)
  exact Finset.disjoint_left.mp hd (ht hi) hi'
lemma three_exclude_flip : ∀ (s t o : Fin 3), o≠0 → s≠o → t≠o → s≠t →
    (if t=0 then false else true) = !(if s=0 then false else true) := by decide
lemma fourState_diagonal_positive (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    (s : Fin 3) (hs : s≠0) : 0<angularMeasure {t | fourState c hc x t=s} := by
  by_contra! hn
  have hnot : ∀ᵐt∂angularMeasure, fourState c hc x t≠s :=
    measure_eq_zero_iff_ae_notMem.mp (le_antisymm hn zero_le)
  let r : Fin 3 := if s=1 then 2 else 1
  have hr : r≠0 ∧ r≠s ∧ ∀t : Fin 3,t≠0 → t≠s → t=r := by
    exact (show ∀s : Fin 3,s≠0 → (if s=1 then (2:Fin 3) else 1)≠0 ∧ (if s=1 then (2:Fin 3) else 1)≠s ∧
      ∀t : Fin 3,t≠0 → t≠s → t=(if s=1 then 2 else 1) from by decide) s hs
  let f : Angles → Bool := fun t => if fourState c hc x t=0 then false else true
  have hf : Measurable f := Measurable.ite
    (measurableSet_eq_fun (fourState_measurable c hc x) measurable_const) measurable_const measurable_const
  have hrep (v : Bool) : RealState hc x {t : ℝ | f (t : Angles)=v} (if v then fourGroup r else fourGroup 0) := by
    refine ⟨measurableSet_eq_fun (hf.comp angleMk_quasiMeasurePreserving.measurable) measurable_const,?_⟩
    intro i hi
    filter_upwards [angleMk_quasiMeasurePreserving.ae (fourState_group c hc hw hx),
      angleMk_quasiMeasurePreserving.ae hnot] with t ht htn htv
    change f (t : Angles)=v at htv
    apply (mem_palette c hc x (t : Angles) i).mp
    apply ht
    cases v
    · have hz : fourState c hc x (t : Angles)=0 := by simpa [f] using htv
      simpa only [hz,Bool.false_eq_true,ite_false] using hi
    · have hz : fourState c hc x (t : Angles)=r := hr.2.2 _ (by simpa [f] using htv) htn
      simpa only [hz,ite_true] using hi
  have hcard : (Finset.univ\(fourGroup 0∪fourGroup r)).card≤2 := by
    exact (show ∀s : Fin 3,s≠0 → (Finset.univ\(fourGroup 0∪fourGroup (if s=1 then 2 else 1))).card≤2 from by decide) s hs
  apply two_state_impossible hc hw x (fourGroup 0) (fourGroup r) hcard f hf (hrep false) (hrep true)
  filter_upwards [hnot,(measurePreserving_add_right angularMeasure (Real.pi/3 : ℝ)).quasiMeasurePreserving.ae hnot,
      fourState_changes c hc hw hx] with t ht hu hne
  exact three_exclude_flip _ _ s hs ht hu hne
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal
namespace EuclideanFiveColor
lemma varying_pullback_L1 {X Y : Type*} [MeasurableSpace X]
    [TopologicalSpace Y] [NormalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [ν.WeaklyRegular]
    {T : ℕ → X → Y} {S : X → Y} {C : ℝ≥0}
    (hT : ∀ n, Measurable (T n)) (hS : Measurable S)
    (hmT : ∀ᶠ n in atTop, μ.map (T n) ≤ (C : ENNReal) • ν) (hmS : μ.map S ≤ (C : ENNReal) • ν)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => T n x) atTop (𝓝 (S x)))
    {f : Y → ℝ} {g : ℕ → Y → ℝ} (hf : Integrable f ν) (hg : ∀ n, Integrable (g n) ν)
    (hgf : Tendsto (fun n => ∫ y, ‖g n y-f y‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖g n (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
  have hfixed := tendsto_integral_norm_comp_sub_eventual hT hS hmT hmS ht hf
  have hbound : Tendsto (fun n => (C : ℝ)*(∫ y, ‖g n y-f y‖ ∂ν)+
      ∫ x, ‖f (T n x)-f (S x)‖ ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hgf.const_mul (C : ℝ)).add hfixed
  apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [hmT] with n hn
  have hgT := integrable_comp_of_map_le (hT n) hn (hg n)
  have hfT := integrable_comp_of_map_le (hT n) hn hf
  have hfS := integrable_comp_of_map_le hS hmS hf
  calc
    _ ≤ ∫ x, ‖g n (T n x)-f (T n x)‖+‖f (T n x)-f (S x)‖ ∂μ :=
      integral_mono (hgT.sub hfS).norm ((hgT.sub hfT).norm.add (hfT.sub hfS).norm)
        (fun x => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = (∫ x, ‖g n (T n x)-f (T n x)‖ ∂μ)+(∫ x, ‖f (T n x)-f (S x)‖ ∂μ) :=
      integral_add (hgT.sub hfT).norm (hfT.sub hfS).norm
    _ ≤ _ := add_le_add (integral_norm_comp_le (hT n) hn ((hg n).sub hf)) le_rfl
lemma indicator_inter_positive {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {A : Set X} {B D : ℕ → Set X} (hA : MeasurableSet A)
    (hB : ∀ n,MeasurableSet (B n)) (hD : ∀ n,MeasurableSet (D n)) (hp : 0<μ A)
    (hBA : Tendsto (fun n => ∫ x, ‖(B n).indicator (fun _ => (1:ℝ)) x-A.indicator (fun _ => (1:ℝ)) x‖ ∂μ) atTop (𝓝 0))
    (hDA : Tendsto (fun n => ∫ x, ‖(D n).indicator (fun _ => (1:ℝ)) x-A.indicator (fun _ => (1:ℝ)) x‖ ∂μ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0<μ (B n∩D n) := by
  have hpos : 0<(μ A).toReal := ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)
  have ht := hBA.add hDA
  rw [add_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hpos)] with n hn
  by_contra hh
  have hz : μ (B n∩D n)=0 := nonpos_iff_eq_zero.mp (le_of_not_gt hh)
  have hiA : Integrable (A.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hA
  have hiB : Integrable ((B n).indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator (hB n)
  have hiD : Integrable ((D n).indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator (hD n)
  have hi := integral_mono_ae hiA ((hiB.sub hiA).norm.add (hiD.sub hiA).norm) ?_
  · simp only [Pi.add_apply] at hi
    rw [integral_add (hiB.sub hiA).norm (hiD.sub hiA).norm,integral_indicator_const (1:ℝ) hA,smul_eq_mul,mul_one] at hi
    exact (not_lt_of_ge hi) hn
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx
    by_cases ha : x∈A
    · by_cases hb : x∈B n
      · have hd : x∉D n := fun hd => hx ⟨hb,hd⟩
        simp [ha,hb,hd]
      · by_cases hd : x∈D n <;> simp [ha,hb,hd]
    · simp only [Pi.add_apply,Set.indicator_of_notMem ha]
      positivity
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma circleEndpoint_identity_neighborhood {a u : ℝ} (h : Real.sin (u-a)≠0) :
    ∃ I : Set ℝ, IsOpen I ∧ a∈I ∧
      ∀ v∈I, circleTarget (samplingParameter 0 (direction (u : Angles)) 1,v)∈(circleInverseHomeo h).target ∧
        circleEndpoint h (samplingParameter 0 (direction (u : Angles)) 1,v)=v := by
  let V := (circleInverseHomeo h).source
  have ha : (a,u)∈V := (circleSum_strict 1 (a,u)).mem_toOpenPartialHomeomorph_source
  let I := (fun v : ℝ => (v,u)) ⁻¹' V
  refine ⟨I,(circleInverseHomeo h).open_source.preimage (continuous_id.prodMk continuous_const),ha,?_⟩
  intro v hv
  have he : circleTarget (samplingParameter 0 (direction (u : Angles)) 1,v)=circleSum 1 (v,u) := by
    simp [circleTarget,samplingParameter,circleSum,add_comm]
  have hv' : (v,u)∈(circleInverseHomeo h).source := hv
  have ht : circleSum 1 (v,u)∈(circleInverseHomeo h).target := (circleInverseHomeo h).map_source hv'
  refine ⟨he ▸ ht,?_⟩
  rw [circleEndpoint,he,circleInverse_eq h ht]
  exact congrArg Prod.fst ((circleInverseHomeo h).left_inv hv')
lemma near_identity_circle_in {a u : ℝ} (h : Real.sin (u-a)≠0)
    {w : ℕ → ℂ} (hw : Tendsto w atTop (𝓝 (direction (u : Angles))))
    {V : Set ℝ} (hV : IsOpen V) (haV : a∈V) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ ∃ C : ℝ≥0, 1≤C ∧ ∃ T : ℕ → ℝ → ℝ,
      (∀ n,Measurable (T n)) ∧
      (∀ v∈Metric.ball a δ,Tendsto (fun n => T n v) atTop (𝓝 v)) ∧
      (∀ᶠ n in atTop, AntilipschitzWith C ((Metric.ball a δ).domRestrict (T n)) ∧
        MapsTo (T n) (Metric.ball a δ) (Metric.closedBall a 1) ∧
        MapsTo (T n) (Metric.ball a δ) V ∧
        ∀ v∈Metric.ball a δ, ‖w n+direction (v : Angles)-direction (T n v : Angles)‖=1) := by
  let p := samplingParameter 0 (direction (u : Angles)) 1
  have he : circleTarget (p,a)=circleSum 1 (a,u) := by
    simp [p,circleTarget,samplingParameter,circleSum,add_comm]
  have ha : Real.sin (a-u)≠0 := by rwa [← neg_sub u a,Real.sin_neg,neg_ne_zero]
  obtain ⟨P,I,hP,hp,hI,hai,hIp,K,hK,hctrl⟩ := circleEndpoint_good_neighborhood h he rfl ha
  obtain ⟨J,hJ,haj,hid⟩ := circleEndpoint_identity_neighborhood h
  have hcv : ∀ᶠ q in 𝓝 (p,a),circleEndpoint h q∈V := by
    apply (circleEndpoint_strict h he).continuousAt
    simpa only [circleEndpoint,he,circleInverse_at] using hV.mem_nhds haV
  obtain ⟨P₁,hP₁,I₁,hI₁,hsubV⟩ := mem_nhds_prod_iff.mp hcv
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem ((hI.inter hJ).mem_nhds ⟨hai,haj⟩) hI₁)
  let ε := min δ 1
  have hε : 0<ε := lt_min hδ (by norm_num)
  let T : ℕ → ℝ → ℝ := fun n v => circleEndpoint h (samplingParameter 0 (w n) 1,v)
  have hparam := samplingParameter_tendsto (x := 0) hw tendsto_const_nhds
  have hT (n : ℕ) : Measurable (T n) :=
    (circleEndpoint_measurable h).comp (measurable_const.prodMk measurable_id)
  refine ⟨ε,hε,min_le_right _ _,max K 1,le_max_right _ _,T,hT,?_,?_⟩
  · intro v hv
    have hvI := (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).1
    have hh := (circleInverse_continuousAt h (hid v hvI.2).1).fst.tendsto.comp
      (circleTarget_continuous.continuousAt.tendsto.comp (hparam.prodMk_nhds tendsto_const_nhds))
    have hid' := (hid v hvI.2).2
    change Tendsto (fun n => T n v) atTop (𝓝 (circleEndpoint h (p,v))) at hh
    simpa only [p,hid'] using hh
  · filter_upwards [hparam.eventually (hP.mem_nhds hp),hparam.eventually hP₁] with n hn hnV
    refine ⟨?_,?_,?_,?_⟩
    · apply AntilipschitzWith.of_le_mul_dist
      intro v z
      have hv := (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) v.2)).1.1
      have hz := (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) z.2)).1.1
      exact ((hK _ hn).le_mul_dist ⟨v,hv⟩ ⟨z,hz⟩).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left K 1) dist_nonneg)
    · intro v hv
      exact (hctrl _ hn v (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).1.1).2.2
    · intro v hv
      exact hsubV ⟨hnV,(hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).2⟩
    · intro v hv
      have ht := (hctrl _ hn v (hsub ((Metric.ball_subset_ball (min_le_left δ 1)) hv)).1.1).1
      have hh := circleInverse_sampling h ht
      simp only [Complex.ofReal_one,one_mul,angularSum,zero_add,angleChart] at hh
      change w n+direction (v : Angles)=direction (T n v : Angles)+
        direction (((circleInverse h (circleTarget (samplingParameter 0 (w n) 1,v))).2) : Angles) at hh
      rw [hh,add_sub_cancel_left]
      exact Circle.norm_coe _
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma nonparallel_neighborhood {a b : ℝ} (h : Real.sin (b-a)≠0)
    {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 b)) :
    ∃ V : Set ℝ, IsOpen V ∧ a∈V ∧ ∀ᶠ n in atTop, ∀ v∈V, Real.sin (s n-v)≠0 := by
  have hf : Continuous (fun q : ℝ×ℝ => Real.sin (q.2-q.1)) :=
    Real.continuous_sin.comp (continuous_snd.sub continuous_fst)
  have ho : IsOpen {q : ℝ×ℝ | Real.sin (q.2-q.1)≠0} :=
    isOpen_compl_singleton.preimage hf
  have hh : {q : ℝ×ℝ | Real.sin (q.2-q.1)≠0}∈𝓝 (a,b) := ho.mem_nhds h
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨Metric.ball a ε,Metric.isOpen_ball,Metric.mem_ball_self hε,?_⟩
  filter_upwards [hs.eventually (Metric.ball_mem_nhds b hε)] with n hn
  intro v hv
  exact @hsub (v,s n) (show max (dist v a) (dist (s n) b)<ε from max_lt hv hn)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma strict_state_sequence_local_false {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℕ → ℂ) (J K : Finset (Fin k)) (X : Fin k)
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    (A B : ℕ → Set ℝ) (D : Set ℝ) (hD : MeasurableSet D)
    (hA : ∀n,RealState hc (x n) (A n) J) (hB : ∀n,RealState hc (x n) (B n) K)
    (b d : ℕ → ℝ) (b₀ d₀ a u : ℝ)
    (hb : Tendsto b atTop (𝓝 b₀)) (hd : Tendsto d atTop (𝓝 d₀))
    (hbden : ∀n,LineDensityZero (B n)ᶜ (b n)) (hdden : ∀n,LineDensityZero (B n)ᶜ (d n))
    (hu : direction (u : Angles)=direction (b₀ : Angles)-direction (d₀ : Angles))
    (hab : Real.sin (b₀-a)≠0) (had : Real.sin (d₀-a)≠0) (hau : Real.sin (u-a)≠0)
    (hpos : ∀ε>0,0<volume (D∩Metric.ball a ε))
    (hL1 : ∀ E : Set ℝ, IsCompact E →
      Tendsto (fun n => ∫ v in E, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖)
        atTop (𝓝 0)) : False := by
  let w : ℕ → ℂ := fun n => direction (b n : Angles)-direction (d n : Angles)
  have hdir : Continuous (fun v : ℝ => direction (v : Angles)) := direction_continuous.comp (AddCircle.continuous_mk' (2*Real.pi))
  have hwt : Tendsto w atTop (𝓝 (direction (u : Angles))) := by
    rw [hu]
    exact (hdir.tendsto b₀ |>.comp hb).sub (hdir.tendsto d₀ |>.comp hd)
  obtain ⟨V,hV,haV,hparb⟩ := nonparallel_neighborhood hab hb
  obtain ⟨W,hW,haW,hpard⟩ := nonparallel_neighborhood had hd
  obtain ⟨δ,hδ,hδ1,C,hC,T,hT,hTlim,hctrl⟩ := near_identity_circle_in hau hwt hW haW
  obtain ⟨η,hη,hηV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds haV)
  let ε := min δ η
  have hε : 0<ε := lt_min hδ hη
  let I := Metric.ball a ε
  let E := Metric.closedBall a 1
  have hIE : I⊆E := (Metric.ball_subset_ball ((min_le_left δ η).trans hδ1)).trans Metric.ball_subset_closedBall
  have hIδ : I⊆Metric.ball a δ := Metric.ball_subset_ball (min_le_left δ η)
  have hIV : I⊆V := (Metric.ball_subset_ball (min_le_right δ η)).trans hηV
  let μ := volume.restrict I
  let ν := volume.restrict E
  have hEc : IsCompact E := isCompact_closedBall a 1
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hEc.measure_ne_top
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top hEc.measure_ne_top (measure_mono hIE))
  have : ν.WeaklyRegular := Measure.WeaklyRegular.restrict_of_measure_ne_top hEc.measure_lt_top.ne
  have hS : AntilipschitzWith C (I.domRestrict id) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro v z
    change dist v.1 z.1≤(C:ℝ)*dist v.1 z.1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (show (1:ℝ)≤C by exact_mod_cast hC) (dist_nonneg (x := v.1) (y := z.1))
  have hmS : μ.map id≤(C:ENNReal) •ν := line_map_restrict_volume_le measurable_id hEc.measurableSet hS hIE
  have hmT : ∀ᶠ n in atTop, μ.map (T n)≤(C:ENNReal) •ν := by
    filter_upwards [hctrl] with n hn
    apply line_map_restrict_volume_le (hT n) hEc.measurableSet
      (AntilipschitzWith.of_le_mul_dist fun v z => hn.1.le_mul_dist ⟨v,hIδ v.2⟩ ⟨z,hIδ z.2⟩)
    exact hn.2.1.mono_left hIδ
  have hiD : Integrable (D.indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator hD
  have hiA (n : ℕ) : Integrable ((A n).indicator (fun _ => (1:ℝ))) ν := (integrable_const _).indicator (hA n).1
  have hlimT : ∀ᵐ v ∂μ,Tendsto (fun n => T n v) atTop (𝓝 (id v)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with v hv
    exact hTlim v (hIδ hv)
  have hcomp := varying_pullback_L1 hT measurable_id hmT hmS hlimT hiD hiA (hL1 E hEc)
  have hdirect : Tendsto (fun n => ∫ v, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖ ∂μ)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun v => norm_nonneg _) _
      (by simpa only [mul_zero] using (hL1 E hEc).const_mul (C:ℝ))
    exact Eventually.of_forall fun n => integral_norm_comp_le measurable_id hmS ((hiA n).sub hiD)
  have hpre (n : ℕ) : MeasurableSet (T n ⁻¹' A n) := (hA n).1.preimage (hT n)
  have hcompeq (n : ℕ) (v : ℝ) : (T n ⁻¹' A n).indicator (fun _ => (1:ℝ)) v =
      (A n).indicator (fun _ => (1:ℝ)) (T n v) := by
    by_cases hv : T n v∈A n <;> simp [hv]
  have hpositive : ∀ᶠ n in atTop,0<μ (A n∩T n ⁻¹' A n) := by
    apply indicator_inter_positive hD (fun n => (hA n).1) hpre ?_ hdirect
    · simpa only [hcompeq,id_eq] using hcomp
    · simpa only [μ,Measure.restrict_apply hD,I] using hpos ε hε
  obtain ⟨n,hn,hbp,hdp,hp⟩ := (hctrl.and (hparb.and (hpard.and hpositive))).exists
  have hqmp : Measure.QuasiMeasurePreserving (T n) μ volume :=
    line_antilipschitz_qmp (hT n)
      (AntilipschitzWith.of_le_mul_dist fun v z => hn.1.le_mul_dist ⟨v,hIδ v.2⟩ ⟨z,hIδ z.2⟩)
  have hden := ae_lineDensityZero_compl (hA n).1
  have hgood : ∀ᵐ v ∂μ,v∈I ∧ (v∈A n → LineDensityZero (A n)ᶜ v) ∧
      (T n v∈A n → LineDensityZero (A n)ᶜ (T n v)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae hden,hqmp.ae hden] with v hv hd₁ hd₂
    exact ⟨hv,hd₁,hd₂⟩
  obtain ⟨v,hvA,hvI,hvden,hTvden⟩ := ((frequently_ae_mem_iff.mpr hp.ne').and_eventually hgood).exists
  have h₁ := states_densityOne hc hw (hA n) (hB n) (hvden hvA.1) (hbden n) (hbp v (hIV hvI))
  have h₂ := states_densityOne hc hw (hA n) (hB n) (hTvden hvA.2) (hdden n)
    (hdp (T n v) (hn.2.2.1 (hIδ hvI)))
  have he : {z | c z∉J∪K}={z | c z=X} := by ext z; exact hlabels (c z)
  rw [he] at h₁ h₂
  apply weak_density_proper c hc hw X _ h₁ h₂
  have hdist := hn.2.2.2 v (hIδ hvI)
  convert hdist using 1
  congr 1
  simp only [angularSum,angleChart,Complex.ofReal_one,one_mul,w]
  ring
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma positive_state_support_point {D : Set ℝ} (_hD : MeasurableSet D) (hp : 0<volume D)
    (b d u : ℝ) : ∃ a : ℝ, Real.sin (b-a)≠0 ∧ Real.sin (d-a)≠0 ∧ Real.sin (u-a)≠0 ∧
      ∀ ε>0,0<volume (D∩Metric.ball a ε) := by
  have hs : ∀ᵐ a ∂volume.restrict D, a∈(volume.restrict D).support ∧
      Real.sin (a-b)≠0 ∧ Real.sin (a-d)≠0 ∧ Real.sin (a-u)≠0 := by
    filter_upwards [(volume.restrict D).support_mem_ae,
      ae_restrict_of_ae (ae_sin_sub_ne_zero b),ae_restrict_of_ae (ae_sin_sub_ne_zero d),
      ae_restrict_of_ae (ae_sin_sub_ne_zero u)] with a ha hb hd hu
    exact ⟨ha,hb,hd,hu⟩
  obtain ⟨a,_,ha,hb,hd,hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp.ne' hs
  have hneg (v : ℝ) (hv : Real.sin (a-v)≠0) : Real.sin (v-a)≠0 := by
    rwa [← neg_sub a v,Real.sin_neg,neg_ne_zero]
  refine ⟨a,hneg b hb,hneg d hd,hneg u hu,?_⟩
  intro ε hε
  have hh := (Measure.mem_support_iff_forall a).mp ha (Metric.ball a ε) (Metric.ball_mem_nhds a hε)
  simpa only [Measure.restrict_apply measurableSet_ball,inter_comm] using hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma support_density_direction {B : Set ℝ} (hB : MeasurableSet B) {b : ℝ}
    (hb : b∈(volume.restrict B).support) {ε : ℝ} (hε : 0<ε) :
    ∃ t∈B, dist t b<ε ∧ LineDensityZero Bᶜ t := by
  have hp : 0<volume (B∩Metric.ball b ε) := by
    have hh := (Measure.mem_support_iff_forall b).mp hb (Metric.ball b ε) (Metric.ball_mem_nhds b hε)
    simpa only [Measure.restrict_apply measurableSet_ball,inter_comm] using hh
  obtain ⟨t,ht,hd⟩ := ((frequently_ae_mem_iff.mpr hp.ne').and_eventually (ae_lineDensityZero_compl hB)).exists
  exact ⟨t,ht.1,ht.2,hd ht.1⟩
lemma support_density_sequence {B : ℕ → Set ℝ} (hB : ∀n,MeasurableSet (B n))
    {b : ℕ → ℝ} {b₀ : ℝ} (hb : Tendsto b atTop (𝓝 b₀))
    (hs : ∀n,b n∈(volume.restrict (B n)).support) :
    ∃ d : ℕ → ℝ, Tendsto d atTop (𝓝 b₀) ∧ ∀n,LineDensityZero (B n)ᶜ (d n) := by
  have hp (n : ℕ) : 0<(1:ℝ)/(n+1) := by positivity
  choose d _hmem hdist hden using fun n => support_density_direction (hB n) (hs n) (hp n)
  refine ⟨d,?_,hden⟩
  apply hb.congr_dist
  simp only [dist_comm (b _) (d _)]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat
lemma strict_state_sequence_false {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    (x : ℕ → ℂ) (J K : Finset (Fin k)) (X : Fin k)
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    (A B : ℕ → Set ℝ) (D : Set ℝ) (hD : MeasurableSet D) (hp : 0<volume D)
    (hA : ∀n,RealState hc (x n) (A n) J) (hB : ∀n,RealState hc (x n) (B n) K)
    (b d : ℕ → ℝ) (b₀ d₀ : ℝ)
    (hb : Tendsto b atTop (𝓝 b₀)) (hd : Tendsto d atTop (𝓝 d₀))
    (hbs : ∀n,b n∈(volume.restrict (B n)).support)
    (hds : ∀n,d n∈(volume.restrict (B n)).support)
    (hu : ‖direction (b₀ : Angles)-direction (d₀ : Angles)‖=1)
    (hL1 : ∀ E : Set ℝ, IsCompact E →
      Tendsto (fun n => ∫ v in E, ‖(A n).indicator (fun _ => (1:ℝ)) v-D.indicator (fun _ => (1:ℝ)) v‖)
        atTop (𝓝 0)) : False := by
  obtain ⟨b',hb',hbden⟩ := support_density_sequence (fun n => (hB n).1) hb hbs
  obtain ⟨d',hd',hdden⟩ := support_density_sequence (fun n => (hB n).1) hd hds
  obtain ⟨u,hu⟩ := direction_exists hu
  obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨a,hab,had,hau,hpos⟩ := positive_state_support_point hD hp b₀ d₀ u
  exact strict_state_sequence_local_false hc hw x J K X hlabels A B D hD hA hB
    b' d' b₀ d₀ a u hb' hd' hbden hdden hu hab had hau hpos hL1
lemma strict_state_no_unit_support {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    {x : ℂ} {J K : Finset (Fin k)} {X : Fin k}
    (hlabels : ∀i, i∉J∪K ↔ i=X)
    {A B : Set ℝ} (hA : RealState hc x A J) (hB : RealState hc x B K)
    (hp : 0<volume A) {b d : ℝ}
    (hb : b∈(volume.restrict B).support) (hd : d∈(volume.restrict B).support) :
    ‖direction (b : Angles)-direction (d : Angles)‖≠1 := by
  intro hu
  apply strict_state_sequence_false hc hw (fun _ => x) J K X hlabels (fun _ => A) (fun _ => B)
    A hA.1 hp (fun _ => hA) (fun _ => hB) (fun _ => b) (fun _ => d) b d tendsto_const_nhds
    tendsto_const_nhds (fun _ => hb) (fun _ => hd) hu
  intro E _
  simp only [sub_self,norm_zero,integral_zero]
  exact tendsto_const_nhds
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma complex_unit_orthogonal {e v : ℂ} (he : ‖e‖=1) (hv : ‖v‖=1) (h : ⟪e,v⟫=0) :
    e=Complex.I*v ∨ e= -Complex.I*v := by
  have hr : (e*star v).re=0 := by
    rw [real_inner_comm,Complex.inner] at h
    exact h
  have hn : ‖e*star v‖=1 := by rw [norm_mul,norm_star,he,hv,one_mul]
  have hs : (e*star v).im^2=1 := by
    have hh := Complex.normSq_eq_norm_sq (e*star v)
    rw [hn] at hh
    simp only [Complex.normSq_apply,hr,zero_mul,zero_add,one_pow] at hh
    nlinarith
  have him : (e*star v).im=1 ∨ (e*star v).im= -1 := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs)
  have hmul : star v*v=1 := by
    change (starRingEnd ℂ) v*v=1
    rw [Complex.conj_mul']
    simp only [hv,one_pow,Complex.ofReal_one]
  rcases him with him|him
  · left
    have hz : e*star v=Complex.I := Complex.ext (by simpa using hr) (by simpa using him)
    calc e = (e*star v)*v := by rw [mul_assoc,hmul,mul_one]
         _ = Complex.I*v := congrArg (·*v) hz
  · right
    have hz : e*star v= -Complex.I := Complex.ext (by simpa using hr) (by simpa using him)
    calc e = (e*star v)*v := by rw [mul_assoc,hmul,mul_one]
         _ = -Complex.I*v := congrArg (·*v) hz
lemma ae_direction_nonorthogonal {v : ℂ} (hv : ‖v‖=1) :
    ∀ᵐt∂angularMeasure,⟪direction t,v⟫≠0 := by
  have hd : Function.Injective direction := fun _ _ h =>
    AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) (Subtype.ext h)
  have hf : {t | ⟪direction t,v⟫=0}.Finite := by
    apply ((Set.toFinite {Complex.I*v,-Complex.I*v}).preimage (f := direction) hd.injOn).subset
    intro t ht
    rcases complex_unit_orthogonal (direction_norm t) hv ht with ht|ht <;> simp [ht]
  exact measure_eq_zero_iff_ae_notMem.mp (hf.measure_zero angularMeasure)
end EuclideanFiveColor
end

end OAI
