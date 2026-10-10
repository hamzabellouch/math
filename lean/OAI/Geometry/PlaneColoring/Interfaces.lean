import OAI.Geometry.PlaneColoring.AngularBoundary

namespace OAI

noncomputable section
open Set
namespace EuclideanFiveColor
/-- The four cyclic edges, with outsider label `4`. This definition is local to
this interface argument and agrees extensionally with `fourEdge`. -/
def interfaceFourEdge (i : Fin 4) : Finset (Fin 5) :=
  if i=0 then {0,1} else if i=1 then {1,2} else if i=2 then {2,3} else {3,0}
def interfaceFourAllowed (s : Fin 4 → Bool) (b : Bool) : Finset (Fin 5) :=
  Finset.univ.filter fun j => ∀i, s i=b → j∉interfaceFourEdge i
def InterfaceFourCompatible (s : Fin 4 → Bool) (p : Finset (Fin 5)) : Prop :=
  p.Nonempty ∧ p.card≤2 ∧
    (p∩interfaceFourAllowed s true).Nonempty ∧ (p∩interfaceFourAllowed s false).Nonempty
def InterfaceFourSplit (s : Fin 4 → Bool) : Prop := s 0≠s 2 ∧ s 1≠s 3
def interfaceFourDiagonal (s : Fin 4 → Bool) : Fin 3 := if s 0=s 1 then 2 else 1
lemma interface_four_not_edge : ∀s : Fin 4 → Bool, ∀p : Finset (Fin 5),
    InterfaceFourCompatible s p → ∀i, ¬p⊆interfaceFourEdge i := by
  unfold InterfaceFourCompatible interfaceFourAllowed
  decide
lemma interface_four_split : ∀s : Fin 4 → Bool, ∀p : Finset (Fin 5),
    InterfaceFourCompatible s p → 4∉p → InterfaceFourSplit s ∧
      (if 4∈p then (0:Fin 3) else if 0∈p then 1 else 2)=interfaceFourDiagonal s := by
  unfold InterfaceFourCompatible InterfaceFourSplit interfaceFourAllowed interfaceFourDiagonal
  decide
lemma interface_four_split_neg (s : Fin 4 → Bool) :
    InterfaceFourSplit (fun i => !(s i)) ↔ InterfaceFourSplit s := by
  simp [InterfaceFourSplit]
lemma interface_four_diagonal_neg (s : Fin 4 → Bool) :
    interfaceFourDiagonal (fun i => !(s i))=interfaceFourDiagonal s := by
  simp [interfaceFourDiagonal]
lemma interface_four_diagonal_ne_zero (s : Fin 4 → Bool) : interfaceFourDiagonal s≠0 := by
  unfold interfaceFourDiagonal
  split <;> decide
lemma interface_four_split_no_opposite : ∀s : Fin 4 → Bool,
    InterfaceFourSplit s → ∀i,¬(s i=true ∧ s (i+2)=true) := by
  unfold InterfaceFourSplit
  decide
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def fourInterfaceSign (v : Fin 4 → ℂ) (t : Angles) (i : Fin 4) : Bool :=
  decide (0<⟪direction t,v i⟫)
lemma interfaceFourEdge_eq (i : Fin 4) : interfaceFourEdge i=fourEdge i := rfl
lemma fourInterfaceSign_opposite {v : Fin 4 → ℂ} {t : Angles}
    (hn : ∀i,⟪direction t,v i⟫≠0) :
    fourInterfaceSign v (t+(Real.pi : Angles))=fun i => !(fourInterfaceSign v t i) := by
  funext i
  simp only [fourInterfaceSign,direction_add_pi,inner_neg_left]
  by_cases hi : 0<⟪direction t,v i⟫
  · simp only [hi,show ¬0< -⟪direction t,v i⟫ by linarith,decide_true,decide_false,Bool.not_true]
  · have hneg : ⟪direction t,v i⟫<0 := lt_of_le_of_ne (le_of_not_gt hi) (hn i)
    simp only [hi,show 0< -⟪direction t,v i⟫ by linarith,decide_true,decide_false,Bool.not_false]
variable {c : ℂ → Fin 5} (hc : Measurable c)
lemma four_interface_compatible (hw : WeakColoring 5 c) {x : ℂ}
    {K : Fin 4 → Set ℂ} {v : Fin 4 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈fourEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    ∀ᵐt∂angularMeasure,InterfaceFourCompatible (fourInterfaceSign v t) (palette c hc x t) := by
  classical
  let E (s : Fin 4 → Bool) (b : Bool) : Finset (Fin 4) := Finset.univ.filter fun i => s i=b
  have hex := finite_support_exclusion_ae c hc K fourEdge hH
  have hJ (s : Fin 4 → Bool) (b : Bool) :
      ∀ᵐz : ℂ∂volume,(∀i∈E s b,z∈Straddle (K i)) → c z∈interfaceFourAllowed s b := by
    filter_upwards [hex] with z hz hzE
    simp only [interfaceFourAllowed,Finset.mem_filter,Finset.mem_univ,true_and]
    intro i hi
    exact hz i (hzE i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩))
  have hout (s : Fin 4 → Bool) := continuum_outer_restriction c hc (E s true) hK (hJ s true)
  have hin (s : Fin 4 → Bool) := continuum_inner_restriction c hc (E s false) hK (hJ s false)
  filter_upwards [ae_all_iff.mpr hout,ae_all_iff.mpr hin,palette_nonempty c hc x,
    palette_cardinality c hc hw x,ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i))]
    with t ho hi hp hcard hn
  refine ⟨hp,hcard.2,ho (fourInterfaceSign v t) ?_,hi (fourInterfaceSign v t) ?_⟩
  · intro i hi
    exact of_decide_eq_true (Finset.mem_filter.mp hi).2
  · intro i hi
    have hn' : ¬0<⟪direction t,v i⟫ := of_decide_eq_false (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (le_of_not_gt hn') (hn i)
lemma four_interface_admissible {x : ℂ} {v : Fin 4 → ℂ}
    (h : ∀ᵐt∂angularMeasure,InterfaceFourCompatible (fourInterfaceSign v t) (palette c hc x t)) :
    ∀ᵐt∂angularMeasure,FourAdmissible (palette c hc x t) := by
  filter_upwards [h] with t ht
  exact ⟨ht.1,ht.2.1,interface_four_not_edge _ _ ht⟩
lemma four_state_group_of_admissible {x : ℂ}
    (h : ∀ᵐt∂angularMeasure,FourAdmissible (palette c hc x t)) :
    ∀ᵐt∂angularMeasure,fourGroup (fourState c hc x t)⊆palette c hc x t :=
  h.mono fun _ ht => four_admissible_group _ ht
lemma four_state_represents_of_group {x : ℂ}
    (hg : ∀ᵐt∂angularMeasure,fourGroup (fourState c hc x t)⊆palette c hc x t)
    (s : Fin 3) :
    RealState hc x {t : ℝ | fourState c hc x (t : Angles)=s} (fourGroup s) := by
  refine ⟨measurableSet_eq_fun ((fourState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) measurable_const,?_⟩
  intro i hi
  filter_upwards [angleMk_quasiMeasurePreserving.ae hg] with t ht hts
  change fourState c hc x (t : Angles)=s at hts
  exact (mem_palette c hc x (t : Angles) i).mp (ht (by simpa only [hts] using hi))
lemma four_state_changes_of_group (hw : WeakColoring 5 c) {x : ℂ}
    (hg : ∀ᵐt∂angularMeasure,fourGroup (fourState c hc x t)⊆palette c hc x t) :
    ∀ᵐt∂angularMeasure,fourState c hc x t≠fourState c hc x (t+(sixty : Angles)) := by
  filter_upwards [hg,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hg,
    palette_sixty_disjoint c hc hw x] with t ht hu hd he
  obtain ⟨i,hi⟩ := fourGroup_nonempty (fourState c hc x t)
  exact Finset.disjoint_left.mp hd (ht hi) (hu (by simpa only [he] using hi))
lemma four_state_diagonal_positive_of_group (hw : WeakColoring 5 c) {x : ℂ}
    (hg : ∀ᵐt∂angularMeasure,fourGroup (fourState c hc x t)⊆palette c hc x t)
    (s : Fin 3) (hs : s≠0) : 0<angularMeasure {t | fourState c hc x t=s} := by
  by_contra! hn
  have hnot : ∀ᵐt∂angularMeasure,fourState c hc x t≠s :=
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
    filter_upwards [angleMk_quasiMeasurePreserving.ae hg,angleMk_quasiMeasurePreserving.ae hnot]
      with t ht htn htv
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
  filter_upwards [hnot,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hnot,
      four_state_changes_of_group hc hw hg] with t ht hu hne
  exact three_exclude_flip _ _ s hs ht hu hne
lemma four_interface_state_rule {x : ℂ} {v : Fin 4 → ℂ}
    (h : ∀ᵐt∂angularMeasure,InterfaceFourCompatible (fourInterfaceSign v t) (palette c hc x t)) :
    ∀ᵐt∂angularMeasure,fourState c hc x t≠0 →
      InterfaceFourSplit (fourInterfaceSign v t) ∧ fourState c hc x t=interfaceFourDiagonal (fourInterfaceSign v t) := by
  filter_upwards [h] with t ht hn
  have ho : 4∉palette c hc x t := by
    intro ho
    exact hn (by simp only [fourState,fourCanonical,ho,ite_true])
  exact interface_four_split _ _ ht ho
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma angle_state_preimage_positive {A : Set Angles} (hA : MeasurableSet A) (hp : 0<angularMeasure A) :
    0<volume (((↑) : ℝ → Angles) ⁻¹' A) := by
  by_contra! hn
  have hz := measure_eq_zero_iff_ae_notMem.mp (le_antisymm hn zero_le)
  have ha : ∀ᵐt∂angularMeasure,t∉A := ae_angular_of_ae_line hA.compl hz
  exact hp.ne' (measure_eq_zero_iff_ae_notMem.mpr ha)
/-- Every point of an angular essential support has a real essential-support lift.
The compact fundamental domain is used only to establish the support inclusion. -/
lemma angle_support_lift {A : Set Angles} (hA : MeasurableSet A) {t : Angles}
    (ht : t∈(angularMeasure.restrict A).support) :
    ∃b : ℝ,(b : Angles)=t ∧ b∈(volume.restrict (((↑) : ℝ → Angles) ⁻¹' A)).support := by
  let B : Set ℝ := ((↑) : ℝ → Angles) ⁻¹' A
  let S : Set ℝ := (volume.restrict B).support∩Icc 0 (2*Real.pi)
  let F : Set Angles := ((↑) : ℝ → Angles) '' S
  have hm : Continuous ((↑) : ℝ → Angles) := AddCircle.continuous_mk' _
  have hS : IsCompact S := isCompact_Icc.inter_left Measure.isClosed_support
  have hF : IsClosed F := (hS.image hm).isClosed
  have ha : ∀ᵐt∂((volume : Measure Angles).restrict A),t∈F := by
    rw [← (AddCircle.measurePreserving_mk (2*Real.pi) 0).map_eq,
      Measure.restrict_map hm.measurable hA]
    apply (ae_map_iff hm.measurable.aemeasurable hF.measurableSet).mpr
    have hs : ∀ᵐb∂((volume.restrict (Ioc 0 (0+2*Real.pi))).restrict B),b∈(volume.restrict B).support := by
      apply ae_mono (Measure.restrict_mono_measure Measure.restrict_le_self B)
      exact Measure.support_mem_ae
    have hi : ∀ᵐb∂((volume.restrict (Ioc 0 (0+2*Real.pi))).restrict B),b∈Ioc 0 (0+2*Real.pi) :=
      ae_restrict_of_ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hs,hi] with b hb hib
    exact ⟨b,⟨hb,hib.1.le,by simpa only [zero_add] using hib.2⟩,rfl⟩
  have ha' : ∀ᵐt∂(angularMeasure.restrict A),t∈F := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.restrict_smul] at ha
    exact (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (2*Real.pi)≠0)).mp ha
  obtain ⟨b,hb,hbt⟩ := Measure.support_subset_of_isClosed hF ha' ht
  exact ⟨b,hbt,hb.1⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma direction_inner_real (t : ℝ) (v : ℂ) :
    ⟪direction (t : Angles),v⟫=Real.cos t*v.re+Real.sin t*v.im := by
  rw [Complex.inner,direction_real,Circle.coe_exp,Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.add_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im]
  ring
lemma three_direction_moment (t : Angles) (v w : ℂ) :
    ⟪direction t,v⟫*⟪direction t,w⟫+
      ⟪direction (t+(sixty : Angles)),v⟫*⟪direction (t+(sixty : Angles)),w⟫+
      ⟪direction (t+2•(sixty : Angles)),v⟫*⟪direction (t+2•(sixty : Angles)),w⟫=
      (3/2:ℝ)*⟪v,w⟫ := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← AddCircle.coe_nsmul,← AddCircle.coe_add,← AddCircle.coe_add]
  simp only [direction_inner_real,nsmul_eq_mul,sixty,Real.cos_add,Real.sin_add,
    Real.cos_pi_div_three,Real.sin_pi_div_three]
  norm_num only [Nat.cast_ofNat]
  rw [show 2*(Real.pi/3)=Real.pi/3+Real.pi/3 by ring]
  simp only [Real.cos_add,Real.sin_add,Real.cos_pi_div_three,Real.sin_pi_div_three,
    Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  have hs : Real.sqrt 3^2=3 := Real.sq_sqrt (by norm_num)
  have hc := Real.sin_sq_add_cos_sq a
  ring_nf
  have hs3 : Real.sqrt 3^3=3*Real.sqrt 3 := by rw [pow_succ,hs]
  have hs4 : Real.sqrt 3^4=9 := by rw [show 4=2*2 from rfl,pow_mul,hs]; norm_num
  simp only [hs,hs3,hs4]
  linear_combination (3/2:ℝ)*(v.re*w.re+v.im*w.im)*hc
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma direction_sixty_unit (t : Angles) : ‖direction t-direction (t+(sixty : Angles))‖=1 := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← AddCircle.coe_add,direction_real,direction_real]
  have he : (Circle.exp a : ℂ)-(Circle.exp (a+sixty) : ℂ)=(Circle.exp (a-sixty) : ℂ) := by
    simp only [Circle.coe_exp,Complex.exp_ofReal_mul_I]
    apply Complex.ext <;> simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Real.cos_add,Real.cos_sub,Real.sin_add,Real.sin_sub,sixty,Real.cos_pi_div_three] <;> ring
  rw [he]
  exact Circle.norm_coe _
lemma compact_no_unit_margin {F : Set Angles} (hF : IsCompact F)
    (hu : ∀t∈F,∀u∈F,‖direction t-direction u‖≠1) :
    ∃ε : ℝ,0<ε ∧ ∀t∈F,∀u,dist t u<ε → u+(sixty : Angles)∉F ∧ u-(sixty : Angles)∉F := by
  let T : Set Angles := {u | u+(sixty : Angles)∉F ∧ u-(sixty : Angles)∉F}
  have ho : IsOpen T := (hF.isClosed.isOpen_compl.preimage (continuous_id.add_const _)).inter
    (hF.isClosed.isOpen_compl.preimage (continuous_id.sub continuous_const))
  have hs : F⊆T := by
    intro t ht
    refine ⟨fun hh => hu t ht _ hh (direction_sixty_unit t),fun hh => ?_⟩
    apply hu (t-(sixty : Angles)) hh t ht
    simpa only [sub_add_cancel] using direction_sixty_unit (t-(sixty : Angles))
  obtain ⟨ε,hε,hsub⟩ := hF.exists_thickening_subset_open ho hs
  exact ⟨ε,hε,fun t ht u htu => hsub (Metric.mem_thickening_iff.mpr ⟨t,ht,by simpa only [dist_comm] using htu⟩)⟩

variable {c : ℂ → Fin 5} (hc : Measurable c)
def interfaceStateSet (x : ℂ) (s : Fin 3) : Set Angles := {t | fourState c hc x t=s}
def interfaceStateSupport (x : ℂ) (s : Fin 3) : Set Angles :=
  (angularMeasure.restrict (interfaceStateSet hc x s)).support
lemma interfaceStateSet_measurable (x : ℂ) (s : Fin 3) : MeasurableSet (interfaceStateSet hc x s) :=
  measurableSet_eq_fun (fourState_measurable c hc x) measurable_const
lemma interfaceStateSupport_ae (x : ℂ) :
    ∀ᵐt∂angularMeasure,∀s : Fin 3,fourState c hc x t=s → t∈interfaceStateSupport hc x s := by
  apply ae_all_iff.mpr
  intro s
  exact (ae_restrict_iff' (interfaceStateSet_measurable hc x s)).mp Measure.support_mem_ae
lemma interfaceStateSupport_no_unit (hw : WeakColoring 5 c) {x : ℂ}
    (hg : ∀ᵐt∂angularMeasure,fourGroup (fourState c hc x t)⊆palette c hc x t)
    {s : Fin 3} (hs : s≠0) {t u : Angles}
    (ht : t∈interfaceStateSupport hc x s) (hu : u∈interfaceStateSupport hc x s) :
    ‖direction t-direction u‖≠1 := by
  let r : Fin 3 := if s=1 then 2 else 1
  have hr : r≠0 := by dsimp [r]; split <;> decide
  have hl : ∀i : Fin 5,i∉fourGroup r∪fourGroup s ↔ i=4 := by
    exact (show ∀s : Fin 3,s≠0 → ∀i : Fin 5,i∉fourGroup (if s=1 then 2 else 1)∪fourGroup s ↔ i=4 from by decide) s hs
  obtain ⟨b,rfl,hb⟩ := angle_support_lift (interfaceStateSet_measurable hc x s) ht
  obtain ⟨d,rfl,hd⟩ := angle_support_lift (interfaceStateSet_measurable hc x s) hu
  exact strict_state_no_unit_support hc hw hl (four_state_represents_of_group hc hg r)
    (four_state_represents_of_group hc hg s)
    (angle_state_preimage_positive (interfaceStateSet_measurable hc x r)
      (four_state_diagonal_positive_of_group hc hw hg r hr)) hb hd
lemma interfaceStateSupport_margin (hw : WeakColoring 5 c) {x : ℂ}
    (hg : ∀ᵐt∂angularMeasure,fourGroup (fourState c hc x t)⊆palette c hc x t) :
    ∃ε : ℝ,0<ε ∧ ∀s : Fin 3,s≠0 → ∀t∈interfaceStateSupport hc x s,∀u,dist t u<ε →
      u+(sixty : Angles)∉interfaceStateSupport hc x s ∧ u-(sixty : Angles)∉interfaceStateSupport hc x s := by
  have h (s : Fin 3) (hs : s≠0) := compact_no_unit_margin
    (show IsCompact (interfaceStateSupport hc x s) from Measure.isClosed_support.isCompact)
    (fun t ht u hu => interfaceStateSupport_no_unit hc hw hg hs ht hu)
  obtain ⟨ε₁,hε₁,h₁⟩ := h 1 (by decide)
  obtain ⟨ε₂,hε₂,h₂⟩ := h 2 (by decide)
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro s hs t ht u htu
  fin_cases s
  · exact (hs rfl).elim
  · exact h₁ t ht u (htu.trans_le (min_le_left _ _))
  · exact h₂ t ht u (htu.trans_le (min_le_right _ _))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma four_diagonal_product_neg {v : Fin 4 → ℂ} {t : Angles}
    (hn : ∀i,⟪direction t,v i⟫≠0) (hd : interfaceFourDiagonal (fourInterfaceSign v t)=1) :
    ⟪direction t,v 0⟫*⟪direction t,v 1⟫<0 := by
  by_cases h0 : 0<⟪direction t,v 0⟫ <;> by_cases h1 : 0<⟪direction t,v 1⟫
  · simp only [interfaceFourDiagonal,fourInterfaceSign,h0,h1] at hd
    norm_num at hd
  · exact mul_neg_of_pos_of_neg h0 (lt_of_le_of_ne (le_of_not_gt h1) (hn 1))
  · exact mul_neg_of_neg_of_pos (lt_of_le_of_ne (le_of_not_gt h0) (hn 0)) h1
  · simp only [interfaceFourDiagonal,fourInterfaceSign,h0,h1] at hd
    norm_num at hd
lemma four_diagonal_product_pos {v : Fin 4 → ℂ} {t : Angles}
    (hn : ∀i,⟪direction t,v i⟫≠0) (hd : interfaceFourDiagonal (fourInterfaceSign v t)=2) :
    0<⟪direction t,v 0⟫*⟪direction t,v 1⟫ := by
  by_cases h0 : 0<⟪direction t,v 0⟫ <;> by_cases h1 : 0<⟪direction t,v 1⟫
  · exact mul_pos h0 h1
  · simp only [interfaceFourDiagonal,fourInterfaceSign,h0,h1,decide_true,decide_false] at hd
    norm_num at hd
  · simp only [interfaceFourDiagonal,fourInterfaceSign,h0,h1,decide_true,decide_false] at hd
    norm_num at hd
  · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (le_of_not_gt h0) (hn 0))
      (lt_of_le_of_ne (le_of_not_gt h1) (hn 1))
lemma four_diagonal_orbit_half {v : Fin 4 → ℂ} {t : Angles} {j : Fin 6}
    (hn : ∀i,⟪direction (t+sixAngle j),v i⟫≠0) :
    interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle (j+3)))=
      interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j)) := by
  rw [sixAngle_half,← add_assoc,fourInterfaceSign_opposite hn,interface_four_diagonal_neg]
lemma four_diagonal_uniform_of_parity {v : Fin 4 → ℂ} {t : Angles} {a : Fin 3} {p : Fin 2}
    (hn : ∀j i,⟪direction (t+sixAngle j),v i⟫≠0)
    (hd : ∀j : Fin 6,j.val%2≠p.val → interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))=a) :
    ∀j : Fin 6,interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))=a := by
  intro j
  by_cases hj : j.val%2≠p.val
  · exact hd j hj
  have hh : (j+3).val%2≠p.val := by
    have h : ∀p : Fin 2,∀j : Fin 6,¬j.val%2≠p.val → (j+3).val%2≠p.val := by decide
    exact h p j hj
  rw [← four_diagonal_orbit_half (hn j)]
  exact hd (j+3) hh
lemma four_uniform_diagonal_one {v : Fin 4 → ℂ} {t : Angles}
    (hn : ∀j i,⟪direction (t+sixAngle j),v i⟫≠0)
    (hd : ∀j : Fin 6,interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))=1) :
    ⟪v 0,v 1⟫<0 := by
  have h0 := four_diagonal_product_neg (hn 0) (hd 0)
  have h1 := four_diagonal_product_neg (hn 1) (hd 1)
  have h2 := four_diagonal_product_neg (hn 2) (hd 2)
  norm_num only [sixAngle,Fin.val_zero,Fin.val_one,Fin.val_two,zero_nsmul,one_nsmul,add_zero] at h0 h1 h2
  have hm := three_direction_moment t (v 0) (v 1)
  linarith
lemma four_uniform_diagonal_two {v : Fin 4 → ℂ} {t : Angles}
    (hn : ∀j i,⟪direction (t+sixAngle j),v i⟫≠0)
    (hd : ∀j : Fin 6,interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))=2) :
    0<⟪v 0,v 1⟫ := by
  have h0 := four_diagonal_product_pos (hn 0) (hd 0)
  have h1 := four_diagonal_product_pos (hn 1) (hd 1)
  have h2 := four_diagonal_product_pos (hn 2) (hd 2)
  norm_num only [sixAngle,Fin.val_zero,Fin.val_one,Fin.val_two,zero_nsmul,one_nsmul,add_zero] at h0 h1 h2
  have hm := three_direction_moment t (v 0) (v 1)
  linarith
/-- The three-direction quadratic moment replaces the source's projective arc
length argument. No assumption about antipodal ray pairs or the collinear case
is required: two opposite uniform diagonal triples are already contradictory. -/
lemma four_opposite_uniform_diagonals_false {v : Fin 4 → ℂ} {t u : Angles}
    (hnt : ∀j i,⟪direction (t+sixAngle j),v i⟫≠0)
    (hnu : ∀j i,⟪direction (u+sixAngle j),v i⟫≠0)
    {a b : Fin 3} (ha : a≠0) (hb : b≠0) (hab : a≠b)
    (hdt : ∀j : Fin 6,interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))=a)
    (hdu : ∀j : Fin 6,interfaceFourDiagonal (fourInterfaceSign v (u+sixAngle j))=b) : False := by
  have hab' : (a=1 ∧ b=2) ∨ (a=2 ∧ b=1) :=
    (show ∀a b : Fin 3,a≠0 → b≠0 → a≠b → (a=1 ∧ b=2) ∨ (a=2 ∧ b=1) from by decide) a b ha hb hab
  rcases hab' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact (four_uniform_diagonal_one hnt hdt).not_gt (four_uniform_diagonal_two hnu hdu)
  · exact (four_uniform_diagonal_one hnu hdu).not_gt (four_uniform_diagonal_two hnt hdt)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma sixAngle_prev (j : Fin 6) : sixAngle (j-1)=sixAngle j-(sixty : Angles) := by
  have h := sixAngle_step (j-1)
  simpa only [sub_add_cancel] using eq_sub_iff_add_eq.mpr h.symm
variable {c : ℂ → Fin 5} (hc : Measurable c)
def fourInterfaceWord (x : ℂ) (t : Angles) (j : Fin 6) : Fin 3 :=
  fourState c hc x (t+sixAngle j)
lemma fourInterfaceWord_shift (x : ℂ) (t : Angles) (j : Fin 6) :
    fourInterfaceWord hc x (t+(sixty : Angles)) j=fourInterfaceWord hc x t (j+1) := by
  simp only [fourInterfaceWord,sixAngle_step]
  congr 1
  abel
/-- Construction of the dense conull shift-invariant set and its actual
six-position words, from the previously established genuine state system. -/
lemma four_interface_word_data (hw : WeakColoring 5 c) {x : ℂ} {v : Fin 4 → ℂ}
    (hv : ∀i,‖v i‖=1)
    (hcompat : ∀ᵐt∂angularMeasure,InterfaceFourCompatible (fourInterfaceSign v t) (palette c hc x t)) :
    ∃G : Set Angles,Dense G ∧ (∀t∈G,t+(sixty : Angles)∈G) ∧
      (∀t∈G,∀j i,⟪direction (t+sixAngle j),v i⟫≠0) ∧
      (∀t∈G,∀j,fourInterfaceWord hc x t j≠0 → fourInterfaceWord hc x t j=
        interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j))) ∧
      (∀t∈G,FourWordValid (fourInterfaceWord hc x t)) ∧
      ∃ε : ℝ,0<ε ∧ ∀t∈G,∀u∈G,dist t u<ε →
        FourWordCross (fourInterfaceWord hc x t) (fourInterfaceWord hc x u) := by
  have hg := four_state_group_of_admissible hc (four_interface_admissible hc hcompat)
  obtain ⟨ε,hε,hmargin⟩ := interfaceStateSupport_margin hc hw hg
  let Q (t : Angles) : Prop := (∀i,⟪direction t,v i⟫≠0) ∧
    (fourState c hc x t≠0 → fourState c hc x t=interfaceFourDiagonal (fourInterfaceSign v t)) ∧
    fourState c hc x t≠fourState c hc x (t+(sixty : Angles)) ∧
    ∀s : Fin 3,fourState c hc x t=s → t∈interfaceStateSupport hc x s
  have hQ : ∀ᵐt∂angularMeasure,Q t := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i)),
      four_interface_state_rule hc hcompat,four_state_changes_of_group hc hw hg,
      interfaceStateSupport_ae hc x] with t hn hr hs hF
    exact ⟨hn,fun h => (hr h).2,hs,hF⟩
  let G : Set Angles := {t | ∀j : Fin 6,Q (t+sixAngle j)}
  have hGae : ∀ᵐt∂angularMeasure,t∈G := ae_all_iff.mpr fun j =>
    (measurePreserving_add_right angularMeasure (sixAngle j)).quasiMeasurePreserving.ae hQ
  have hGshift : ∀t∈G,t+(sixty : Angles)∈G := by
    intro t ht j
    have he : t+(sixty : Angles)+sixAngle j=t+sixAngle (j+1) := by
      rw [sixAngle_step]
      abel
    rw [he]
    exact ht (j+1)
  refine ⟨G,Measure.dense_of_ae hGae,hGshift,fun t ht j => (ht j).1,fun t ht j => (ht j).2.1,?_,ε,hε,?_⟩
  · intro t ht
    refine ⟨?_,?_⟩
    · intro j
      simpa only [fourInterfaceWord,sixAngle_step,← add_assoc] using (ht j).2.2.1
    · intro j hj hj3
      dsimp only [fourInterfaceWord]
      rw [(ht (j+3)).2.1 hj3,(ht j).2.1 hj]
      exact four_diagonal_orbit_half (ht j).1
  · intro t ht u hu htu j hj
    have hm := hmargin (fourInterfaceWord hc x t j) hj (t+sixAngle j)
      ((ht j).2.2.2 _ rfl) (u+sixAngle j) (by simpa only [dist_add_right] using htu)
    constructor
    · intro he
      apply hm.1
      have hh := (hu (j+1)).2.2.2 _ he
      simpa only [sixAngle_step,← add_assoc] using hh
    · intro he
      apply hm.2
      have hh := (hu (j-1)).2.2.2 _ he
      simpa only [sixAngle_prev,add_sub_assoc] using hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma four_word_opposite_geometry_false {v : Fin 4 → ℂ} {t u : Angles}
    {w z : Fin 6 → Fin 3} (hw : FourWordValid w) (hz : FourWordValid z)
    (hzero : ∀j,w j=0 → j.val%2=0) (hzero' : ∀j,z j=0 → j.val%2=1)
    (hcross : FourWordCross w z)
    (hnt : ∀j i,⟪direction (t+sixAngle j),v i⟫≠0)
    (hnu : ∀j i,⟪direction (u+sixAngle j),v i⟫≠0)
    (hdt : ∀j,w j≠0 → w j=interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j)))
    (hdu : ∀j,z j≠0 → z j=interfaceFourDiagonal (fourInterfaceSign v (u+sixAngle j))) : False := by
  obtain ⟨a,b,ha,hb,hab,hwa,hzb⟩ := four_word_opposite_parity w hw hzero z hz hzero' hcross
  apply four_opposite_uniform_diagonals_false hnt hnu ha hb hab
  · apply four_diagonal_uniform_of_parity (p:=0) hnt
    intro j hj
    have hh := hwa j (by norm_num only [Fin.val_zero] at hj; omega)
    exact (hdt j (fun h => ha (hh.symm.trans h))).symm.trans hh
  · apply four_diagonal_uniform_of_parity (p:=1) hnu
    intro j hj
    have hh := hzb j (by norm_num only [Fin.val_one] at hj; omega)
    exact (hdu j (fun h => hb (hh.symm.trans h))).symm.trans hh

lemma no_four_word_geometry (v : Fin 4 → ℂ) (G : Set Angles) (hG : Dense G)
    (w : Angles → Fin 6 → Fin 3) (hw : ∀t∈G,FourWordValid (w t))
    (hshiftG : ∀t∈G,t+(sixty : Angles)∈G)
    (hshift : ∀t∈G,∀j,w (t+(sixty : Angles)) j=w t (j+1))
    (hn : ∀t∈G,∀j i,⟪direction (t+sixAngle j),v i⟫≠0)
    (hd : ∀t∈G,∀j,w t j≠0 → w t j=interfaceFourDiagonal (fourInterfaceSign v (t+sixAngle j)))
    {ε : ℝ} (hε : 0<ε)
    (hcross : ∀t∈G,∀u∈G,dist t u<ε → FourWordCross (w t) (w u)) : False := by
  classical
  have hnomix := four_words_no_mixed G hG w hw hshiftG hshift hε hcross
  have hpar (t : Angles) (ht : t∈G) := four_word_parity (w t) (hw t ht) (hnomix t ht)
  let p : Angles → Fin 2 := fun t => if ht : t∈G then (hpar t ht).choose else 0
  have hp (t : Angles) (ht : t∈G) : ∀j,w t j=0 → j.val%2=(p t).val := by
    simpa only [p,dite_eq_left ht] using (hpar t ht).choose_spec
  have hclose (t : Angles) (ht : t∈G) (u : Angles) (hu : u∈G) (htu : dist t u<ε) : p t=p u := by
    by_contra hne
    have hcases : (p t=0 ∧ p u=1) ∨ (p t=1 ∧ p u=0) :=
      (show ∀a b : Fin 2,a≠b → (a=0 ∧ b=1) ∨ (a=1 ∧ b=0) from by decide) _ _ hne
    rcases hcases with ⟨hpt,hpu⟩|⟨hpt,hpu⟩
    · exact four_word_opposite_geometry_false (hw t ht) (hw u hu)
        (by simpa only [hpt,Fin.val_zero] using hp t ht)
        (by simpa only [hpu,Fin.val_one] using hp u hu)
        (hcross t ht u hu htu) (hn t ht) (hn u hu) (hd t ht) (hd u hu)
    · exact four_word_opposite_geometry_false (hw u hu) (hw t ht)
        (by simpa only [hpu,Fin.val_zero] using hp u hu)
        (by simpa only [hpt,Fin.val_one] using hp t ht)
        (hcross u hu t ht (by simpa only [dist_comm] using htu))
        (hn u hu) (hn t ht) (hd u hu) (hd t ht)
  obtain ⟨t,ht⟩ := hG.nonempty
  have hconst : ∀u∈G,p u=p t := by
    apply dense_isolated_value_constant hG p hε ⟨t,ht,rfl⟩
    intro u hu hut z hz huz
    exact (hclose u hu z hz huz).symm.trans hut
  obtain ⟨j,hj⟩ := four_word_has_outsider (w (t+(sixty : Angles))) (hw _ (hshiftG t ht))
  have hh := four_word_shift_parity (w t) (p t) (hp t ht) j
    (by simpa only [hshift t ht j] using hj)
  have hh' := hp _ (hshiftG t ht) j hj
  rw [hconst _ (hshiftG t ht)] at hh'
  have he : (p t).val=(p t+1).val := hh'.symm.trans hh
  exact (show ∀a : Fin 2,a.val≠(a+1).val from by decide) (p t) he

/-- The actual length-four interface cycle is impossible. All hypotheses are
exactly approach directions and common straddling exclusion of both endpoints. -/
lemma no_four_interfaces {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 4 → Set ℂ} {v : Fin 4 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈fourEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) : False := by
  obtain ⟨G,hG,hshiftG,hn,hd,hw',ε,hε,hcross⟩ := four_interface_word_data hc hw hv
    (four_interface_compatible hc hw hv hK hH)
  exact no_four_word_geometry v G hG (fourInterfaceWord hc x) hw' hshiftG
    (fun t _ j => fourInterfaceWord_shift hc x t j) hn hd hε hcross
end EuclideanFiveColor
end

end OAI
