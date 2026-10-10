import OAI.Geometry.PlaneColoring.Accumulation

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_neighbor_real (hw : WeakColoring k c) (x : ℂ) (a : ℝ) (i : Fin k) :
    ∀ᵐt : ℝ∂volume,t∈liftPalette c hc (x+direction (a : Angles)) i → t∉liftPalette c hc x i := by
  let U : Set ℝ := {t | Real.sin (a-t)≠0}
  have hU : IsOpen U := isOpen_ne_fun (Real.continuous_sin.comp (continuous_const.sub continuous_id)) continuous_const
  have hu : ∀ᵐt : ℝ∂volume,t∈U := by
    filter_upwards [ae_sin_sub_ne_zero a] with t ht
    change Real.sin (a-t)≠0
    rwa [← neg_sub t a,Real.sin_neg,neg_ne_zero]
  have hh := palette_smooth_transport c hc hw (x := x) (z := x+direction (a : Angles)) hU (s := id) (t := fun _ => a)
    (ds := fun _ => 1) (dt := fun _ => 0) (fun t _ => hasDerivAt_id t)
    (fun t _ => hasDerivAt_const t a) (fun _ _ => one_ne_zero) (fun _ ht => ht) (fun t _ => ?_) i
  · exact (ae_restrict_iff' hU.measurableSet).mp hh |>.mp (hu.mono fun t ht hi => hi ht)
  · simp only [circleTarget,samplingParameter,add_sub_cancel_left,direction_realPlane,circleSum,one_smul,one_mul,id_eq]
    exact Prod.ext (add_comm _ _) (add_comm _ _)
lemma palette_neighbor_disjoint (hw : WeakColoring k c) (x : ℂ) (a : ℝ) :
    ∀ᵐt∂angularMeasure,Disjoint (palette c hc (x+direction (a : Angles)) t) (palette c hc x t) := by
  have hp (i : Fin k) : ∀ᵐt∂angularMeasure,t∈paletteSet c hc (x+direction (a : Angles)) i → t∉paletteSet c hc x i := by
    apply ae_angular_of_ae_line
    · simpa only [imp_iff_not_or,Set.compl_def,Set.union_def,Set.mem_ofPred_eq] using
        (paletteSet_measurable c hc (x+direction (a : Angles)) i).compl.union (paletteSet_measurable c hc x i).compl
    · exact palette_neighbor_real c hc hw x a i
  filter_upwards [ae_all_iff.mpr hp] with t ht
  exact Finset.disjoint_left.mpr fun i hi hj => ht i ((mem_palette c hc _ t i).mp hi) ((mem_palette c hc _ t i).mp hj)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
def stateSupport (f : ℝ → ι) (i : ι) : Set ℝ := (volume.restrict {t | f t=i}).support
lemma ae_mem_stateSupport {f : ℝ → ι} (hf : Measurable f) (i : ι) :
    ∀ᵐt : ℝ∂volume,f t=i → t∈stateSupport f i :=
  (ae_restrict_iff' (measurableSet_eq_fun hf measurable_const)).mp
    (volume.restrict {t | f t=i}).support_mem_ae
lemma ae_state_support {f : ℝ → ι} (hf : Measurable f) :
    ∀ᵐt : ℝ∂volume,t∈stateSupport f (f t) := by
  have h : ∀ᵐt : ℝ∂volume,∀i : ι,f t=i → t∈stateSupport f i :=
    ae_all_iff.mpr (fun i => ae_mem_stateSupport hf i)
  exact h.mono fun t ht => ht (f t) rfl
lemma stateSupport_cover {f : ℝ → ι} (hf : Measurable f) (a : ℝ) : ∃i,a∈stateSupport f i := by
  have hclosed : IsClosed (⋃i,stateSupport f i)  := isClosed_iUnion_of_finite fun _ => Measure.isClosed_support
  have hae : ∀ᵐt : ℝ∂volume,t∈⋃i,stateSupport f i :=
    (ae_state_support hf).mono fun t ht => mem_iUnion.mpr ⟨f t,ht⟩
  have hd := Measure.dense_of_ae hae
  exact mem_iUnion.mp ((hclosed.closure_eq ▸ hd a) : a∈⋃i,stateSupport f i)
lemma stateSupport_shift_relation {f : ℝ → ι} (hf : Measurable f) {R : ι → ι → Prop}
    {d : ℝ} (hR : ∀ᵐt : ℝ∂volume,R (f t) (f (t+d))) {i : ι} {a : ℝ}
    (ha : a∈stateSupport f i) : ∃j,R i j ∧ a+d∈stateSupport f j := by
  classical
  let K : Set ℝ := ⋃j∈({j | R i j} : Set ι),(fun t => t+d)⁻¹'stateSupport f j
  have hK : IsClosed K := (Set.toFinite _).isClosed_biUnion (fun j _ =>
    Measure.isClosed_support.preimage (continuous_id.add continuous_const))
  have hm : ∀ᵐt : ℝ∂volume,f t=i → t∈K := by
    filter_upwards [hR,(measurePreserving_add_right (volume : Measure ℝ) d).quasiMeasurePreserving.ae (ae_state_support hf)] with t hR ht hti
    exact mem_iUnion.mpr ⟨f (t+d),mem_iUnion.mpr ⟨hti ▸ hR,ht⟩⟩
  have hk : a∈K := Measure.support_subset_of_isClosed hK
    ((ae_restrict_iff' (hf (measurableSet_singleton i))).mpr hm) ha
  rcases mem_iUnion.mp hk with ⟨j,hj⟩
  obtain ⟨hr,hs⟩ := mem_iUnion.mp hj
  exact ⟨j,hr,hs⟩
omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
lemma stateSupport_nonempty_measure {f : ℝ → ι} {i : ι} {a : ℝ}
    (ha : a∈stateSupport f i) : 0<volume {t | f t=i} := by
  have h := (Measure.mem_support_iff_forall a).mp ha univ (univ_mem)
  simpa only [Measure.restrict_apply_univ] using h
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fiveRealState (x : ℂ) (i : Fin 5) : Set ℝ := {t | fiveState c hc x (t : Angles)=i}
def fiveSupport (x : ℂ) (i : Fin 5) : Set ℝ := (volume.restrict (fiveRealState c hc x i)).support
lemma five_realState_measurable (x : ℂ) (i : Fin 5) : MeasurableSet (fiveRealState c hc x i) :=
  measurableSet_eq_fun ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) measurable_const
lemma five_support_trace (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (ha : a∈fiveSupport c hc x i) :
    ∃b : TraceVector 5,IsTrace c hc (x+direction (a : Angles)) b ∧ ∀j∈fiveDiag i,traceValue b j=0 :=
  state_support_avoiding_trace c hc hw (fiveState_represents c hc hw hx i) ha
lemma five_support_step_ban (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i j : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hj : a∈fiveSupport c hc x j) (hij : fiveAdj i j) :
    ∀ᵐt∂angularMeasure,¬(fiveState c hc x t=i ∧ fiveState c hc x (t+(sixty : Angles))=j) ∧
      ¬(fiveState c hc x t=j ∧ fiveState c hc x (t+(sixty : Angles))=i) := by
  obtain ⟨bi,hbi,hzi⟩ := five_support_trace c hc hw hx hi
  obtain ⟨bj,hbj,hzj⟩ := five_support_trace c hc hw hx hj
  obtain ⟨X,hX⟩ := five_adj_four i j hij
  have hji : fiveAdj j i := hij.symm
  have hv : ∀ᵐt∂angularMeasure,fiveState c hc x t=i ∨ fiveState c hc x t=j →
      X∈palette c hc (x+direction (a : Angles)) t := by
    filter_upwards [avoiding_trace_palette c hc hbi hzi,avoiding_trace_palette c hc hbj hzj,
      palette_neighbor_disjoint c hc hw x a,fiveState_diag c hc hw hx] with t hni hnj hd he hs
    rw [he] at hd
    rcases hs with hi|hj
    · rw [hi] at hd
      exact five_forced_label i j X hij hX _ hd hnj
    · rw [hj] at hd
      exact five_forced_label j i X hji (by simpa only [Finset.union_comm] using hX) _ hd hni
  filter_upwards [hv,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hv,
    palette_sixty_disjoint c hc hw (x+direction (a : Angles))] with t ht hu hd
  constructor
  · rintro ⟨hi,hj⟩
    exact Finset.disjoint_left.mp hd (ht (Or.inl hi)) (hu (Or.inr hj))
  · rintro ⟨hj,hi⟩
    exact Finset.disjoint_left.mp hd (ht (Or.inr hj)) (hu (Or.inl hi))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_support_cover (x : ℂ) (a : ℝ) : ∃i,a∈fiveSupport c hc x i :=
  stateSupport_cover ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) a
lemma five_support_next (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) : ∃j,fiveAdj i j ∧ a+sixty∈fiveSupport c hc x j := by
  apply stateSupport_shift_relation ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) _ hi
  simpa only [Function.comp_def,AddCircle.coe_add] using angleMk_quasiMeasurePreserving.ae (fiveState_adj c hc hw hx)
lemma five_support_prev (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) : ∃j,fiveAdj i j ∧ a-sixty∈fiveSupport c hc x j := by
  apply stateSupport_shift_relation ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) (d := -sixty) _ hi
  have hh := angleMk_quasiMeasurePreserving.ae (fiveState_adj c hc hw hx)
  have hh' := (measurePreserving_add_right (volume : Measure ℝ) (-sixty)).quasiMeasurePreserving.ae hh
  filter_upwards [hh'] with t ht
  have he : ((t+-sixty : ℝ) : Angles)+(sixty : Angles)=(t : Angles) := by
    rw [← AddCircle.coe_add,neg_add_cancel_right]
  rw [he] at ht
  exact ht.symm
lemma five_support_no_sixty (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) : a+sixty∉fiveSupport c hc x i := by
  obtain ⟨j,hj,hsj⟩ := five_support_next c hc hw hx hi
  obtain ⟨X,hX⟩ := five_adj_four j i hj.symm
  have hp : 0<volume (fiveRealState c hc x j) := stateSupport_nonempty_measure hsj
  intro hs
  exact strict_state_no_unit_support hc hw hX (fiveState_represents c hc hw hx j)
    (fiveState_represents c hc hw hx i) hp hi hs (direction_sixty_unit_real a)
end EuclideanFiveColor
end

noncomputable section
namespace EuclideanFiveColor.FiveComb
-- Independent finite arithmetic facts; the source labels are Z/5Z, represented by Fin 5.
def Adj (i j : Fin 5) : Prop := i+1=j ∨ j+1=i
instance (i j : Fin 5) : Decidable (Adj i j) := inferInstanceAs (Decidable (_∨_))
lemma contact_neighbors : ∀i : Fin 5,∀L : Finset (Fin 5), i∉L → i+1∉L →
    (∃j∈L,Adj i j) → (∃j∈L,Adj (i+1) j) → i-1∈L ∧ i+2∈L := by decide
lemma opposite_contacts : ∀i j : Fin 5, Disjoint ({i-1,i+2} : Finset (Fin 5)) {j-1,j+2} →
    j=i+1 ∨ j+1=i := by decide
lemma adjacent_oriented : ∀I : Finset (Fin 5), (∃i∈I,∃j∈I,Adj i j) → ∃i,i∈I ∧ i+1∈I := by decide
lemma neighbors : ∀i j : Fin 5, Adj i j → j=i-1 ∨ j=i+1 := by decide
lemma two_bans : ∀i j : Fin 5, j=i+1 ∨ j+1=i → ∃s,
    (s=i ∨ s=i+1) ∧ (s=j ∨ s=j+1) ∧
    ∀t,Adj s t → ((s=i ∧ t=i+1) ∨ (s=i+1 ∧ t=i)) ∨ ((s=j ∧ t=j+1) ∨ (s=j+1 ∧ t=j)) := by decide
end EuclideanFiveColor.FiveComb
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fiveSupportList (x : ℂ) (a : ℝ) : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter (fun i => a∈fiveSupport c hc x i)
@[simp] lemma mem_fiveSupportList (x : ℂ) (a : ℝ) (i : Fin 5) :
    i∈fiveSupportList c hc x a ↔ a∈fiveSupport c hc x i := by simp only [fiveSupportList,Finset.mem_filter,Finset.mem_univ,true_and]
lemma five_contact_next (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hi' : a∈fiveSupport c hc x (i+1)) :
    i-1∈fiveSupportList c hc x (a+sixty) ∧ i+2∈fiveSupportList c hc x (a+sixty) := by
  apply FiveComb.contact_neighbors
  · exact fun h => five_support_no_sixty c hc hw hx hi ((mem_fiveSupportList _ _ _ _ _).mp h)
  · exact fun h => five_support_no_sixty c hc hw hx hi' ((mem_fiveSupportList _ _ _ _ _).mp h)
  · obtain ⟨j,hj,hs⟩ := five_support_next c hc hw hx hi
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
  · obtain ⟨j,hj,hs⟩ := five_support_next c hc hw hx hi'
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
lemma five_contact_prev (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {i : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hi' : a∈fiveSupport c hc x (i+1)) :
    i-1∈fiveSupportList c hc x (a-sixty) ∧ i+2∈fiveSupportList c hc x (a-sixty) := by
  apply FiveComb.contact_neighbors
  · intro h
    have hh := five_support_no_sixty c hc hw hx ((mem_fiveSupportList _ _ _ _ _).mp h)
    exact hh (by simpa only [sub_add_cancel] using hi)
  · intro h
    have hh := five_support_no_sixty c hc hw hx ((mem_fiveSupportList _ _ _ _ _).mp h)
    exact hh (by simpa only [sub_add_cancel] using hi')
  · obtain ⟨j,hj,hs⟩ := five_support_prev c hc hw hx hi
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
  · obtain ⟨j,hj,hs⟩ := five_support_prev c hc hw hx hi'
    exact ⟨j,(mem_fiveSupportList _ _ _ _ _).mpr hs,hj⟩
lemma five_opposite_contacts_false (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x)
    {a b : ℝ} (hab : b=a+3*sixty) {i j : Fin 5}
    (hi : a∈fiveSupport c hc x i) (hi' : a∈fiveSupport c hc x (i+1))
    (hj : b∈fiveSupport c hc x j) (hj' : b∈fiveSupport c hc x (j+1)) : False := by
  have hn := five_contact_next c hc hw hx hi hi'
  have hp := five_contact_prev c hc hw hx hj hj'
  have hdis : Disjoint ({i-1,i+2} : Finset (Fin 5)) {j-1,j+2} := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hiK : a+sixty∈fiveSupport c hc x k := by
      apply (mem_fiveSupportList _ _ _ _ _).mp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl|rfl <;> tauto
    have hjK : b-sixty∈fiveSupport c hc x k := by
      apply (mem_fiveSupportList _ _ _ _ _).mp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hl
      rcases hl with rfl|rfl <;> tauto
    exact five_support_no_sixty c hc hw hx hiK (by convert hjK using 1; rw [hab]; ring)
  have hji := FiveComb.opposite_contacts i j hdis
  obtain ⟨s,hs,_hst,hban⟩ := FiveComb.two_bans i j hji
  have hss : a∈fiveSupport c hc x s := by rcases hs with rfl|rfl <;> assumption
  have hbanI := five_support_step_ban c hc hw hx hi hi' (Or.inl rfl)
  have hbanJ := five_support_step_ban c hc hw hx hj hj' (Or.inl rfl)
  have hnot : ∀ᵐt∂angularMeasure,fiveState c hc x t≠s := by
    filter_upwards [hbanI,hbanJ,fiveState_adj c hc hw hx] with t hbI hbJ ha he
    rw [he] at ha
    rcases hban _ ha with h|h
    · rcases h with ⟨rfl,ht⟩|⟨rfl,ht⟩
      · exact hbI.1 ⟨he,ht⟩
      · exact hbI.2 ⟨he,ht⟩
    · rcases h with ⟨rfl,ht⟩|⟨rfl,ht⟩
      · exact hbJ.1 ⟨he,ht⟩
      · exact hbJ.2 ⟨he,ht⟩
  have hz : volume (fiveRealState c hc x s)=0 := measure_eq_zero_iff_ae_notMem.mpr (angleMk_quasiMeasurePreserving.ae hnot)
  exact (stateSupport_nonempty_measure hss).ne' hz
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
open scoped NNReal ENNReal
lemma plane_lipschitz_image_null {F : RealPlane → RealPlane} {K : ℝ≥0}
    (hf : LipschitzWith K F) {A : Set RealPlane} (ha : volume A=0) : volume (F '' A)=0 := by
  have h := hf.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2) A
  rw [hausdorffMeasure_prod_real,ha,mul_zero] at h
  exact bot_unique h
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma palette_open_exclusion (hw : WeakColoring k c) {x : ℂ} {i : Fin k} {a b : ℝ}
    (hab : Real.sin (b-a)≠0) {V : Set ℝ} (hV : IsOpen V) (ha : a∈V)
    (hpal : ∀ᵐt : ℝ∂volume,t∈V → (t : Angles)∈paletteSet c hc x i) :
    ∃U : Set ℂ, IsOpen U ∧ x+direction (a : Angles)+direction (b : Angles)∈U ∧
      volume (U∩{z | c z=i})=0 := by
  let e := circleInverseHomeo hab
  let W : Set RealPlane := e.source ∩ Prod.fst ⁻¹' V
  have hW : IsOpen W := e.open_source.inter (hV.preimage continuous_fst)
  have haW : (a,b)∈W := by
    refine ⟨?_,ha⟩
    exact (show HasStrictFDerivAt (circleSum 1)
      (circleSumDerivEquiv (r := 1) (p := (a,b)) (by simpa using hab) : RealPlane →L[ℝ] RealPlane)
      (a,b) from circleSum_strict 1 (a,b)).mem_toOpenPartialHomeomorph_source
  have hO : IsOpen (circleSum 1 '' W) := e.isOpen_image_of_subset_source hW inter_subset_left
  let g : RealPlane → ℂ := fun q => x+Complex.equivRealProdCLM.symm q
  have hgs (q : RealPlane) : g (circleSum 1 q)=angularSum x 1 (angleChart q) := by
    rw [angularSum_chart]
    simp only [g,map_add,ContinuousLinearEquiv.symm_apply_apply]
  have hgc : IsOpenMap g := (Homeomorph.addLeft x).isOpenMap.comp Complex.equivRealProdCLM.symm.toHomeomorph.isOpenMap
  have hex := anglePair_quasiMeasurePreserving.ae (palette_first_exclusion c hc hw x i)
  have hp : ∀ᵐq : RealPlane∂volume,q.1∈V → (q.1 : Angles)∈paletteSet c hc x i :=
    Measure.quasiMeasurePreserving_fst.ae hpal
  have hnull : volume (W∩{q | c (g (circleSum 1 q))=i})=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hex,hp] with q hq hp hmem
    apply hq (hp hmem.1.2)
    change c (angularSum x 1 (angleChart q))=i
    rw [← hgs]
    exact hmem.2
  have himage := plane_lipschitz_image_null circleSum_one_lipschitz_sumTransport hnull
  have hnullg : volume (g '' (circleSum 1 '' (W∩{q | c (g (circleSum 1 q))=i})))=0 := by
    rw [show g '' (circleSum 1 '' (W∩{q | c (g (circleSum 1 q))=i}))=
      (fun z => Complex.equivRealProdCLM (z-x)) ⁻¹' (circleSum 1 '' (W∩{q | c (g (circleSum 1 q))=i})) by
        ext z
        constructor
        · rintro ⟨p,hp,rfl⟩
          simpa only [Set.mem_preimage,g,add_sub_cancel_left,ContinuousLinearEquiv.apply_symm_apply] using hp
        · intro hz
          refine ⟨Complex.equivRealProdCLM (z-x),hz,?_⟩
          change x+Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (z-x))=z
          rw [ContinuousLinearEquiv.symm_apply_apply]
          abel]
    exact ((Complex.volume_preserving_equiv_real_prod.comp (measurePreserving_sub_right volume x)).quasiMeasurePreserving.preimage_null himage)
  refine ⟨g '' (circleSum 1 '' W),hgc _ hO,?_,?_⟩
  · refine ⟨circleSum 1 (a,b),⟨(a,b),haW,rfl⟩,?_⟩
    simpa only [angularSum,Complex.ofReal_one,one_mul,angleChart] using hgs (a,b)
  · exact measure_mono_null (by rintro z ⟨⟨q,⟨p,hp,rfl⟩,rfl⟩,hz⟩; exact ⟨_,⟨p,⟨hp,hz⟩,rfl⟩,rfl⟩) hnullg
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionEdge_no_open_exclusion {i j : Fin k} {x : ℂ} (he : TransitionEdge c i j x)
    {U : Set ℂ} (hU : IsOpen U) (hx : x∈U) (hz : volume (U∩{z | c z=i})=0) : False := by
  obtain ⟨r,hr,hB⟩ := Metric.isOpen_iff.mp hU x hx
  have hae : ∀ᵐz : ℂ∂volume,z∈U → c z≠i := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with z hz hu he
    exact hz ⟨hu,he⟩
  have hratio : ∀ᶠh : ℂ in 𝓝[≠] 0, transitionRatio c i j x (r/2) h=0 := by
    have hh : ∀ᶠh : ℂ in 𝓝[≠] 0,‖h‖<r/2 := by
      have hb : ∀ᶠh : ℂ in 𝓝[≠] 0,h∈Metric.ball 0 (r/2) :=
        nhdsWithin_le_nhds (Metric.ball_mem_nhds _ (show 0<r/2 by linarith))
      filter_upwards [hb] with h hh
      simpa only [Metric.mem_ball,dist_zero_right] using hh
    filter_upwards [hh] with h hh
    have hap := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae hae
    have hzT : volume (transitionSet c i j x (r/2) h)=0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hae,hap] with q hq hqh ht
      have hqU : q∈U := hB (Metric.ball_subset_ball (show r/2≤r by linarith) ht.1)
      have hqhU : q+h∈U := by
        apply hB
        have hd := dist_triangle (q+h) q x
        have hdist : dist (q+h) q=‖h‖ := by simp [dist_eq_norm]
        rw [hdist] at hd
        exact hd.trans_lt (by have hqx : dist q x<r/2 := ht.1; linarith)
      rcases ht.2 with ht|ht
      · exact hq hqU ht.1
      · exact hqh hqhU ht.2
    simp only [transitionRatio,hzT,ENNReal.zero_div]
  have hh : limsup (transitionRatio c i j x (r/2)) (𝓝[≠] (0:ℂ))=0 := by
    rw [limsup_congr hratio]
    exact limsup_const 0
  have hp := he.2 (r/2) (by linarith)
  rw [hh] at hp
  exact lt_irrefl _ hp
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
variable {ι X : Type*} [Finite ι] [TopologicalSpace X]
lemma finite_closed_family_locally_subset {S : ι → Set X} (hS : ∀i,IsClosed (S i)) (a : X) :
    ∃V,IsOpen V ∧ a∈V ∧ ∀v∈V,∀i,v∈S i → a∈S i := by
  let V := ⋂i∈({i | a∉S i} : Set ι),(S i)ᶜ
  have hop : IsOpen V := (Set.toFinite _).isOpen_biInter (fun i _ => (hS i).isOpen_compl)
  refine ⟨V,hop,?_,?_⟩
  · exact mem_iInter₂.mpr (fun _ hi => hi)
  · intro v hv i hi
    by_contra hn
    exact mem_iInter₂.mp hv i hn hi
lemma finite_closed_family_no_common_limit {S : ι → Set X} (hS : ∀i,IsClosed (S i))
    {P : ι → Prop} {a : X} {an : ℕ → X} (ha : Tendsto an atTop (𝓝 a))
    (hn : ∀n,∃i,an n∈S i ∧ P i) : ∃i,a∈S i ∧ P i := by
  obtain ⟨V,hV,haV,hsub⟩ := finite_closed_family_locally_subset hS a
  have hev : ∀ᶠn in atTop,an n∈V := ha (hV.mem_nhds haV)
  obtain ⟨n,hnV⟩ := hev.exists
  obtain ⟨i,hi,hP⟩ := hn n
  exact ⟨i,hsub _ hnV i hi,hP⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma stateSupport_local_pred {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {f : ℝ → ι} (hf : Measurable f) {P : ι → Prop} {a : ℝ}
    (ha : ∀i,a∈stateSupport f i → P i) :
    ∃V,IsOpen V ∧ a∈V ∧ ∀ᵐt : ℝ∂volume,t∈V → P (f t) := by
  obtain ⟨V,hV,haV,hsub⟩ := finite_closed_family_locally_subset
    (S := stateSupport f) (fun _ => Measure.isClosed_support) a
  refine ⟨V,hV,haV,?_⟩
  exact (ae_state_support hf).mono fun t ht hv => ha _ (hsub t hv _ ht)
end EuclideanFiveColor
end

end OAI
