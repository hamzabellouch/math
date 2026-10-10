import OAI.Geometry.PlaneColoring.FourContinuity

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma circleSum_one_lipschitz_sumTransport : LipschitzWith 2 (circleSum 1) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hh (g : ℝ → ℝ) (hg : LipschitzWith 1 g) :
      dist (g p.1+g p.2) (g q.1+g q.2)≤2*max (dist p.1 q.1) (dist p.2 q.2) := by
    have h1 := hg.dist_le_mul p.1 q.1
    have h2 := hg.dist_le_mul p.2 q.2
    norm_num only [NNReal.coe_one,one_mul] at h1 h2
    have h3 := dist_add_add_le (g p.1) (g p.2) (g q.1) (g q.2)
    have h4 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
    have h5 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
    linarith
  simpa only [circleSum,one_mul,Prod.dist_eq,NNReal.coe_ofNat] using
    max_le (hh _ Real.lipschitzWith_cos) (hh _ Real.lipschitzWith_sin)

def sumTransport {a b : ℝ} (h : Real.sin (b-a)≠0) (H : RealPlane) (q : RealPlane) :=
  circleInverse h (circleSum 1 q-H)
lemma sumTransport_measurable {a b : ℝ} (h : Real.sin (b-a)≠0) (H : RealPlane) :
    Measurable (sumTransport h H) :=
  (circleInverse_measurable h).comp ((circleSum_continuous 1).sub continuous_const).measurable
lemma sumTransport_neighborhood {a b : ℝ} (h : Real.sin (b-a)≠0) :
    ∃P V : Set RealPlane,IsOpen P ∧ 0∈P ∧ IsOpen V ∧ (a,b)∈V ∧
      ∃K : ℝ≥0,∀H∈P,
        (∀q∈V,ContinuousAt (sumTransport h H) q) ∧
        AntilipschitzWith K (V.domRestrict (sumTransport h H)) ∧
        (∀q∈V,Real.sin (q.2-q.1)≠0) ∧
        (∀q∈V,Real.sin ((sumTransport h H q).2-(sumTransport h H q).1)≠0) ∧
        ∀q∈V,circleSum 1 (sumTransport h H q)=circleSum 1 q-H := by
  have hc : Continuous (fun z : RealPlane×RealPlane => circleSum 1 z.2-z.1) :=
    ((circleSum_continuous 1).comp continuous_snd).sub continuous_fst
  have hbtarget : circleSum 1 (a,b)∈(circleInverseHomeo h).target :=
    (circleSum_strict 1 (a,b)).image_mem_toOpenPartialHomeomorph_target
  have ht : ∀ᶠ z : RealPlane×RealPlane in 𝓝 (0,(a,b)),
      circleSum 1 z.2-z.1∈(circleInverseHomeo h).target ∧
      Real.sin ((circleInverse h (circleSum 1 z.2-z.1)).2-(circleInverse h (circleSum 1 z.2-z.1)).1)≠0 := by
    have hlim : Tendsto (fun z : RealPlane×RealPlane => circleSum 1 z.2-z.1)
        (𝓝 (0,(a,b))) (𝓝 (circleSum 1 (a,b))) := by simpa only [sub_zero] using hc.tendsto (0,(a,b))
    have htt : ∀ᶠ q in 𝓝 (circleSum 1 (a,b)),q∈(circleInverseHomeo h).target :=
      (circleInverseHomeo h).open_target.mem_nhds hbtarget
    exact hlim.eventually (htt.and (circleInverse_regular h))
  obtain ⟨P,hP,W,hW,hPW⟩ := mem_nhds_prod_iff.mp ht
  obtain ⟨P₀,hP₀,hPsub,hPmem⟩ := mem_nhds_iff.mp hP
  obtain ⟨W₀,hW₀,hWsub,hWmem⟩ := mem_nhds_iff.mp hW
  obtain ⟨V₀,hV₀,hv₀,L,hL⟩ := circleSum_local_antilipschitz (r := 1) (p := (a,b)) (by simpa only [one_mul] using h)
  let V := W₀∩V₀∩{q : RealPlane | Real.sin (q.2-q.1)≠0}
  have hV : IsOpen V := (hWsub.inter hV₀).inter ((Real.continuous_sin.comp (continuous_snd.sub continuous_fst)).isOpen_preimage _ isOpen_ne)
  refine ⟨P₀,V,hPsub,hPmem,hV,⟨⟨hWmem,hv₀⟩,h⟩,L*2,?_⟩
  intro H hH
  have htarget (q : RealPlane) (hq : q∈V) := hPW (a := (H,q)) ⟨hP₀ hH,hW₀ hq.1.1⟩
  have heq (q : RealPlane) (hq : q∈V) : circleSum 1 (sumTransport h H q)=circleSum 1 q-H :=
    circleInverse_right h (htarget q hq).1
  refine ⟨?_,?_,fun _ hq => hq.2,fun q hq => (htarget q hq).2,heq⟩
  · intro q hq
    change ContinuousAt (fun z : RealPlane => circleInverse h (circleSum 1 z-H)) q
    exact (circleInverse_continuousAt h (htarget q hq).1).comp (x := q)
      (((circleSum_continuous 1).sub (continuous_const (y := H))).continuousAt)
  · apply AntilipschitzWith.of_le_mul_dist
    intro q r
    have hh := hL.le_mul_dist ⟨q,q.2.1.2⟩ ⟨r,r.2.1.2⟩
    have hd : dist (circleSum 1 q) (circleSum 1 r)=dist (circleSum 1 (sumTransport h H q)) (circleSum 1 (sumTransport h H r)) := by
      rw [heq q q.2,heq r r.2,dist_sub_right]
    change dist (q : RealPlane) (r : RealPlane) ≤ L*dist (circleSum 1 q) (circleSum 1 r) at hh
    rw [hd] at hh
    have hl := circleSum_one_lipschitz_sumTransport.dist_le_mul (sumTransport h H q) (sumTransport h H r)
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left hl L.2
    simp only [NNReal.coe_mul,NNReal.coe_ofNat,Set.domRestrict_apply] at *
    nlinarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def fourNonSingleton (x : ℂ) : Set ℝ := fourSupport c hc x 1∪fourSupport c hc x 2
lemma four_complement_support (x : ℂ) :
    (volume.restrict (fourRealState c hc x 0)ᶜ).support=fourNonSingleton c hc x := by
  have he : (fourRealState c hc x 0)ᶜ=fourRealState c hc x 1∪fourRealState c hc x 2 := by
    ext t
    change (fourState c hc x (t : Angles)≠0) ↔
      fourState c hc x (t : Angles)=1 ∨ fourState c hc x (t : Angles)=2
    exact (show ∀s : Fin 3,s≠0 ↔ s=1 ∨ s=2 from by decide) _
  have hd : Disjoint (fourRealState c hc x 1) (fourRealState c hc x 2) := by
    apply Set.disjoint_left.mpr
    intro t h1 h2
    exact (by decide : (1 : Fin 3)≠2) (h1.symm.trans h2)
  rw [he,Measure.restrict_union hd (four_realState_measurable c hc x 2),Measure.support_add]
  rfl
lemma four_support_transport (hw : WeakColoring 5 c) {x y : ℂ}
    (hx : FourCenter c x) (hy : FourCenter c y) {s : Fin 3} (hs : s≠0)
    {a b : ℝ} (ha : a∈fourSupport c hc x s)
    (hb : b∈fourSupport c hc x (if s=1 then 2 else 1)) (hab : Real.sin (b-a)≠0)
    {P V : Set RealPlane} {K : ℝ≥0} (hV : IsOpen V) (habV : (a,b)∈V)
    (hbranch : ∀H∈P,
        (∀q∈V,ContinuousAt (sumTransport hab H) q) ∧
        AntilipschitzWith K (V.domRestrict (sumTransport hab H)) ∧
        (∀q∈V,Real.sin (q.2-q.1)≠0) ∧
        (∀q∈V,Real.sin ((sumTransport hab H q).2-(sumTransport hab H q).1)≠0) ∧
        ∀q∈V,circleSum 1 (sumTransport hab H q)=circleSum 1 q-H)
    (hxy : Complex.equivRealProdCLM (y-x)∈P) :
    sumTransport hab (Complex.equivRealProdCLM (y-x)) (a,b)∈
      fourNonSingleton c hc y×ˢfourNonSingleton c hc y := by
  obtain ⟨hct,hL,hi,ho,heq⟩ := hbranch _ hxy
  rw [← four_complement_support c hc y]
  apply state_support_transport hc hw
    (fourState_represents c hc hw hx s)
    (fourState_represents c hc hw hx (if s=1 then 2 else 1))
    (fourState_represents c hc hw hy 0)
    ((show ∀s : Fin 3,s≠0 → ∀i : Fin 5,i∉fourGroup s∪fourGroup (if s=1 then 2 else 1) ↔ i=4 from by decide) s hs)
    ha hb (sumTransport_measurable hab _) (hct _ habV) hV habV hL hi ho
  intro q hq
  rw [angularSum_chart,angularSum_chart,heq q hq,map_sub]
  congr 1
  abel
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma four_support_transport_general (coloring : ℂ → Fin 5) (hc : Measurable coloring)
    (hw : WeakColoring 5 coloring) {x y : ℂ}
    (hx : FourCenter coloring x) (hy : FourCenter coloring y) {s : Fin 3} (hs : s≠0)
    {a₀ b₀ : ℝ} (h₀ : Real.sin (b₀-a₀)≠0)
    {a b : ℝ} (ha : a∈fourSupport coloring hc x s)
    (hb : b∈fourSupport coloring hc x (if s=1 then 2 else 1))
    {P V : Set RealPlane} {K : ℝ≥0} (hV : IsOpen V) (habV : (a,b)∈V)
    (hbranch : ∀H∈P,
        (∀q∈V,ContinuousAt (sumTransport h₀ H) q) ∧
        AntilipschitzWith K (V.domRestrict (sumTransport h₀ H)) ∧
        (∀q∈V,Real.sin (q.2-q.1)≠0) ∧
        (∀q∈V,Real.sin ((sumTransport h₀ H q).2-(sumTransport h₀ H q).1)≠0) ∧
        ∀q∈V,circleSum 1 (sumTransport h₀ H q)=circleSum 1 q-H)
    (hxy : Complex.equivRealProdCLM (y-x)∈P) :
    sumTransport h₀ (Complex.equivRealProdCLM (y-x)) (a,b)∈
      fourNonSingleton coloring hc y×ˢfourNonSingleton coloring hc y := by
  obtain ⟨hct,hL,hi,ho,heq⟩ := hbranch _ hxy
  rw [← four_complement_support coloring hc y]
  apply state_support_transport hc hw
    (fourState_represents coloring hc hw hx s)
    (fourState_represents coloring hc hw hx (if s=1 then 2 else 1))
    (fourState_represents coloring hc hw hy 0)
    ((show ∀s : Fin 3,s≠0 → ∀i : Fin 5,i∉fourGroup s∪fourGroup (if s=1 then 2 else 1) ↔ i=4 from by decide) s hs)
    ha hb (sumTransport_measurable h₀ _) (hct _ habV) hV habV hL hi ho
  intro q hq
  rw [angularSum_chart,angularSum_chart,heq q hq,map_sub]
  congr 1
  abel
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma two_closed_shift_separated_not_cover {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (ha : A.Nonempty) (hb : B.Nonempty) (R : X → X)
    (hRA : ∀x∈A,R x∉A) (hRB : ∀x∈B,R x∉B) : A∪B≠univ := by
  intro hcov
  obtain ⟨x,_,hxA,hxB⟩ := isPreconnected_closed_iff.mp isPreconnected_univ A B hA hB
    (by rw [hcov]) (by simpa using ha) (by simpa using hb)
  have hm : R x∈A∪B := hcov.symm ▸ mem_univ _
  exact hm.elim (hRA x hxA) (hRB x hxB)
lemma closed_gap {N : Set ℝ} (hN : IsClosed N) {z l r : ℝ}
    (hz : z∉N) (hl : l∈N) (hr : r∈N) (hlz : l<z) (hzr : z<r) :
    ∃a b : ℝ,a∈N ∧ b∈N ∧ a<z ∧ z<b ∧ Ioo a b⊆Nᶜ := by
  have hLC : IsCompact (N∩Icc l z) := isCompact_Icc.inter_left hN
  have hRC : IsCompact (N∩Icc z r) := isCompact_Icc.inter_left hN
  obtain ⟨a,ha,ham⟩ := hLC.exists_isMaxOn (f := id) ⟨l,hl,le_rfl,hlz.le⟩ continuous_id.continuousOn
  obtain ⟨b,hb,hbm⟩ := hRC.exists_isMinOn (f := id) ⟨r,hr,hzr.le,le_rfl⟩ continuous_id.continuousOn
  have haz : a<z := lt_of_le_of_ne ha.2.2 (fun he => hz (he ▸ ha.1))
  have hzb : z<b := lt_of_le_of_ne hb.2.1 (fun he => hz (he.symm ▸ hb.1))
  refine ⟨a,b,ha.1,hb.1,haz,hzb,?_⟩
  intro t ht hn
  by_cases htz : t≤z
  · have hta : t≤a := ham ⟨hn,ha.2.1.trans ht.1.le,htz⟩
    exact (not_lt_of_ge hta) ht.1
  · have hbt : b≤t := hbm ⟨hn,(not_le.mp htz).le,ht.2.le.trans hb.2.2⟩
    exact (not_lt_of_ge hbt) ht.2
lemma positive_normalized_increment_enters_gap {a b : ℝ} (hab : a<b)
    {u δ : ℕ → ℝ} {v : ℝ} (hδ : ∀n,0<δ n) (hv : 0<v)
    (hu : Tendsto u atTop (𝓝 a))
    (hs : Tendsto (fun n => (u n-a)/δ n) atTop (𝓝 v)) :
    ∀ᶠn in atTop,u n∈Ioo a b := by
  filter_upwards [hu.eventually (gt_mem_nhds hab),hs.eventually (lt_mem_nhds hv)] with n hn hp
  exact ⟨sub_pos.mp ((div_pos_iff.mp hp).resolve_right (fun h => (not_lt_of_ge (hδ n).le) h.2)).1,hn⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma direction_sixty_unit_real (a : ℝ) :
    ‖direction (a : Angles)-direction ((a+sixty : ℝ) : Angles)‖=1 := by
  have he : direction (a : Angles)=direction ((a+sixty : ℝ) : Angles)+direction ((a-sixty : ℝ) : Angles) := by
    apply Complex.equivRealProdCLM.injective
    simpa only [map_add,direction_realPlane,circleTarget,samplingParameter,sub_self,map_zero,one_smul,zero_add,circleSum,one_mul,Prod.mk_add_mk] using sixty_sum (0:ℂ) a
  rw [he,add_sub_cancel_left,direction_norm]
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_support_nonempty (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    {s : Fin 3} (hs : s≠0) : (fourSupport c hc x s).Nonempty := by
  apply Measure.nonempty_support
  intro hz
  have hh := congrArg (fun μ : Measure ℝ => μ univ) hz
  simp only [Measure.restrict_apply_univ,Measure.coe_zero,Pi.zero_apply] at hh
  exact (four_realState_positive c hc hw hx hs).ne' hh
lemma four_support_no_sixty (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    {s : Fin 3} (hs : s≠0) {a : ℝ} (ha : a∈fourSupport c hc x s) :
    a+sixty∉fourSupport c hc x s := by
  intro hb
  exact four_support_sequence_no_unit c hc hw (fun _ => hx) hx tendsto_const_nhds hs
    tendsto_const_nhds tendsto_const_nhds (fun _ => ha) (fun _ => hb) (direction_sixty_unit_real a)
lemma four_support_union_proper (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    fourSupport c hc x 1∪fourSupport c hc x 2≠univ :=
  two_closed_shift_separated_not_cover Measure.isClosed_support Measure.isClosed_support
    (four_support_nonempty c hc hw hx (by decide)) (four_support_nonempty c hc hw hx (by decide))
    (fun a => a+sixty) (fun _ ha => four_support_no_sixty c hc hw hx (by decide) ha)
    (fun _ ha => four_support_no_sixty c hc hw hx (by decide) ha)
lemma four_outside_support_state (x : ℂ) :
    ∀ᵐt : ℝ∂volume,t∉fourSupport c hc x 1∪fourSupport c hc x 2 →
      fourState c hc x (t : Angles)=0 := by
  have h1 : ∀ᵐt : ℝ∂volume,t∈fourRealState c hc x 1 → t∈fourSupport c hc x 1 :=
    (ae_restrict_iff' (four_realState_measurable c hc x 1)).mp (volume.restrict (fourRealState c hc x 1)).support_mem_ae
  have h2 : ∀ᵐt : ℝ∂volume,t∈fourRealState c hc x 2 → t∈fourSupport c hc x 2 :=
    (ae_restrict_iff' (four_realState_measurable c hc x 2)).mp (volume.restrict (fourRealState c hc x 2)).support_mem_ae
  filter_upwards [h1,h2] with t ht1 ht2 hn
  have hn1 : fourState c hc x (t : Angles)≠1 := fun he => hn (Or.inl (ht1 he))
  have hn2 : fourState c hc x (t : Angles)≠2 := fun he => hn (Or.inr (ht2 he))
  exact (show ∀s : Fin 3,s≠1 → s≠2 → s=0 from by decide) _ hn1 hn2
lemma four_gap_length (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    {a b : ℝ} (hgap : Ioo a b⊆(fourSupport c hc x 1∪fourSupport c hc x 2)ᶜ) : b-a ≤ sixty := by
  by_contra! hab
  have hp : 0<volume (Ioo a (b-sixty)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have h0 := four_outside_support_state c hc x
  have hshift := (measurePreserving_add_right (volume : Measure ℝ) sixty).quasiMeasurePreserving.ae h0
  have hneq := angleMk_quasiMeasurePreserving.ae (fourState_changes c hc hw hx)
  obtain ⟨t,ht,ht0,hts,htn⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp.ne'
    (ae_restrict_of_ae (h0.and (hshift.and hneq)))
  have hκ : 0<sixty := by dsimp [sixty]; positivity
  have he0 := ht0 (hgap ⟨ht.1,by linarith [ht.2]⟩)
  have he1 := hts (hgap ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  apply htn
  simpa only [sixty,AddCircle.coe_add,he0] using he1.symm
lemma four_gap_exists (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∃a b : ℝ,a∈fourSupport c hc x 1∪fourSupport c hc x 2 ∧
      b∈fourSupport c hc x 1∪fourSupport c hc x 2 ∧ a<b ∧ b-a ≤ sixty ∧
      Ioo a b⊆(fourSupport c hc x 1∪fourSupport c hc x 2)ᶜ := by
  let N := fourSupport c hc x 1∪fourSupport c hc x 2
  have hN : IsClosed N := Measure.isClosed_support.union Measure.isClosed_support
  have hex : ∃z : ℝ,z∉N := by
    by_contra! h
    exact four_support_union_proper c hc hw hx (Set.eq_univ_of_forall h)
  obtain ⟨z,hz⟩ := hex
  have hκ : 0<sixty := by dsimp [sixty]; positivity
  have hn (a b : ℝ) (hab : sixty<b-a) : ∃t∈Ioo a b,t∈N := by
    by_contra! hbad
    have hle := four_gap_length c hc hw hx hbad
    exact (not_lt_of_ge hle) hab
  obtain ⟨l,hl,hlN⟩ := hn (z-sixty-1) z (by linarith)
  obtain ⟨r,hr,hrN⟩ := hn z (z+sixty+1) (by linarith)
  obtain ⟨a,b,ha,hb,haz,hzb,hgap⟩ := closed_gap hN hz hlN hrN hl.2 hr.1
  exact ⟨a,b,ha,hb,haz.trans hzb,four_gap_length c hc hw hx hgap,hgap⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma open_subset_closed_of_ae {U N : Set ℝ} (hU : IsOpen U) (hN : IsClosed N)
    (h : ∀ᵐt : ℝ∂volume,t∈U → t∈N) : U⊆N := by
  apply Set.sdiff_eq_empty.mp
  apply (hU.sdiff hN).eq_empty_of_measure_zero (μ := volume)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [h] with t ht htn
  exact htn.2 (ht htn.1)
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_gap_shift_subset (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    {a b : ℝ} (hab : a<b)
    (hgap : Ioo a b⊆(fourSupport c hc x 1∪fourSupport c hc x 2)ᶜ) :
    Icc (a+sixty) (b+sixty)⊆fourSupport c hc x 1∪fourSupport c hc x 2 := by
  have hN : IsClosed (fourSupport c hc x 1∪fourSupport c hc x 2) :=
    Measure.isClosed_support.union Measure.isClosed_support
  have hs : Ioo (a+sixty) (b+sixty)⊆fourSupport c hc x 1∪fourSupport c hc x 2 := by
    apply open_subset_closed_of_ae isOpen_Ioo hN
    have h0 := four_outside_support_state c hc x
    have hneq : ∀ᵐt : ℝ∂volume,fourState c hc x (t : Angles)≠fourState c hc x ((t+sixty : ℝ) : Angles) := by
      simpa only [AddCircle.coe_add,sixty] using angleMk_quasiMeasurePreserving.ae (fourState_changes c hc hw hx)
    have hm := (measurePreserving_add_right (volume : Measure ℝ) (-sixty)).quasiMeasurePreserving
    filter_upwards [h0,hm.ae h0,hm.ae hneq] with t ht htm htn htI
    by_contra hn
    have he0 := ht hn
    have hem := htm (hgap ⟨by linarith [htI.1],by linarith [htI.2]⟩)
    apply htn
    simp only [neg_add_cancel_right,he0,hem]
  have hz := closure_minimal hs hN
  rwa [closure_Ioo (by linarith : a+sixty≠b+sixty)] at hz
end EuclideanFiveColor
end

noncomputable section
open Filter Topology Asymptotics
namespace EuclideanFiveColor
lemma strict_increment_limit {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E →L[ℝ] F} {p : E}
    (hf : HasStrictFDerivAt f L p) {u v : ℕ → E} {δ : ℕ → ℝ} {w : E}
    (hu : Tendsto u atTop (𝓝 p)) (hv : Tendsto v atTop (𝓝 p)) (hδ : ∀n,0<δ n)
    (hw : Tendsto (fun n => (δ n)⁻¹ • (u n-v n)) atTop (𝓝 w)) :
    Tendsto (fun n => (δ n)⁻¹ • (f (u n)-f (v n))) atTop (𝓝 (L w)) := by
  have hb : (fun n => u n-v n) =O[atTop] δ := by
    apply IsBigO.of_bound (‖w‖+1)
    filter_upwards [hw.norm.eventually (gt_mem_nhds (lt_add_one ‖w‖))] with n hn
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (hδ n)] at hn
    rw [Real.norm_eq_abs,abs_of_pos (hδ n)]
    exact ((inv_mul_lt_iff₀ (hδ n)).mp hn).le.trans_eq (mul_comm _ _)
  have ho : (fun n => f (u n)-f (v n)-L (u n-v n)) =o[atTop] δ :=
    (hf.isLittleO.comp_tendsto (hu.prodMk_nhds hv)).trans_isBigO hb
  have hz := ho.tendsto_inv_smul_nhds_zero
  have hl := L.continuous.tendsto w |>.comp hw
  have hh := hz.add hl
  simpa only [Function.comp_def,map_smul,smul_sub,map_sub,sub_add_cancel,zero_add] using hh
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
def transportVelocity (H : RealPlane) (a b : ℝ) : ℝ :=
  -(H.1*Real.cos b+H.2*Real.sin b)/Real.sin (b-a)
lemma circleInverseDeriv_fst {a b : ℝ} (h : Real.sin (b-a)≠0) (H : RealPlane) :
    ((circleSumDerivEquiv (r := 1) (p := (a,b)) (by simpa only [one_mul] using h)).symm (-H)).1=
      transportVelocity H a b := by
  let L := circleSumDerivEquiv (r := 1) (p := (a,b)) (by simpa only [one_mul] using h)
  let q := L.symm (-H)
  have he : circleSumDeriv 1 (a,b) q = -H := L.apply_symm_apply (-H)
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  change 1*(-Real.sin a*q.1)+(-Real.sin b)*q.2= -H.1 at h1
  change 1*(Real.cos a*q.1)+Real.cos b*q.2= -H.2 at h2
  change q.1= -(H.1*Real.cos b+H.2*Real.sin b)/Real.sin (b-a)
  apply (eq_div_iff h).mpr
  rw [Real.sin_sub]
  linear_combination Real.cos b*h1+Real.sin b*h2
lemma sumTransport_increment_limit {a b : ℝ} (h : Real.sin (b-a)≠0)
    {Hn q : ℕ → RealPlane} {δ : ℕ → ℝ} {H : RealPlane}
    (hH : Tendsto Hn atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 (a,b)))
    (hδ : ∀n,0<δ n) (hdir : Tendsto (fun n => (δ n)⁻¹•Hn n) atTop (𝓝 H)) :
    Tendsto (fun n => ((sumTransport h (Hn n) (q n)).1-(q n).1)/δ n)
      atTop (𝓝 (transportVelocity H a b)) := by
  have hv : Tendsto (fun n => circleSum 1 (q n)) atTop (𝓝 (circleSum 1 (a,b))) :=
    ((circleSum_continuous 1).tendsto (a,b)).comp hq
  have hu : Tendsto (fun n => circleSum 1 (q n)-Hn n) atTop (𝓝 (circleSum 1 (a,b))) := by
    simpa only [sub_zero] using hv.sub hH
  have hdiff : Tendsto (fun n => (δ n)⁻¹•((circleSum 1 (q n)-Hn n)-circleSum 1 (q n)))
      atTop (𝓝 (-H)) := by
    simpa only [sub_sub_cancel_left,smul_neg] using hdir.neg
  have hh := strict_increment_limit (circleInverse_strict h) hu hv hδ hdiff
  have hid : ∀ᶠ n in atTop,circleInverse h (circleSum 1 (q n))=q n := by
    have hb : (a,b)∈(circleInverseHomeo h).source :=
      (circleSum_strict 1 (a,b)).mem_toOpenPartialHomeomorph_source
    filter_upwards [hq.eventually ((circleInverseHomeo h).open_source.mem_nhds hb)] with n hn
    have ht : circleSum 1 (q n)∈(circleInverseHomeo h).target := (circleInverseHomeo h).map_source hn
    rw [circleInverse_eq h ht]
    exact (circleInverseHomeo h).left_inv hn
  have hf := hh.fst_nhds
  simp only [ContinuousLinearEquiv.coe_coe] at hf
  rw [circleInverseDeriv_fst h H] at hf
  apply hf.congr'
  filter_upwards [hid] with n hn
  simp only [hn,div_eq_inv_mul,sumTransport]
  rfl
lemma sumTransport_tendsto {a b : ℝ} (h : Real.sin (b-a)≠0)
    {Hn q : ℕ → RealPlane} (hH : Tendsto Hn atTop (𝓝 0))
    (hq : Tendsto q atTop (𝓝 (a,b))) :
    Tendsto (fun n => sumTransport h (Hn n) (q n)) atTop (𝓝 (a,b)) := by
  have ht : Tendsto (fun n => circleSum 1 (q n)-Hn n) atTop (𝓝 (circleSum 1 (a,b))) := by
    simpa only [sub_zero,Function.comp_def] using (((circleSum_continuous 1).tendsto (a,b)).comp hq).sub hH
  have hi := (circleInverse_strict h).continuousAt.tendsto.comp ht
  simpa only [sub_zero,circleInverse_at,sumTransport,Function.comp_def] using hi
lemma transportVelocity_neg (H : RealPlane) (a b : ℝ) :
    transportVelocity (-H) a b= -transportVelocity H a b := by
  simp only [transportVelocity,Prod.fst_neg,Prod.snd_neg]
  ring
lemma sumTransport_double_increment {a b b' : ℝ}
    (h : Real.sin (b-a)≠0) (h' : Real.sin (b'-a)≠0)
    {Hn : ℕ → RealPlane} {δ bn : ℕ → ℝ} {H : RealPlane}
    (hH : Tendsto Hn atTop (𝓝 0)) (hb : Tendsto bn atTop (𝓝 b'))
    (hδ : ∀n,0<δ n) (hdir : Tendsto (fun n => (δ n)⁻¹•Hn n) atTop (𝓝 H)) :
    Tendsto (fun n =>
      ((sumTransport h' (-Hn n) ((sumTransport h (Hn n) (a,b)).1,bn n)).1-a)/δ n)
      atTop (𝓝 (transportVelocity H a b-transportVelocity H a b')) := by
  have hct := sumTransport_tendsto h hH tendsto_const_nhds
  have hf := sumTransport_increment_limit h hH tendsto_const_nhds hδ hdir
  have hn : Tendsto (fun n => -Hn n) atTop (𝓝 0) := by simpa only [neg_zero] using hH.neg
  have hnd : Tendsto (fun n => (δ n)⁻¹•(-Hn n)) atTop (𝓝 (-H)) := by
    simpa only [smul_neg] using hdir.neg
  have hr := sumTransport_increment_limit h' hn (hct.fst_nhds.prodMk_nhds hb) hδ hnd
  have hh := hr.add hf
  rw [transportVelocity_neg] at hh
  convert hh using 1
  · funext n
    dsimp
    ring
  · ring_nf
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_angular_nonparallel (a : ℝ) : ∀ᵐb : ℝ∂volume,Real.sin (b-a)≠0 := by
  have hs : {b : ℝ | Real.sin (b-a)=0}⊆Set.range (fun n : ℤ => a+n*Real.pi) := by
    intro b hb
    obtain ⟨n,hn⟩ := Real.sin_eq_zero_iff.mp hb
    exact ⟨n,by linarith⟩
  rw [ae_iff]
  simpa only [not_not] using measure_mono_null hs ((countable_range _).measure_zero volume)
lemma transportVelocity_ne {H : RealPlane} {a b b' : ℝ}
    (ha : H.1*Real.cos a+H.2*Real.sin a≠0)
    (hb : Real.sin (b-a)≠0) (hb' : Real.sin (b'-a)≠0)
    (hbb : Real.sin (b'-b)≠0) : transportVelocity H a b≠transportVelocity H a b' := by
  intro he
  have hq := (div_eq_div_iff hb hb').mp he
  have hz : (H.1*Real.cos a+H.2*Real.sin a)*Real.sin (b'-b)=0 := by
    simp only [Real.sin_sub] at hq ⊢
    linear_combination -hq
  exact mul_ne_zero ha hbb hz
lemma exists_transportVelocity_lt {A : Set ℝ} (hA : 0<volume A)
    {H : RealPlane} {a : ℝ} (ha : H.1*Real.cos a+H.2*Real.sin a≠0) :
    ∃b∈A,∃b'∈A,Real.sin (b-a)≠0 ∧ Real.sin (b'-a)≠0 ∧
      transportVelocity H a b<transportVelocity H a b' := by
  obtain ⟨b,hb,hba⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hA.ne'
    (ae_restrict_of_ae (ae_angular_nonparallel a))
  obtain ⟨b',hb',hba',hbb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hA.ne'
    (ae_restrict_of_ae ((ae_angular_nonparallel a).and (ae_angular_nonparallel b)))
  rcases (transportVelocity_ne ha hba hba' hbb).lt_or_gt with hlt | hgt
  · exact ⟨b,hb,b',hb',hba,hba',hlt⟩
  · exact ⟨b',hb',b,hb,hba',hba,hgt⟩
end EuclideanFiveColor
end

end OAI
