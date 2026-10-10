import OAI.Geometry.PlaneColoring.BoundaryTrace

namespace OAI

noncomputable section
namespace EuclideanFiveColor
/-- `0` is the outsider and `1,2` the two diagonal states. -/
def FourWordValid (w : Fin 6 → Fin 3) : Prop :=
  (∀j,w j≠w (j+1)) ∧ (∀j,w j≠0 → w (j+3)≠0 → w (j+3)=w j)
instance (w : Fin 6 → Fin 3) : Decidable (FourWordValid w) := inferInstanceAs (Decidable (_∧_))
def FourWordMixed (w : Fin 6 → Fin 3) : Prop :=
  ∃i j,w i=0 ∧ w j=0 ∧ i.val%2≠j.val%2
instance (w : Fin 6 → Fin 3) : Decidable (FourWordMixed w) := inferInstanceAs (Decidable (∃_i _j,_∧_∧_))
def FourWordCross (w u : Fin 6 → Fin 3) : Prop :=
  ∀j,w j≠0 → u (j+1)≠w j ∧ u (j-1)≠w j
instance (w u : Fin 6 → Fin 3) : Decidable (FourWordCross w u) := inferInstanceAs (Decidable (∀_j,_→_∧_))
lemma forall_six_word (P : (Fin 6 → Fin 3) → Prop) :
    (∀w,P w) ↔ ∀a b c d e f : Fin 3,P ![a,b,c,d,e,f] := by
  constructor
  · intro h a b c d e f
    exact h _
  · intro h w
    have he : w=![w 0,w 1,w 2,w 3,w 4,w 5] := by
      ext j
      fin_cases j <;> rfl
    rw [he]
    exact h _ _ _ _ _ _
lemma four_word_has_outsider : ∀w : Fin 6 → Fin 3,FourWordValid w → ∃j,w j=0 := by
  simp only [forall_six_word]
  decide
lemma four_word_mixed_periodic : ∀w : Fin 6 → Fin 3,FourWordValid w → FourWordMixed w →
    (∀j,w (j+3)=w j) ∧ w 0≠w 1 ∧ w 1≠w 2 ∧ w 0≠w 2 := by
  simp only [forall_six_word]
  decide
lemma four_word_mixed_isolated : ∀w : Fin 6 → Fin 3,FourWordValid w → FourWordMixed w →
    ∀u : Fin 6 → Fin 3,FourWordValid u → FourWordCross w u → u=w := by
  simp only [forall_six_word]
  decide
lemma four_word_parity : ∀w : Fin 6 → Fin 3,FourWordValid w → ¬FourWordMixed w →
    ∃p : Fin 2,∀j,w j=0 → j.val%2=p.val := by
  simp only [forall_six_word]
  decide
lemma four_word_shift_parity : ∀w : Fin 6 → Fin 3,∀p : Fin 2,
    (∀j,w j=0 → j.val%2=p.val) → ∀j,w (j+1)=0 → j.val%2=(p+1).val := by
  simp only [forall_six_word]
  decide
lemma four_word_opposite_parity : ∀w : Fin 6 → Fin 3,FourWordValid w →
    (∀j,w j=0 → j.val%2=0) → ∀u : Fin 6 → Fin 3,FourWordValid u →
    (∀j,u j=0 → j.val%2=1) → FourWordCross w u →
    ∃a b : Fin 3,a≠0 ∧ b≠0 ∧ a≠b ∧
      (∀j,j.val%2=1 → w j=a) ∧ (∀j,j.val%2=0 → u j=b) := by
  simp only [forall_six_word]
  decide
end EuclideanFiveColor
end

noncomputable section
open Set Topology
namespace EuclideanFiveColor
/-- Uniform local isolation of a value on a dense subset of a connected metric
space propagates globally. This is the manuscript dense-set chain argument. -/
lemma dense_isolated_value_constant {E F : Type*} [MetricSpace E] [PreconnectedSpace E]
    {G : Set E} (hG : Dense G) (f : E → F) {b : F} {ε : ℝ} (hε : 0<ε)
    (hne : ∃x∈G,f x=b)
    (hl : ∀x∈G,f x=b → ∀y∈G,dist x y<ε → f y=b) : ∀y∈G,f y=b := by
  let A : Set E := {x | x∈G ∧ f x=b}
  have hAne : A.Nonempty := hne
  have hAopen : IsOpen (closure A) := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨a,ha,had⟩ := Metric.mem_closure_iff.mp hx ε hε
    have hsub : Metric.ball a ε∩G⊆A := by
      intro y hy
      exact ⟨hy.2,hl a ha.1 ha.2 y hy.2 (by simpa only [Metric.mem_ball,dist_comm] using hy.1)⟩
    have hball : Metric.ball a ε⊆closure A := by
      intro y hy
      apply closure_mono hsub
      exact Metric.isOpen_ball.inter_closure ⟨hy,hG y⟩
    exact ⟨Metric.ball a ε,hball,Metric.isOpen_ball,had⟩
  have hfull : closure A=univ := (show IsClopen (closure A) from ⟨isClosed_closure,hAopen⟩).eq_univ
    (hAne.mono subset_closure)
  intro y hy
  have hym : y∈closure A := by rw [hfull]; trivial
  obtain ⟨a,ha,had⟩ := Metric.mem_closure_iff.mp hym ε hε
  exact hl a ha.1 ha.2 y hy (by simpa only [dist_comm] using had)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma sixty_six : (6 : ℕ) • (sixty : Angles)=0 := by
  rw [← AddCircle.coe_nsmul]
  convert AddCircle.coe_period (p := 2*Real.pi) using 1
  congr 1
  simp only [nsmul_eq_mul,sixty]
  ring
lemma sixty_three : (3 : ℕ) • (sixty : Angles)=(Real.pi : Angles) := by
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul,sixty]
  ring
def sixAngle (j : Fin 6) : Angles := j.val • (sixty : Angles)
lemma sixAngle_step (j : Fin 6) : sixAngle (j+1)=sixAngle j+(sixty : Angles) := by
  fin_cases j <;> norm_num [sixAngle,Fin.val_add,succ_nsmul]
  simpa only [succ_nsmul,zero_nsmul,zero_add] using sixty_six.symm
lemma sixAngle_half (j : Fin 6) : sixAngle (j+3)=sixAngle j+(Real.pi : Angles) := by
  rw [show j+3=(j+1+1)+1 from (by decide : ∀j : Fin 6,j+3=(j+1+1)+1) j,sixAngle_step,sixAngle_step,sixAngle_step,← sixty_three]
  simp only [succ_nsmul,zero_nsmul,zero_add]
  abel
lemma direction_add_pi (t : Angles) : direction (t+(Real.pi : Angles))= -direction t := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← AddCircle.coe_add,direction_real,direction_real,Circle.exp_add]
  simp
end EuclideanFiveColor
end

noncomputable section
open Set Topology
namespace EuclideanFiveColor
/-- The mixed-parity exceptional words are excluded by actual local isolation
and sixty-degree covariance on a dense set. -/
lemma four_words_no_mixed (G : Set Angles) (hG : Dense G) (w : Angles → Fin 6 → Fin 3)
    (hv : ∀t∈G,FourWordValid (w t))
    (hshiftG : ∀t∈G,t+(sixty : Angles)∈G)
    (hshift : ∀t∈G,∀j,w (t+(sixty : Angles)) j=w t (j+1))
    {ε : ℝ} (hε : 0<ε)
    (hcross : ∀t∈G,∀u∈G,dist t u<ε → FourWordCross (w t) (w u)) :
    ∀t∈G,¬FourWordMixed (w t) := by
  intro t ht hm
  have he : ∀u∈G,w u=w t := by
    apply dense_isolated_value_constant hG w hε ⟨t,ht,rfl⟩
    intro u hu hue v hv' hdist
    exact (four_word_mixed_isolated (w u) (hv u hu) (by rw [hue]; exact hm)
      (w v) (hv v hv') (hcross u hu v hv' hdist)).trans hue
  have hconst := congrFun (he (t+(sixty : Angles)) (hshiftG t ht)) 0
  rw [hshift t ht 0] at hconst
  exact (hv t ht).1 0 hconst.symm
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
/-- The source's strict min/max straddling region, in equivalent witness form. -/
def Straddle (K : Set ℂ) : Set ℂ := {z | ∃p∈K,∃q∈K,dist z p<1 ∧ 1<dist z q}
lemma straddle_isOpen (K : Set ℂ) : IsOpen (Straddle K) := by
  have he : Straddle K=⋃p∈K,⋃q∈K,{z | dist z p<1 ∧ 1<dist z q} := by
    ext z
    simp only [Straddle,mem_iUnion,mem_ofPred_eq,exists_prop]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      (isOpen_lt continuous_const (continuous_id.dist continuous_const))
lemma straddle_connected_unit {K : Set ℂ} (hK : IsPreconnected K) {z : ℂ} (hz : z∈Straddle K) :
    ∃p∈K,dist z p=1 := by
  obtain ⟨p,hp,q,hq,hp1,hq1⟩ := hz
  exact hK.intermediate_value hp hq (continuous_const.dist continuous_id).continuousOn ⟨hp1.le,hq1.le⟩
lemma approaching_direction_inside {r : ℕ → ℝ} {w : ℕ → ℂ} {v e : ℂ}
    (hr : ∀n,0<r n) (hr0 : Tendsto r atTop (𝓝 0)) (hw : ∀n,‖w n‖=1)
    (hwv : Tendsto w atTop (𝓝 v)) (he : ‖e‖=1) (hv : 0<⟪e,v⟫) :
    ∀ᶠn in atTop,‖e-(r n : ℂ)*w n‖<1 := by
  have ht : Tendsto (fun n => 2*⟪e,w n⟫-r n) atTop (𝓝 (2*⟪e,v⟫)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds.inner hwv).const_mul 2).sub hr0
  filter_upwards [ht.eventually (lt_mem_nhds (by positivity : (0:ℝ)<2*⟪e,v⟫))] with n hn
  have heq : ‖e-(r n : ℂ)*w n‖^2=1-2*r n*⟪e,w n⟫+(r n)^2 := by
    change ‖e-r n • w n‖^2= _
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hr n),he,hw]
    ring
  have hpos := mul_pos (hr n) hn
  nlinarith [norm_nonneg (e-(r n : ℂ)*w n)]
lemma approaching_direction_outside {r : ℕ → ℝ} {w : ℕ → ℂ} {v e : ℂ}
    (hr : ∀n,0<r n) (hr0 : Tendsto r atTop (𝓝 0)) (hw : ∀n,‖w n‖=1)
    (hwv : Tendsto w atTop (𝓝 v)) (he : ‖e‖=1) (hv : ⟪e,v⟫<0) :
    ∀ᶠn in atTop,1<‖e-(r n : ℂ)*w n‖ := by
  have ht : Tendsto (fun n => 2*⟪e,w n⟫-r n) atTop (𝓝 (2*⟪e,v⟫)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds.inner hwv).const_mul 2).sub hr0
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : 2*⟪e,v⟫<(0:ℝ)))] with n hn
  have heq : ‖e-(r n : ℂ)*w n‖^2=1-2*r n*⟪e,w n⟫+(r n)^2 := by
    change ‖e-r n • w n‖^2= _
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hr n),he,hw]
    ring
  have hneg := mul_neg_of_pos_of_neg (hr n) hn
  nlinarith [norm_nonneg (e-(r n : ℂ)*w n)]
lemma outer_straddle_strip {K : Set ℂ} {x e q : ℂ} (hx : x∈K) (hq : q∈K)
    (_he : ‖e‖=1) (hed : dist (x+e) q<1) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,1<r → r<1+δ →
      x+(r : ℂ)*e'∈Straddle K := by
  have hn : ∀ᶠp : ℝ × ℂ in 𝓝 (1,e),dist (x+(p.1 : ℂ)*p.2) q<1 :=
    (show Continuous (fun p : ℝ × ℂ => dist (x+(p.1 : ℂ)*p.2) q) by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simpa only [Complex.ofReal_one,one_mul] using hed))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,fun e' he' heδ r hr hrδ => ⟨q,hq,x,hx,?_,?_⟩⟩
  · apply hsub (a := (r,e'))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by rw [Real.dist_eq,abs_of_pos (by linarith : 0<r-1)]; linarith,heδ⟩
  · rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<r),he',mul_one]
    exact hr
lemma inner_straddle_strip {K : Set ℂ} {x e q : ℂ} (hx : x∈K) (hq : q∈K)
    (_he : ‖e‖=1) (hed : 1<dist (x+e) q) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,0<r → 1-δ<r → r<1 →
      x+(r : ℂ)*e'∈Straddle K := by
  have hn : ∀ᶠp : ℝ × ℂ in 𝓝 (1,e),1<dist (x+(p.1 : ℂ)*p.2) q :=
    (show Continuous (fun p : ℝ × ℂ => dist (x+(p.1 : ℂ)*p.2) q) by fun_prop).continuousAt.eventually
      (lt_mem_nhds (by simpa only [Complex.ofReal_one,one_mul] using hed))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,fun e' he' heδ r hr hrδ hr1 => ⟨x,hx,q,hq,?_,?_⟩⟩
  · rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,he',mul_one]
    exact hr1
  · apply hsub (a := (r,e'))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by rw [Real.dist_eq,abs_of_neg (by linarith : r-1<0)]; linarith,heδ⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma finite_positive_lower_bound {ι : Type*} (E : Finset ι) (d : ι → ℝ)
    (hd : ∀i∈E,0<d i) : ∃δ>0,δ≤1 ∧ ∀i∈E,δ≤d i := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,le_rfl,by simp⟩
  | @insert a E ha ih =>
    obtain ⟨δ,hδ,hδ1,hδd⟩ := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (d a),lt_min hδ (hd a (Finset.mem_insert_self _ _)),(min_le_left _ _).trans hδ1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδd i hi)
/-- The approach data furnished by the manuscript interface proposition, with no
assumption of angular strip conclusions. -/
structure ApproachingContinuum (x : ℂ) (K : Set ℂ) (v : ℂ) where
  center_mem : x∈K
  r : ℕ → ℝ
  w : ℕ → ℂ
  r_pos : ∀n,0<r n
  r_tendsto : Tendsto r atTop (𝓝 0)
  w_unit : ∀n,‖w n‖=1
  w_tendsto : Tendsto w atTop (𝓝 v)
  point_mem : ∀n,x+(r n : ℂ)*w n∈K
lemma ApproachingContinuum.outer_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hv : 0<⟪e,v⟫) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,1<r → r<1+δ →
      x+(r : ℂ)*e'∈Straddle K := by
  obtain ⟨n,hn⟩ := (approaching_direction_inside h.r_pos h.r_tendsto h.w_unit h.w_tendsto he hv).exists
  apply outer_straddle_strip h.center_mem (h.point_mem n) he
  simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hn
lemma ApproachingContinuum.inner_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hv : ⟪e,v⟫<0) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,0<r → 1-δ<r → r<1 →
      x+(r : ℂ)*e'∈Straddle K := by
  obtain ⟨n,hn⟩ := (approaching_direction_outside h.r_pos h.r_tendsto h.w_unit h.w_tendsto he hv).exists
  apply inner_straddle_strip h.center_mem (h.point_mem n) he
  simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hn
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma continuum_outer_restriction {ι : Type*} [Fintype ι] (E : Finset ι)
    {x : ℂ} {K : ι → Set ℂ} {v : ι → ℂ} (hK : ∀i,ApproachingContinuum x (K i) (v i))
    {J : Finset (Fin k)}
    (hJ : ∀ᵐz : ℂ∂volume,(∀i∈E,z∈Straddle (K i)) → c z∈J) :
    ∀ᵐt∂angularMeasure,(∀i∈E,0<⟪direction t,v i⟫) → (palette c hc x t∩J).Nonempty := by
  classical
  apply ae_of_locally_ae angularMeasure
  intro t ht
  have hex (i : E) := (hK i).outer_strip (direction_norm t) (ht i i.2)
  choose d hd hs using hex
  obtain ⟨δ,hδ,_,hδd⟩ := finite_positive_lower_bound Finset.univ d (fun i _ => hd i)
  let W : Set ℂ := ⋂i : E,Straddle (K i)
  have ho : IsOpen W := isOpen_iInter_of_finite fun i => straddle_isOpen (K i)
  have hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J := hJ.mono fun z hz hzW => hz
    (fun i hi => mem_iInter.mp hzW ⟨i,hi⟩)
  exact outer_strip_trace c hc hδ ho hW (fun u hu r hr hrδ => by
    apply mem_iInter.mpr
    intro i
    apply hs i (direction u) (direction_norm u) (hu.trans_le (hδd i (Finset.mem_univ _))) r hr
    linarith [hδd i (Finset.mem_univ _)])
lemma continuum_inner_restriction {ι : Type*} [Fintype ι] (E : Finset ι)
    {x : ℂ} {K : ι → Set ℂ} {v : ι → ℂ} (hK : ∀i,ApproachingContinuum x (K i) (v i))
    {J : Finset (Fin k)}
    (hJ : ∀ᵐz : ℂ∂volume,(∀i∈E,z∈Straddle (K i)) → c z∈J) :
    ∀ᵐt∂angularMeasure,(∀i∈E,⟪direction t,v i⟫<0) → (palette c hc x t∩J).Nonempty := by
  classical
  apply ae_of_locally_ae angularMeasure
  intro t ht
  have hex (i : E) := (hK i).inner_strip (direction_norm t) (ht i i.2)
  choose d hd hs using hex
  obtain ⟨δ,hδ,_,hδd⟩ := finite_positive_lower_bound Finset.univ d (fun i _ => hd i)
  let W : Set ℂ := ⋂i : E,Straddle (K i)
  have ho : IsOpen W := isOpen_iInter_of_finite fun i => straddle_isOpen (K i)
  have hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J := hJ.mono fun z hz hzW => hz
    (fun i hi => mem_iInter.mp hzW ⟨i,hi⟩)
  exact inner_strip_trace c hc hδ ho hW (fun u hu r hr hrδ hr1 => by
    apply mem_iInter.mpr
    intro i
    apply hs i (direction u) (direction_norm u) (hu.trans_le (hδd i (Finset.mem_univ _))) r hr
    · linarith [hδd i (Finset.mem_univ _)]
    · exact hr1)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
/-- The manuscript's essential spatial color support. -/
def spatialSupport (i : Fin k) : Set ℂ := (volume.restrict {z | c z=i}).support
lemma mem_spatialSupport_ae (hc : Measurable c) (i : Fin k) :
    ∀ᵐz : ℂ∂volume,c z=i → z∈spatialSupport c i :=
  (ae_restrict_iff' (measurableSet_eq_fun hc measurable_const)).mp
    (volume.restrict {z | c z=i}).support_mem_ae
lemma support_exclusion_ae (hc : Measurable c) {i : Fin k} {W : Set ℂ}
    (h : Disjoint (spatialSupport c i) W) : ∀ᵐz : ℂ∂volume,z∈W → c z≠i := by
  filter_upwards [mem_spatialSupport_ae c hc i] with z hz hzW hzcol
  exact Set.disjoint_left.mp h (hz hzcol) hzW
lemma finite_support_exclusion_ae (hc : Measurable c) {ι : Type*} [Fintype ι]
    (K : ι → Set ℂ) (F : ι → Finset (Fin k))
    (h : ∀i,∀j∈F i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    ∀ᵐz : ℂ∂volume,∀i,z∈Straddle (K i) → c z∉F i := by
  have hh : ∀i,∀j,∀ᵐz : ℂ∂volume,j∈F i → z∈Straddle (K i) → c z≠j := by
    intro i j
    by_cases hj : j∈F i
    · exact (support_exclusion_ae c hc (h i j hj)).mono fun z hz _ => hz
    · exact Eventually.of_forall fun _ h => (hj h).elim
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hh i))] with z hz i hi hj
  exact hz i (c z) hj hi rfl
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
def angleEssential (s : Angles → Bool) (b : Bool) : Set Angles :=
  {t | ∃U : Set Angles,IsOpen U ∧ t∈U ∧ ∀ᵐu∂angularMeasure,u∈U → s u=b}
lemma angleEssential_open (s : Angles → Bool) (b : Bool) : IsOpen (angleEssential s b) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro t ⟨U,hU,ht,ha⟩
  exact ⟨U,fun u hu => ⟨U,hU,hu,ha⟩,hU,ht⟩
lemma angleEssential_ae (s : Angles → Bool) (b : Bool) :
    ∀ᵐt∂angularMeasure,t∈angleEssential s b → s t=b := ae_of_locally_ae angularMeasure (fun _ h => h)
lemma angleEssential_disjoint (s : Angles → Bool) {a b : Bool} (hab : a≠b) :
    Disjoint (angleEssential s a) (angleEssential s b) := by
  apply disjoint_left.mpr
  rintro t ⟨U,hU,ht,ha⟩ ⟨V,hV,ht',hb⟩
  have hpos := (hU.inter hV).measure_pos angularMeasure ⟨t,ht,ht'⟩
  obtain ⟨u,hu,huab⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae (ha.and hb))
  exact hab ((huab.1 hu.1).symm.trans (huab.2 hu.2))
def angleBoundary (s : Angles → Bool) : Set Angles := (⋃b,angleEssential s b)ᶜ
lemma angleBoundary_closed (s : Angles → Bool) : IsClosed (angleBoundary s) :=
  (isOpen_iUnion (angleEssential_open s)).isClosed_compl
lemma angleEssential_shift {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (t : Angles) (b : Bool) :
    t+(sixty : Angles)∈angleEssential s (!b) ↔ t∈angleEssential s b := by
  constructor
  · rintro ⟨U,hU,ht,ha⟩
    refine ⟨(fun q : Angles => q+(sixty : Angles)) ⁻¹' U,hU.preimage (continuous_id.add continuous_const),ht,?_⟩
    filter_upwards [(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae ha,hf] with q hq hqf hqU
    have hh := hq hqU
    rw [hqf] at hh
    exact Bool.not_injective hh
  · rintro ⟨U,hU,ht,ha⟩
    refine ⟨(fun q : Angles => q-(sixty : Angles)) ⁻¹' U,hU.preimage (continuous_id.sub continuous_const),by simpa,?_⟩
    have hh := (measurePreserving_add_right angularMeasure (-(sixty : Angles))).quasiMeasurePreserving.ae (ha.and hf)
    filter_upwards [hh] with q hq hqU
    have hcol := hq.1 hqU
    have hflip := hq.2
    change s (q-(sixty : Angles))=b at hcol
    simpa only [←sub_eq_add_neg,sub_add_cancel,hcol] using hflip
lemma angleBoundary_shift {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (t : Angles) :
    t+(sixty : Angles)∈angleBoundary s ↔ t∈angleBoundary s := by
  simp only [angleBoundary,mem_compl_iff,mem_iUnion,not_exists]
  constructor
  · intro h b hb
    exact h (!b) ((angleEssential_shift hf t b).mpr hb)
  · intro h b hb
    apply h (!b)
    apply (angleEssential_shift hf t (!b)).mp
    simpa only [Bool.not_not] using hb
lemma angleBoundary_nonempty {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) : (angleBoundary s).Nonempty := by
  by_contra hn
  have hcov : (univ : Set Angles)⊆angleEssential s false∪angleEssential s true := by
    intro t _
    have ht : t∉angleBoundary s := fun h => hn ⟨t,h⟩
    simp only [angleBoundary,mem_compl_iff,not_not,mem_iUnion] at ht
    obtain ⟨b,hb⟩ := ht
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  have hzero := hcov (mem_univ (0:Angles))
  have hconst : ∃b,∀ᵐt∂angularMeasure,s t=b := by
    rcases hzero with h0|h0
    · have hs := isPreconnected_univ.subset_left_of_subset_union (angleEssential_open s false)
        (angleEssential_open s true) (angleEssential_disjoint s (by decide)) hcov ⟨0,mem_univ _,h0⟩
      exact ⟨false,(angleEssential_ae s false).mono fun t ht => ht (hs (mem_univ _))⟩
    · have hs := isPreconnected_univ.subset_left_of_subset_union (angleEssential_open s true)
        (angleEssential_open s false) (angleEssential_disjoint s (by decide))
        (by simpa only [union_comm] using hcov) ⟨0,mem_univ _,h0⟩
      exact ⟨true,(angleEssential_ae s true).mono fun t ht => ht (hs (mem_univ _))⟩
  obtain ⟨b,hb⟩ := hconst
  have hh : ∀ᵐt∂angularMeasure,False := by
    filter_upwards [hb,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hb,hf] with t ht ht' he
    rw [ht,ht'] at he
    cases b <;> cases he
  exact hh.exists.choose_spec
lemma sixAngle_add (i j : Fin 6) : sixAngle (i+j)=sixAngle i+sixAngle j := by
  induction j using Fin.induction with
  | zero => simp [sixAngle]
  | succ j hj =>
    have he : j.succ=(j.castSucc : Fin 6)+1 := by
      apply Fin.ext
      simp only [Fin.val_succ,Fin.val_add,Fin.val_castSucc,Fin.val_one]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [he,←add_assoc,sixAngle_step,sixAngle_step,hj]
    abel
lemma sixty_order : addOrderOf (sixty : Angles)=6 := by
  convert (AddCircle.addOrderOf_period_div (p:=2*Real.pi) (by norm_num : 0<(6:ℕ))) using 1
  congr 2
  dsimp [sixty]
  ring
lemma sixAngle_injective : Function.Injective sixAngle := by
  intro i j hij
  apply Fin.ext
  apply nsmul_injOn_Iio_addOrderOf (x := (sixty : Angles))
  · simpa only [sixty_order,mem_Iio] using i.isLt
  · simpa only [sixty_order,mem_Iio] using j.isLt
  · exact hij
def sixAngleHom : Fin 6 →+ Angles where
  toFun := sixAngle
  map_zero' := rfl
  map_add' := sixAngle_add
lemma sixAngle_sub (i j : Fin 6) : sixAngle (i-j)=sixAngle i-sixAngle j := sixAngleHom.map_sub i j
lemma angleBoundary_six {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) {t : Angles} (ht : t∈angleBoundary s)
    (j : Fin 6) : t+sixAngle j∈angleBoundary s := by
  have hh (n : ℕ) : t+n•(sixty : Angles)∈angleBoundary s := by
    induction n with
    | zero => simpa using ht
    | succ n ih =>
      simpa only [add_nsmul,one_nsmul,←add_assoc] using (angleBoundary_shift hf (t+n•(sixty : Angles))).mpr ih
  exact hh j.val
lemma six_antipodal_vertex_cover : ∀b : Fin 6 → Bool,
    (∀j,b (j+3)=b j) → (∀j,b j=true ∨ b (j+1)=true) →
      4≤(Finset.univ.filter fun j => b j=true).card := by decide
/-- Core finite obstruction behind the one-orbit boundary theorem. -/
lemma angleBoundary_one_orbit {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (B : Finset Angles)
    (hB : B.card≤6) (hanti : ∀t,t+(Real.pi : Angles)∈B ↔ t∈B)
    (hl : ∀t,t∉B → t+(sixty : Angles)∉B → ∃b,t∈angleEssential s b) :
    ∃t,angleBoundary s={u | ∃j : Fin 6,u=t+sixAngle j} := by
  classical
  obtain ⟨t,ht⟩ := angleBoundary_nonempty hf
  let O (q : Angles) : Finset Angles := Finset.univ.image (fun j : Fin 6 => q+sixAngle j)
  have hcard (q : Angles) (hq : q∈angleBoundary s) : 4≤(B∩O q).card := by
    let b : Fin 6 → Bool := fun j => decide (q+sixAngle j∈B)
    have ha (j) : b (j+3)=b j := by
      simp only [b,sixAngle_half,←add_assoc,hanti]
    have hc (j) : b j=true ∨ b (j+1)=true := by
      by_contra hn
      have hh : q+sixAngle j∉B ∧ q+sixAngle (j+1)∉B := by simpa only [b,decide_eq_true_eq,not_or] using hn
      obtain ⟨v,hv⟩ := hl (q+sixAngle j) hh.1 (by simpa only [sixAngle_step,←add_assoc] using hh.2)
      exact (angleBoundary_six hf hq j) (mem_iUnion.mpr ⟨v,hv⟩)
    have hcount := six_antipodal_vertex_cover b ha hc
    have hi : Function.Injective (fun j : Fin 6 => q+sixAngle j) := (add_right_injective q).comp sixAngle_injective
    have him : (Finset.univ.filter fun j => b j=true).image (fun j : Fin 6 => q+sixAngle j)=B∩O q := by
      ext u
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,b,decide_eq_true_eq,
        Finset.mem_inter,O]
      constructor
      · rintro ⟨j,hj,rfl⟩; exact ⟨hj,j,rfl⟩
      · rintro ⟨hu,j,rfl⟩; exact ⟨j,hu,rfl⟩
    rw [←him,Finset.card_image_of_injective _ hi]
    exact hcount
  refine ⟨t,Set.ext fun u => ?_⟩
  constructor
  · intro hu
    by_contra hn
    have hd : Disjoint (O t) (O u) := by
      apply Finset.disjoint_left.mpr
      intro q hqt hqu
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hqt
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hqu
      apply hn
      refine ⟨i-j,?_⟩
      rw [sixAngle_sub]
      have he : t+sixAngle i=u+sixAngle j := hi.trans hj.symm
      calc u = (u+sixAngle j)-sixAngle j := by abel
           _ = (t+sixAngle i)-sixAngle j := by rw [he]
           _ = t+(sixAngle i-sixAngle j) := by abel
    have hd' : Disjoint (B∩O t) (B∩O u) := hd.mono Finset.inter_subset_right Finset.inter_subset_right
    have hh := Finset.card_le_card (show (B∩O t)∪(B∩O u)⊆B from Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    rw [Finset.card_union_of_disjoint hd'] at hh
    have hct := hcard t ht
    have hcu := hcard u hu
    omega
  · rintro ⟨j,rfl⟩
    exact angleBoundary_six hf ht j
end EuclideanFiveColor
end

end OAI
