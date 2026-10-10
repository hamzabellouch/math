import OAI.Geometry.PlaneColoring.Exclusion
import OAI.Geometry.PlaneColoring.FourTransport

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma normalized_increment_endpoint_gap {l r a : ℝ} (hlr : l<r)
    {u δ : ℕ → ℝ} {v : ℝ} (hδ : ∀n,0<δ n)
    (hv : (a=l ∧ 0<v) ∨ (a=r ∧ v<0))
    (hu : Tendsto u atTop (𝓝 a))
    (hs : Tendsto (fun n => (u n-a)/δ n) atTop (𝓝 v)) :
    ∀ᶠn in atTop,u n∈Ioo l r := by
  rcases hv with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact positive_normalized_increment_enters_gap hlr hδ hv hu hs
  · filter_upwards [hu.eventually (lt_mem_nhds hlr),hs.eventually (gt_mem_nhds hv)] with n hn hp
    exact ⟨hn,sub_neg.mp ((div_neg_iff.mp hp).resolve_left (fun h => (not_lt_of_ge (hδ n).le) h.2)).1⟩
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_support_positive (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x)
    {s : Fin 3} (hs : s≠0) : 0<volume (fourSupport c hc x s) := by
  apply (four_realState_positive c hc hw hx hs).trans_le
  apply measure_mono_ae
  exact (ae_restrict_iff' (four_realState_measurable c hc x s)).mp
    (volume.restrict (fourRealState c hc x s)).support_mem_ae
lemma four_other_union (x : ℂ) {s : Fin 3} (hs : s≠0) :
    fourNonSingleton c hc x=fourSupport c hc x s∪fourSupport c hc x (if s=1 then 2 else 1) := by
  fin_cases s
  · exact (hs rfl).elim
  · rfl
  · exact Set.union_comm _ _
lemma four_endpoint_sequence_false (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FourCenter c (yn n)) (hx : FourCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) {δ : ℕ → ℝ} {H : RealPlane} (hδ : ∀n,0<δ n)
    (hdir : Tendsto (fun n => (δ n)⁻¹•Complex.equivRealProdCLM (yn n-x)) atTop (𝓝 H))
    {l r a : ℝ} (hlr : l<r) (haEnd : a=l ∨ a=r)
    (hgap : Ioo l r⊆(fourSupport c hc x 1∪fourSupport c hc x 2)ᶜ)
    {s : Fin 3} (hs : s≠0) (ha : a∈fourSupport c hc x s)
    (hHa : H.1*Real.cos a+H.2*Real.sin a≠0) : False := by
  classical
  let t : Fin 3 := if s=1 then 2 else 1
  have ht : t≠0 := by dsimp [t]; split <;> decide
  have hRaN := four_gap_shift_subset c hc hw hx hlr hgap
    (show a+sixty∈Icc (l+sixty) (r+sixty) from by rcases haEnd with rfl|rfl <;> constructor <;> linarith)
  have hRa : a+sixty∈fourSupport c hc x t := by
    change a+sixty∈fourNonSingleton c hc x at hRaN
    rw [four_other_union c hc x hs] at hRaN
    exact hRaN.resolve_left (four_support_no_sixty c hc hw hx hs ha)
  obtain ⟨b0,hb0,b1,hb1,hb0a,hb1a,hv01⟩ := exists_transportVelocity_lt
    (four_support_positive c hc hw hx ht) hHa
  have hp : ∃b b',b∈fourSupport c hc x t ∧ b'∈fourSupport c hc x t ∧
      Real.sin (b-a)≠0 ∧ Real.sin (b'-a)≠0 ∧
      ((a=l ∧ 0<transportVelocity H a b-transportVelocity H a b') ∨
       (a=r ∧ transportVelocity H a b-transportVelocity H a b'<0)) := by
    rcases haEnd with hal|har
    · exact ⟨b1,b0,hb1,hb0,hb1a,hb0a,Or.inl ⟨hal,sub_pos.mpr hv01⟩⟩
    · exact ⟨b0,b1,hb0,hb1,hb0a,hb1a,Or.inr ⟨har,sub_neg.mpr hv01⟩⟩
  obtain ⟨b,b',hb,hb',hab,hab',hvel⟩ := hp
  obtain ⟨bn,hbn,hbt⟩ := four_support_continuity c hc hw hyn hx hy ht hb'
  obtain ⟨dn,hdn,hdt⟩ := four_support_continuity c hc hw hyn hx hy ht hRa
  let Hn := fun n => Complex.equivRealProdCLM (yn n-x)
  have hH : Tendsto Hn atTop (𝓝 0) := by
    simpa only [sub_self,map_zero,Function.comp_def] using
      Complex.equivRealProdCLM.continuous.continuousAt.tendsto.comp (hy.sub_const x)
  let cn := fun n => (sumTransport hab (Hn n) (a,b)).1
  have hcn : Tendsto cn atTop (𝓝 a) := (sumTransport_tendsto hab hH tendsto_const_nhds).fst_nhds
  have hneg : Tendsto (fun n => -Hn n) atTop (𝓝 0) := by simpa only [neg_zero] using hH.neg
  let un := fun n => (sumTransport hab' (-Hn n) (cn n,bn n)).1
  have hun : Tendsto un atTop (𝓝 a) :=
    (sumTransport_tendsto hab' hneg (hcn.prodMk_nhds hbt)).fst_nhds
  have huGap : ∀ᶠn in atTop,un n∈Ioo l r := normalized_increment_endpoint_gap hlr hδ hvel hun
    (sumTransport_double_increment hab hab' hH hbt hδ hdir)
  obtain ⟨P,V,hP,hP0,hV,haV,K,hbranch⟩ := sumTransport_neighborhood hab
  have hcN : ∀ᶠn in atTop,cn n∈fourNonSingleton c hc (yn n) := by
    filter_upwards [hH.eventually (hP.mem_nhds hP0)] with n hn
    exact (four_support_transport c hc hw hx (hyn n) hs ha hb hab hV haV hbranch hn).1
  obtain ⟨P',V',hP',hP0',hV',haV',K',hbranch'⟩ := sumTransport_neighborhood hab'
  have hcNot : ∀ᶠn in atTop,cn n∉fourSupport c hc (yn n) s := by
    filter_upwards [hneg.eventually (hP'.mem_nhds hP0'),
      (hcn.prodMk_nhds hbt).eventually (hV'.mem_nhds haV'),huGap] with n hn hqn hgn hcu
    have hcenter : Complex.equivRealProdCLM (x-yn n)= -Hn n := by
      dsimp [Hn]
      rw [← map_neg,neg_sub]
    have htr := four_support_transport_general c hc hw (hyn n) hx hs hab' hcu (hbn n)
      hV' hqn hbranch' (hcenter.symm ▸ hn)
    rw [hcenter] at htr
    exact hgap hgn htr.1
  have hcT : ∀ᶠn in atTop,cn n∈fourSupport c hc (yn n) t := by
    filter_upwards [hcN,hcNot] with n hn hnot
    rw [four_other_union c hc (yn n) hs] at hn
    exact hn.resolve_left hnot
  let vn := fun n => if h : cn n∈fourSupport c hc (yn n) t then cn n
    else (four_support_nonempty c hc hw (hyn n) ht).choose
  have hvn : ∀n,vn n∈fourSupport c hc (yn n) t := by
    intro n
    dsimp [vn]
    split
    · assumption
    · exact (four_support_nonempty c hc hw (hyn n) ht).choose_spec
  have hvlim : Tendsto vn atTop (𝓝 a) := hcn.congr' (by
    filter_upwards [hcT] with n hn
    simp only [vn,dite_eq_left hn])
  exact four_support_sequence_no_unit c hc hw hyn hx hy ht hvlim hdt hvn hdn (direction_sixty_unit_real a)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma gap_endpoint_nonorthogonal {H : ℝ×ℝ} (hH : H≠0) {a b : ℝ}
    (hab : 0<b-a) (hab' : b-a<Real.pi) :
    H.1*Real.cos a+H.2*Real.sin a≠0 ∨ H.1*Real.cos b+H.2*Real.sin b≠0 := by
  by_contra! h
  have hs := (Real.sin_pos_of_pos_of_lt_pi hab hab').ne'
  have h1 : H.1*Real.sin (b-a)=0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin b*h.1-Real.sin a*h.2
  have h2 : H.2*Real.sin (b-a)=0 := by
    rw [Real.sin_sub]
    linear_combination -Real.cos b*h.1+Real.cos a*h.2
  apply hH
  exact Prod.ext ((mul_eq_zero.mp h1).resolve_right hs) ((mul_eq_zero.mp h2).resolve_right hs)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma triple_subset_pair {α : Type*} [DecidableEq α] {S : Finset α} {a b d : α}
    (hS : S.card ≤ 2) (hsub : S ⊆ {a,b,d}) :
    S ⊆ {a,b} ∨ S ⊆ {a,d} ∨ S ⊆ {b,d} := by
  by_cases hab : a=b
  · subst b
    exact Or.inr (Or.inl (by simpa using hsub))
  by_cases ha : a∈S
  · by_cases hb : b∈S
    · left
      intro x hx
      by_contra hn
      have hxne : x≠a ∧ x≠b := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hn
      have : 3 ≤ S.card := by
        have hh : ({a,b,x} : Finset α) ⊆ S := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨ha,hb,hx⟩
        have hc := Finset.card_le_card hh
        simpa [hab,hxne.1.symm,hxne.2.symm] using hc
      omega
    · right; left
      intro x hx
      have := hsub hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at this ⊢
      rcases this with h|h|h
      · exact Or.inl h
      · exact False.elim (hb (h ▸ hx))
      · exact Or.inr h
  · right; right
    intro x hx
    exact (Finset.mem_insert.mp (hsub hx)).resolve_left (fun h => ha (h ▸ hx))
lemma triangle_binary (c : ℂ → Fin 5) (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {a b d i j : Fin 5}
    (hab : TransitionEdge c a b x) (had : TransitionEdge c a d x) (hbd : TransitionEdge c b d x)
    (hcomp : Finset.univ\{a,b,d}={i,j}) : BinaryCenter c hc x i j := by
  filter_upwards [palette_cardinality c hc hw x,edge_palette_not_pair c hc hw hab,
    edge_palette_not_pair c hc hw had,edge_palette_not_pair c hc hw hbd] with t ht hab had hbd
  by_contra hn
  have hnot : i∉palette c hc x t ∧ j∉palette c hc x t := by
    simpa only [mem_palette,not_or] using hn
  have hsub : palette c hc x t ⊆ {a,b,d} := by
    intro s hs
    by_contra hns
    have : s∈({i,j} : Finset (Fin 5)) := by rw [← hcomp]; simp [hns]
    simp only [Finset.mem_insert,Finset.mem_singleton] at this
    rcases this with rfl|rfl
    · exact hnot.1 hs
    · exact hnot.2 hs
  rcases triple_subset_pair ht.2 hsub with h|h|h
  · exact hab h
  · exact had h
  · exact hbd h
lemma triangle_centers_separated (c : ℂ → Fin 5) (hc : Measurable c) (hw : WeakColoring 5 c)
    (a b d i j : Fin 5) (hcomp : Finset.univ\{a,b,d}={i,j}) :
    ∃ δ>0, ∀ x z : ℂ, TransitionEdge c a b x → TransitionEdge c a d x → TransitionEdge c b d x →
      TransitionEdge c a b z → TransitionEdge c a d z → TransitionEdge c b d z → x≠z → δ≤dist x z := by
  obtain ⟨δ,hδ,hsep⟩ := binary_centers_separated c hc hw
  exact ⟨δ,hδ,fun x z h1 h2 h3 h4 h5 h6 hne => hsep x z i j
    (triangle_binary c hc hw h1 h2 h3 hcomp) (triangle_binary c hc hw h4 h5 h6 hcomp) hne⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionRatio_mono {i j : Fin k} {x y : ℂ} {R S : ℝ}
    (hB : Metric.ball x R ⊆ Metric.ball y S) (h : ℂ) :
    transitionRatio c i j x R h ≤ transitionRatio c i j y S h := by
  apply ENNReal.div_le_div_right
  exact measure_mono (fun _ hq => ⟨hB hq.1,hq.2⟩)
lemma transitionEdge_closed (i j : Fin k) : IsClosed {x | TransitionEdge c i j x} := by
  apply isClosed_of_closure_subset
  intro x hx
  have hne : i≠j := by
    obtain ⟨y,_,hy⟩ := mem_closure_iff.mp hx Set.univ isOpen_univ (mem_univ _)
    exact hy.1
  refine ⟨hne,fun R hR => ?_⟩
  obtain ⟨y,hyB,hy⟩ := mem_closure_iff.mp hx (Metric.ball x (R/2)) Metric.isOpen_ball
    (Metric.mem_ball_self (by linarith))
  have hB : Metric.ball y (R/2) ⊆ Metric.ball x R := by
    intro z hz
    have ht := dist_triangle z y x
    have hz' : dist z y < R/2 := hz
    have hy' : dist y x < R/2 := hyB
    exact lt_of_le_of_lt ht (by linarith)
  exact (hy.2 (R/2) (by linarith)).trans_le (limsup_le_limsup
    (Eventually.of_forall (transitionRatio_mono c hB)))
lemma missing_edge_lim (i j : Fin k) (hne : i≠j) {x : ℂ}
    (he : ¬TransitionEdge c i j x) : ∃ R>0,
    Tendsto (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
  obtain ⟨R,hR,hr⟩ : ∃ R, 0<R ∧ ¬0<limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) := by
    have hh : ¬∀ R, 0<R → 0<limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ)) :=
      fun hh => he ⟨hne,hh⟩
    push Not at hh
    exact ⟨hh.choose,hh.choose_spec.1,not_lt.mpr hh.choose_spec.2⟩
  refine ⟨R,hR,?_⟩
  have hs : limsup (transitionRatio c i j x R) (𝓝[≠] (0:ℂ))=0 := le_antisymm (not_lt.mp hr) (bot_le)
  exact tendsto_of_le_liminf_of_limsup_le (bot_le) hs.le
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
include hc
lemma four_normalized_sequence_false (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FourCenter c (yn n)) (hx : FourCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) {δ : ℕ → ℝ} {H : RealPlane} (hδ : ∀n,0<δ n) (hH : H≠0)
    (hdir : Tendsto (fun n => (δ n)⁻¹•Complex.equivRealProdCLM (yn n-x)) atTop (𝓝 H)) : False := by
  obtain ⟨a,b,ha,hb,hab,hab',hgap⟩ := four_gap_exists c hc hw hx
  have hp : b-a<Real.pi := hab'.trans_lt (by dsimp [sixty]; linarith [Real.pi_pos])
  rcases gap_endpoint_nonorthogonal hH (sub_pos.mpr hab) hp with hda|hdb
  · rcases ha with ha|ha
    · exact four_endpoint_sequence_false c hc hw hyn hx hy hδ hdir hab (Or.inl rfl) hgap (by decide) ha hda
    · exact four_endpoint_sequence_false c hc hw hyn hx hy hδ hdir hab (Or.inl rfl) hgap (by decide) ha hda
  · rcases hb with hb|hb
    · exact four_endpoint_sequence_false c hc hw hyn hx hy hδ hdir hab (Or.inr rfl) hgap (by decide) hb hdb
    · exact four_endpoint_sequence_false c hc hw hyn hx hy hδ hdir hab (Or.inr rfl) hgap (by decide) hb hdb
lemma four_sequence_no_accumulation (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FourCenter c (yn n)) (hx : FourCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) (hne : ∀n,yn n≠x) : False := by
  let Hn := fun n => Complex.equivRealProdCLM (yn n-x)
  have hn : ∀n,Hn n≠0 := by
    intro n h
    apply hne n
    apply sub_eq_zero.mp
    exact Complex.equivRealProdCLM.injective (h.trans (map_zero _).symm)
  let δ := fun n => ‖Hn n‖
  have hδ : ∀n,0<δ n := fun n => norm_pos_iff.mpr (hn n)
  have hd : ∀n,(δ n)⁻¹•Hn n∈Metric.sphere 0 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (𝕜 := ℝ) (hn n)
  obtain ⟨H,hH,φ,hφ,hlim⟩ := (isCompact_sphere (0 : RealPlane) 1).tendsto_subseq hd
  have hH0 : H≠0 := by
    rw [mem_sphere_zero_iff_norm] at hH
    intro hz
    simp only [hz,norm_zero] at hH
    norm_num at hH
  exact four_normalized_sequence_false c hc hw (fun n => hyn (φ n)) hx
    (hy.comp hφ.tendsto_atTop) (fun n => hδ (φ n)) hH0 hlim
omit hc in
lemma fourCenter_closed : IsClosed {x | FourCenter c x} :=
  (transitionEdge_closed c 0 1).inter ((transitionEdge_closed c 1 2).inter
    ((transitionEdge_closed c 2 3).inter (transitionEdge_closed c 3 0)))
lemma fourCenter_discrete (hw : WeakColoring 5 c) : IsDiscrete {x | FourCenter c x} := by
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_of_noAccPts
  intro x hx ha
  obtain ⟨yn,hyn,hy⟩ := mem_closure_iff_seq_limit.mp
    (accPt_principal_iff_clusterPt.mp ha).mem_closure
  exact four_sequence_no_accumulation c hc hw (fun n => (hyn n).1) hx hy
    (fun n => by simpa only [mem_singleton_iff] using (hyn n).2)
lemma fourCenter_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩{x | FourCenter c x}).Finite :=
  (hK.inter_right (fourCenter_closed c)).finite ((fourCenter_discrete c hc hw).mono inter_subset_right)

end EuclideanFiveColor

end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (e : Equiv.Perm (Fin k))
lemma weak_relabel (hw : WeakColoring k c) : WeakColoring k (e ∘ c) := by
  refine ⟨(measurable_of_finite e).comp_aemeasurable hw.1,?_⟩
  exact hw.2.mono fun p hp h => hp (e.injective h)
lemma transitionSet_relabel (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    transitionSet (e ∘ c) (e i) (e j) x R h=transitionSet c i j x R h := by
  ext q
  simp only [transitionSet,Set.mem_ofPred_eq,Function.comp_apply,Equiv.apply_eq_iff_eq]
lemma transitionEdge_relabel (i j : Fin k) (x : ℂ) :
    TransitionEdge (e ∘ c) (e i) (e j) x ↔ TransitionEdge c i j x := by
  have he : transitionRatio (e ∘ c) (e i) (e j) x=transitionRatio c i j x := by
    funext R h
    unfold transitionRatio
    rw [transitionSet_relabel]
  simp only [TransitionEdge,he,ne_eq,Equiv.apply_eq_iff_eq]
lemma transitionEdge_symm {i j : Fin k} {x : ℂ} (h : TransitionEdge c i j x) :
    TransitionEdge c j i x := by
  have he : transitionRatio c j i x=transitionRatio c i j x := by
    funext R z
    have hs : transitionSet c j i x R z=transitionSet c i j x R z := by
      ext q
      simp only [transitionSet,Set.mem_ofPred_eq,or_comm]
    change volume _ / _ = volume _ / _
    rw [hs]
  exact ⟨h.1.symm,by simpa only [he] using h.2⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def ThreeCenter (x : ℂ) : Prop :=
  TransitionEdge c 0 1 x ∧ TransitionEdge c 0 2 x ∧ TransitionEdge c 1 2 x
lemma threeCenter_closed : IsClosed {x | ThreeCenter c x} :=
  (transitionEdge_closed c 0 1).inter ((transitionEdge_closed c 0 2).inter (transitionEdge_closed c 1 2))
include hc in
lemma three_sequence_no_accumulation (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,ThreeCenter c (yn n)) (hx : ThreeCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) (hne : ∀n,yn n≠x) : False := by
  obtain ⟨δ,hδ,hsep⟩ := triangle_centers_separated c hc hw 0 1 2 3 4 (by decide)
  have hd : Tendsto (fun n => dist (yn n) x) atTop (𝓝 0) := by
    simpa only [dist_self] using hy.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
  have hev : ∀ᶠn in atTop,dist (yn n) x<δ := hd.eventually (gt_mem_nhds hδ)
  obtain ⟨n,hn⟩ := hev.exists
  exact (not_lt_of_ge (hsep (yn n) x (hyn n).1 (hyn n).2.1 (hyn n).2.2 hx.1 hx.2.1 hx.2.2 (hne n))) hn
include hc in
lemma threeCenter_discrete (hw : WeakColoring 5 c) : IsDiscrete {x | ThreeCenter c x} := by
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_of_noAccPts
  intro x hx ha
  obtain ⟨yn,hyn,hy⟩ := mem_closure_iff_seq_limit.mp
    (accPt_principal_iff_clusterPt.mp ha).mem_closure
  exact three_sequence_no_accumulation c hc hw (fun n => (hyn n).1) hx hy
    (fun n => by simpa only [mem_singleton_iff] using (hyn n).2)
include hc in
lemma threeCenter_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩{x | ThreeCenter c x}).Finite :=
  (hK.inter_right (threeCenter_closed c)).finite ((threeCenter_discrete c hc hw).mono inter_subset_right)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def FiveCenter (x : ℂ) : Prop := ∀i : Fin 5,TransitionEdge c i (i+1) x
lemma five_palette_admissible (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) :
    ∀ᵐt∂angularMeasure,FiveAdmissible (palette c hc x t) := by
  filter_upwards [palette_nonempty c hc x,palette_cardinality c hc hw x,
    ae_all_iff.mpr (fun i => edge_palette_not_pair c hc hw (hx i))] with t hn hs he
  exact ⟨hn,hs.2,he⟩
def fiveState (x : ℂ) (t : Angles) : Fin 5 := fiveCanonical (palette c hc x t)
lemma palette_eq_measurable (x : ℂ) (p : Finset (Fin 5)) :
    MeasurableSet {t | palette c hc x t=p} := by
  simp only [Finset.ext_iff,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i∈p
  · simpa only [hi,iff_true,mem_palette,Set.ofPred_mem_eq] using paletteSet_measurable c hc x i
  · simpa only [hi,iff_false,mem_palette,← Set.mem_compl_iff,Set.ofPred_mem_eq] using (paletteSet_measurable c hc x i).compl
lemma fiveState_measurable (x : ℂ) : Measurable (fiveState c hc x) := by
  exact Measurable.ite (palette_eq_measurable c hc x _) measurable_const
    (Measurable.ite (palette_eq_measurable c hc x _) measurable_const
      (Measurable.ite (palette_eq_measurable c hc x _) measurable_const
        (Measurable.ite (palette_eq_measurable c hc x _) measurable_const measurable_const)))
lemma fiveState_diag (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) :
    ∀ᵐt∂angularMeasure,palette c hc x t=fiveDiag (fiveState c hc x t) :=
  (five_palette_admissible c hc hw hx).mono fun _ ht => five_admissible_diag _ ht
lemma fiveState_represents (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) (i : Fin 5) :
    RealState hc x {t : ℝ | fiveState c hc x (t : Angles)=i} (fiveDiag i) := by
  refine ⟨measurableSet_eq_fun ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) measurable_const,?_⟩
  intro j hj
  filter_upwards [angleMk_quasiMeasurePreserving.ae (fiveState_diag c hc hw hx)] with t ht hti
  change fiveState c hc x (t : Angles)=i at hti
  apply (mem_palette c hc x (t : Angles) j).mp
  rw [ht,hti]
  exact hj
lemma fiveState_adj (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) :
    ∀ᵐt∂angularMeasure,fiveAdj (fiveState c hc x t) (fiveState c hc x (t+(sixty : Angles))) := by
  have hs := fiveState_diag c hc hw hx
  filter_upwards [hs,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hs,
    palette_sixty_disjoint c hc hw x] with t ht hu hd
  apply (five_diag_disjoint _ _).mp
  change Disjoint (palette c hc x t) (palette c hc x (t+(sixty : Angles))) at hd
  rwa [ht,hu] at hd
end EuclideanFiveColor
end

end OAI
