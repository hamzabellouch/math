import OAI.Geometry.PlaneColoring.FiveSupport

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma five_ae_mem_support (x : ℂ) :
    ∀ᵐt : ℝ∂volume,t∈fiveSupport c hc x (fiveState c hc x (t : Angles)) :=
  ae_state_support ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable)
lemma five_real_diag (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) :
    ∀ᵐt : ℝ∂volume,palette c hc x (t : Angles)=fiveDiag (fiveState c hc x (t : Angles)) :=
  angleMk_quasiMeasurePreserving.ae (fiveState_diag c hc hw hx)
lemma five_local_palette (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a : ℝ} {k : Fin 5}
    (hk : ∀i,a∈fiveSupport c hc x i → k∈fiveDiag i) :
    ∃V, IsOpen V ∧ a∈V ∧ ∀ᵐt : ℝ∂volume,t∈V → (t : Angles)∈paletteSet c hc x k := by
  obtain ⟨V,hV,ha,hkV⟩ := stateSupport_local_pred
    ((fiveState_measurable c hc x).comp angleMk_quasiMeasurePreserving.measurable) hk
  refine ⟨V,hV,ha,?_⟩
  filter_upwards [hkV,five_real_diag c hc hw hx] with t ht hd htv
  apply (mem_palette c hc x (t : Angles) k).mp
  rw [hd]
  exact ht htv
lemma five_endpoint_no_common (hw : WeakColoring 5 c) {x : ℂ} (hx : FiveCenter c x) {a b : ℝ}
    (hab : Real.sin (b-a)≠0) (hy : FiveCenter c (x+direction (a : Angles)+direction (b : Angles))) :
    ∀k : Fin 5,∃i,a∈fiveSupport c hc x i ∧ k∉fiveDiag i := by
  intro k
  by_contra! h
  obtain ⟨V,hV,ha,hpal⟩ := five_local_palette c hc hw hx h
  obtain ⟨U,hU,hyU,hnull⟩ := palette_open_exclusion c hc hw hab hV ha hpal
  exact transitionEdge_no_open_exclusion c (hy k) hU hyU hnull
lemma five_limit_contact {x : ℂ} {an : ℕ → ℝ} {a : ℝ} (ha : Tendsto an atTop (𝓝 a))
    (hn : ∀n,∀k : Fin 5,∃i,an n∈fiveSupport c hc x i ∧ k∉fiveDiag i) :
    ∃i,a∈fiveSupport c hc x i ∧ a∈fiveSupport c hc x (i+1) := by
  have hall : ∀k : Fin 5,∃i,a∈fiveSupport c hc x i ∧ k∉fiveDiag i := fun k =>
    finite_closed_family_no_common_limit (fun _ => Measure.isClosed_support) ha (fun n => hn n k)
  have hnList : (fiveSupportList c hc x a).Nonempty := by
    obtain ⟨i,hi⟩ := five_support_cover c hc x a
    exact ⟨i,(mem_fiveSupportList _ _ _ _ _).mpr hi⟩
  have hp : ∀k,∃i∈fiveSupportList c hc x a,k∉fiveDiag i := by
    intro k; obtain ⟨i,hi,hk⟩ := hall k
    exact ⟨i,(mem_fiveSupportList _ _ _ _ _).mpr hi,hk⟩
  obtain ⟨i,hi,hi'⟩ := FiveComb.adjacent_oriented _ (five_no_common_adj _ hnList hp)
  exact ⟨i,(mem_fiveSupportList _ _ _ _ _).mp hi,(mem_fiveSupportList _ _ _ _ _).mp hi'⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology
namespace EuclideanFiveColor
lemma chord_angles_sum {z : ℂ} (hz : ‖z‖≤2) :
    Complex.exp (((z.arg-Real.arccos (‖z‖/2) : ℝ) : ℂ)*Complex.I)+
      Complex.exp (((z.arg+Real.arccos (‖z‖/2) : ℝ) : ℂ)*Complex.I)=z := by
  have hc := Real.cos_arccos (x := ‖z‖/2) (by have := norm_nonneg z; linarith) (by linarith)
  have hre := Complex.norm_mul_cos_arg z
  have him := Complex.norm_mul_sin_arg z
  rw [Complex.exp_mul_I,Complex.exp_mul_I]
  apply Complex.ext
  · simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,
      Complex.cos_ofReal_re,Complex.sin_ofReal_re,Complex.sin_ofReal_im,mul_zero,
      sub_zero,mul_one]
    rw [Real.cos_sub,Real.cos_add,hc]
    nlinarith
  · simp only [Complex.add_im,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.cos_ofReal_im,Complex.sin_ofReal_re,Complex.sin_ofReal_im,mul_zero,
      zero_add,add_zero,mul_one]
    rw [Real.sin_sub,Real.sin_add,hc]
    nlinarith
lemma chord_angles_nonparallel {r t : ℝ} (hr : 0<r) (hr2 : r<2) :
    Real.sin ((t+Real.arccos (r/2))-(t-Real.arccos (r/2)))≠0 := by
  have ha := Real.arccos_pos.mpr (show r/2<1 by linarith)
  have hb := Real.arccos_lt_pi_div_two.mpr (show 0<r/2 by linarith)
  exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
lemma chord_sequence_lifts {z : ℕ → ℂ} (hz : Tendsto z atTop (𝓝 0))
    (hne : ∀n,z n≠0) (hsmall : ∀n,‖z n‖<2) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ t : ℝ,∃ a b : ℕ → ℝ,
      Tendsto a atTop (𝓝 (t-Real.pi/2)) ∧ Tendsto b atTop (𝓝 (t+Real.pi/2)) ∧
      (∀n,Complex.exp ((a n : ℂ)*Complex.I)+Complex.exp ((b n : ℂ)*Complex.I)=z (φ n)) ∧
      ∀n,Real.sin (b n-a n)≠0 := by
  obtain ⟨t,_ht,φ,hφ,harg⟩ := (isCompact_Icc : IsCompact (Icc (-Real.pi) Real.pi)).tendsto_subseq
    (fun n => ⟨(Complex.neg_pi_lt_arg (z n)).le,Complex.arg_le_pi (z n)⟩)
  have hn : Tendsto (fun n => ‖z (φ n)‖/2) atTop (𝓝 0) := by
    simpa only [Function.comp_def,norm_zero,zero_div] using ((hz.comp hφ.tendsto_atTop).norm.div_const 2)
  have hac : Tendsto (fun n => Real.arccos (‖z (φ n)‖/2)) atTop (𝓝 (Real.pi/2)) := by
    simpa only [Function.comp_def,Real.arccos_zero] using Real.continuous_arccos.continuousAt.tendsto.comp hn
  refine ⟨φ,hφ,t,(fun n => (z (φ n)).arg-Real.arccos (‖z (φ n)‖/2)),
    (fun n => (z (φ n)).arg+Real.arccos (‖z (φ n)‖/2)),harg.sub hac,harg.add hac,?_,?_⟩
  · exact fun n => chord_angles_sum (hsmall (φ n)).le
  · exact fun n => chord_angles_nonparallel (norm_pos_iff.mpr (hne (φ n))) (hsmall (φ n))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
include hc in
lemma five_sequence_small_no_accumulation (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FiveCenter c (yn n)) (hx : FiveCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) (hne : ∀n,yn n≠x) (hsmall : ∀n,‖yn n-x‖<2) : False := by
  obtain ⟨φ,hφ,t,a,b,ha,hb,hs,hab⟩ := chord_sequence_lifts
    (by simpa only [sub_self] using hy.sub_const x) (fun n => sub_ne_zero.mpr (hne n)) hsmall
  have hcSum (n : ℕ) : x+direction (a n : Angles)+direction (b n : Angles)=yn (φ n) := by
    rw [direction_real,direction_real,Circle.coe_exp,Circle.coe_exp,add_assoc,hs]
    abel
  have haC : ∀n,∀k : Fin 5,∃i,a n∈fiveSupport c hc x i ∧ k∉fiveDiag i := by
    intro n
    apply five_endpoint_no_common c hc hw hx (hab n)
    rw [hcSum]; exact hyn _
  have hbC : ∀n,∀k : Fin 5,∃i,b n∈fiveSupport c hc x i ∧ k∉fiveDiag i := by
    intro n
    apply five_endpoint_no_common c hc hw hx
    · rw [show a n-b n=-(b n-a n) by ring,Real.sin_neg]
      exact neg_ne_zero.mpr (hab n)
    · rw [add_right_comm,hcSum]; exact hyn _
  obtain ⟨i,hi,hi'⟩ := five_limit_contact c hc ha haC
  obtain ⟨j,hj,hj'⟩ := five_limit_contact c hc hb hbC
  exact five_opposite_contacts_false c hc hw hx (by dsimp [sixty]; ring) hi hi' hj hj'
include hc in
lemma five_sequence_no_accumulation (hw : WeakColoring 5 c)
    {yn : ℕ → ℂ} {x : ℂ} (hyn : ∀n,FiveCenter c (yn n)) (hx : FiveCenter c x)
    (hy : Tendsto yn atTop (𝓝 x)) (hne : ∀n,yn n≠x) : False := by
  have hsmall : ∀ᶠn in atTop,‖yn n-x‖<2 := by
    have hn : Tendsto (fun n => ‖yn n-x‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using (hy.sub_const x).norm
    exact hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<2))
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsmall
  exact five_sequence_small_no_accumulation c hc hw (fun n => hyn (n+N)) hx
    (hy.comp (tendsto_add_atTop_nat N)) (fun n => hne (n+N)) (fun n => hN (n+N) (Nat.le_add_left _ _))
lemma fiveCenter_closed : IsClosed {x | FiveCenter c x} := by
  change IsClosed {x | ∀i : Fin 5,TransitionEdge c i (i+1) x}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => transitionEdge_closed c i (i+1)
include hc in
lemma fiveCenter_discrete (hw : WeakColoring 5 c) : IsDiscrete {x | FiveCenter c x} := by
  apply isDiscrete_iff_discreteTopology.mpr
  apply discreteTopology_of_noAccPts
  intro x hx ha
  obtain ⟨yn,hyn,hy⟩ := mem_closure_iff_seq_limit.mp
    (accPt_principal_iff_clusterPt.mp ha).mem_closure
  exact five_sequence_no_accumulation c hc hw (fun n => (hyn n).1) hx hy
    (fun n => by simpa only [mem_singleton_iff] using (hyn n).2)
include hc in
lemma fiveCenter_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩{x | FiveCenter c x}).Finite :=
  (hK.inter_right (fiveCenter_closed c)).finite ((fiveCenter_discrete c hc hw).mono inter_subset_right)
end EuclideanFiveColor
end

noncomputable section
open Set
namespace EuclideanFiveColor
lemma cycle_standard_permutation {G : SimpleGraph (Fin 5)} {v : Fin 5}
    {p : G.Walk v v} (hp : p.IsCycle) : ∃e : Equiv.Perm (Fin 5),
    (G.Adj (e 0) (e 1) ∧ G.Adj (e 0) (e 2) ∧ G.Adj (e 1) (e 2)) ∨
    (G.Adj (e 0) (e 1) ∧ G.Adj (e 1) (e 2) ∧ G.Adj (e 2) (e 3) ∧ G.Adj (e 3) (e 0)) ∨
    (∀i : Fin 5,G.Adj (e i) (e (i+1))) := by
  have hl := hp.three_le_length
  have hinj : Function.Injective (fun i : Fin p.length => p.getVert i) := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (by change i.val≤p.length-1; omega)
      (by change j.val≤p.length-1; omega) h
  have hle : p.length≤5 := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE hle)
    (fun i : Fin p.length => p.getVert i) (Fin.castLE_injective hle) hinj
  have hem (n : ℕ) (hn : n<p.length) : e ⟨n,lt_of_lt_of_le hn hle⟩=p.getVert n := he ⟨n,hn⟩
  have h0 : e 0=p.getVert 0 := hem 0 (by omega)
  have h1 : e 1=p.getVert 1 := hem 1 (by omega)
  have h2 : e 2=p.getVert 2 := hem 2 (by omega)
  have h01 : G.Adj (e 0) (e 1) := by rw [h0,h1]; exact p.adj_getVert_succ (by omega)
  have h12 : G.Adj (e 1) (e 2) := by rw [h1,h2]; exact p.adj_getVert_succ (by omega)
  refine ⟨e,?_⟩
  rcases (by omega : p.length=3 ∨ p.length=4 ∨ p.length=5) with hL|hL|hL
  · left
    refine ⟨h01,?_,h12⟩
    have h20 := p.adj_getVert_succ (i := 2) (by omega)
    have hlast : p.getVert 3=p.getVert 0 := by simpa only [hL,SimpleGraph.Walk.getVert_zero] using p.getVert_length
    rw [hlast,← h2,← h0] at h20
    exact h20.symm
  · right; left
    have h3 : e 3=p.getVert 3 := hem 3 (by omega)
    refine ⟨h01,h12,?_,?_⟩
    · rw [h2,h3]; exact p.adj_getVert_succ (by omega)
    · have h30 := p.adj_getVert_succ (i := 3) (by omega)
      have hlast : p.getVert 4=p.getVert 0 := by simpa only [hL,SimpleGraph.Walk.getVert_zero] using p.getVert_length
      rwa [hlast,← h3,← h0] at h30
  · right; right
    have h3 : e 3=p.getVert 3 := hem 3 (by omega)
    have h4 : e 4=p.getVert 4 := hem 4 (by omega)
    have h23 : G.Adj (e 2) (e 3) := by rw [h2,h3]; exact p.adj_getVert_succ (by omega)
    have h34 : G.Adj (e 3) (e 4) := by rw [h3,h4]; exact p.adj_getVert_succ (by omega)
    have h40 : G.Adj (e 4) (e 0) := by
      have h40 := p.adj_getVert_succ (i := 4) (by omega)
      have hlast : p.getVert 5=p.getVert 0 := by simpa only [hL,SimpleGraph.Walk.getVert_zero] using p.getVert_length
      rwa [hlast,← h4,← h0] at h40
    intro i
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
    · exact h34
    · exact h40
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
def transitionGraph (x : ℂ) : SimpleGraph (Fin 5) where
  Adj i j := TransitionEdge c i j x
  symm := ⟨fun _ _ h => transitionEdge_symm c h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def CyclicCore : Set ℂ := {x | ¬(transitionGraph c x).IsAcyclic}
def StandardCore (e : Equiv.Perm (Fin 5)) : Set ℂ :=
  {x | ThreeCenter (e.symm ∘ c) x ∨ FourCenter (e.symm ∘ c) x ∨ FiveCenter (e.symm ∘ c) x}
lemma transitionEdge_unlabel (e : Equiv.Perm (Fin 5)) (i j : Fin 5) (x : ℂ) :
    TransitionEdge (e.symm ∘ c) i j x ↔ TransitionEdge c (e i) (e j) x := by
  simpa only [Equiv.symm_apply_apply] using transitionEdge_relabel c e.symm (e i) (e j) x
lemma cyclicCore_subset_standard : CyclicCore c ⊆ ⋃e,StandardCore c e := by
  intro x hx
  change ¬∀v (p : (transitionGraph c x).Walk v v),¬p.IsCycle at hx
  push Not at hx
  obtain ⟨v,p,hp⟩ := hx
  obtain ⟨e,he⟩ := cycle_standard_permutation hp
  refine mem_iUnion.mpr ⟨e,?_⟩
  change ThreeCenter (e.symm ∘ c) x ∨ FourCenter (e.symm ∘ c) x ∨ FiveCenter (e.symm ∘ c) x
  simp only [ThreeCenter,FourCenter,FiveCenter,transitionEdge_unlabel]
  exact he
lemma cyclicCore_closed : IsClosed (CyclicCore c) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hx' : (transitionGraph c x).IsAcyclic := not_not.mp hx
  have he : ∀i j : Fin 5,∀ᶠ y in 𝓝 x,
      TransitionEdge c i j y → TransitionEdge c i j x := by
    intro i j
    by_cases hij : TransitionEdge c i j x
    · exact Filter.Eventually.of_forall fun _ _ => hij
    · have ho := (transitionEdge_closed c i j).isOpen_compl.mem_nhds hij
      exact Filter.Eventually.mono ho fun _ hy h => False.elim (hy h)
  have hall : ∀ᶠ y in 𝓝 x,∀i j : Fin 5,
      TransitionEdge c i j y → TransitionEdge c i j x :=
    (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (he i))
  filter_upwards [hall] with y hy
  change ¬¬(transitionGraph c y).IsAcyclic
  exact not_not.mpr (hx'.anti (fun {i j} h => hy i j h))
lemma standardCore_closed (e : Equiv.Perm (Fin 5)) : IsClosed (StandardCore c e) :=
  (threeCenter_closed (e.symm ∘ c)).union
    ((fourCenter_closed (e.symm ∘ c)).union (fiveCenter_closed (e.symm ∘ c)))
include hc in
lemma standardCore_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K)
    (e : Equiv.Perm (Fin 5)) : (K∩StandardCore c e).Finite := by
  have hc' : Measurable (e.symm ∘ c) := (measurable_of_finite e.symm).comp hc
  have hw' := weak_relabel c e.symm hw
  exact ((threeCenter_compact_finite _ hc' hw' hK).union
    ((fourCenter_compact_finite _ hc' hw' hK).union
      (fiveCenter_compact_finite _ hc' hw' hK))).subset (by
        intro x hx
        rcases hx.2 with h|h|h
        · exact Or.inl ⟨hx.1,h⟩
        · exact Or.inr (Or.inl ⟨hx.1,h⟩)
        · exact Or.inr (Or.inr ⟨hx.1,h⟩))
include hc in
lemma cyclicCore_compact_finite (hw : WeakColoring 5 c) {K : Set ℂ} (hK : IsCompact K) :
    (K∩CyclicCore c).Finite := by
  have hf : (⋃e,K∩StandardCore c e).Finite := finite_iUnion fun e =>
    standardCore_compact_finite c hc hw hK e
  apply hf.subset
  intro x hx
  obtain ⟨e,he⟩ := mem_iUnion.mp (cyclicCore_subset_standard c hx.2)
  exact mem_iUnion.mpr ⟨e,hx.1,he⟩
end EuclideanFiveColor
end

end OAI
