import OAI.Analysis.TreePotential.SegmentDual

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

def treeNode (h : ℕ) (s : Tree h) : Node := ⟨h,⟨s.val,s.property.trans (Nat.le_succ h)⟩⟩

def rootSegment (h : ℕ) (s : Tree h) : Segment :=
  ⟨⟨h,⟨[],by simp⟩⟩,treeNode h s,⟨rfl,List.nil_prefix⟩⟩

lemma rootSegment_mem (h : ℕ) (s : Tree h) (v : Node) :
    v ∈ (rootSegment h s).nodes ↔ v.1=h ∧ v.2.val <+: s.val := by
  rw [Segment.mem_nodes]
  constructor
  · intro hv
    exact hv.2
  · rintro ⟨hv,hp⟩
    exact ⟨⟨hv.symm,List.nil_prefix⟩,⟨hv,hp⟩⟩

lemma treeNode_child_injective {h : ℕ} (s : Tree h) (hs : s.val.length < h) :
    Function.Injective (fun n => treeNode h (child s hs n)) := by
  intro i j hij
  have he := congrArg (fun v : Node => v.2.val) hij
  change s.val++[i]=s.val++[j] at he
  simpa using (List.append_cancel_left he)

lemma treeNode_child_prefix {h : ℕ} (s : Tree h) (hs : s.val.length < h) {i j : ℕ}
    (hp : Prefix (treeNode h (child s hs i)) (treeNode h (child s hs j))) : i=j := by
  have he := hp.2.eq_of_length (by simp [treeNode,child])
  simpa only [treeNode,child,List.append_cancel_left_eq,List.cons.injEq,and_true] using he

lemma segmentVector_root_child {h : ℕ} (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    segmentVector (rootSegment h (child s hs j))=
      segmentVector (rootSegment h s)+Finsupp.single (treeNode h (child s hs j)) 1 := by
  ext v
  simp only [Finsupp.add_apply,segmentVector_apply,rootSegment_mem,Finsupp.single_apply]
  by_cases he : treeNode h (child s hs j)=v
  · subst v
    have hn : ¬(child s hs j).val <+: s.val := by
      intro hh
      have hl := hh.length_le
      simp only [child,List.length_append,List.length_singleton] at hl
      omega
    simp [treeNode,hn]
  · have hn : ¬(v.1=h ∧ v.2.val=s.val++[j]) := by
      rintro ⟨hc,hl⟩
      apply he
      cases v with
      | mk n v =>
        dsimp at hc hl
        subst n
        unfold treeNode
        congr 1
        exact Subtype.ext hl.symm
    rw [ite_eq_right he,add_zero]
    simp only [child,prefix_child_iff,and_or_left]
    have hnot : ¬(v.1=h ∧ v.2.val=s.val++[j]) := hn
    simp only [hnot,or_false]

def boundedPath (h : ℕ) (s : Tree h) : DualCore := coreLift (segmentVector (rootSegment h s))

lemma boundedPath_norm (h : ℕ) (s : Tree h) : ‖boundedPath h s‖=1 := by
  change ‖(((testVectorEquiv unitTests).symm (segmentVector (rootSegment h s)) : TestVector unitTests) : DualCore)‖=1
  rw [UniformSpace.Completion.norm_coe,segmentVector_norm]

lemma boundedPath_increment {h : ℕ} (s : Tree h) (hs : s.val.length < h) (j : ℕ) :
    boundedPath h (child s hs j)-boundedPath h s=coordinateVector unitTests (treeNode h (child s hs j)) := by
  unfold boundedPath
  rw [segmentVector_root_child,map_add,add_sub_cancel_left]
  rfl

lemma core_child_hilbert_upper {h : ℕ} (s : Tree h) (hs : s.val.length < h)
    (A : Finset ℕ) (a : ℕ → ℝ) :
    ‖∑ j ∈ A,a j • coordinateVector unitTests (treeNode h (child s hs j))‖ ≤
      Real.sqrt (∑ j ∈ A,(a j)^2) := by
  let v := fun j => treeNode h (child s hs j)
  let S := fun j => Segment.singleton (v j)
  have hinj : Function.Injective S := by
    intro i j hij
    exact treeNode_child_injective s hs (congrArg Segment.start hij)
  have hinc : Incomparable (A.image S) := by
    rintro U hU V hV hUV
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hV
    constructor
    · intro hp
      exact hUV (congrArg S (treeNode_child_prefix s hs hp))
    · intro hp
      exact hUV (congrArg S (treeNode_child_prefix s hs hp).symm)
  have hg (g : unitTests) : (∑ j ∈ A,(g.val (v j))^2) ≤ 1 := by
    have hh := g.property (A.image S) hinc
    rw [Finset.sum_image (fun i hi j hj hij => hinj hij)] at hh
    simpa only [S,Segment.eval_singleton] using hh
  have he : (∑ j ∈ A,a j • coordinateVector unitTests (v j))=
      coreLift (∑ j ∈ A,a j • Finsupp.single (v j) 1) := by
    simp only [map_sum,map_smul]
    rfl
  change ‖∑ j ∈ A,a j • coordinateVector unitTests (v j)‖≤_
  rw [he]
  change ‖(((testVectorEquiv unitTests).symm (∑ j ∈ A,a j • Finsupp.single (v j) 1) : TestVector unitTests) : DualCore)‖≤_
  rw [UniformSpace.Completion.norm_coe]
  change testNorm unitTests (∑ j ∈ A,a j • Finsupp.single (v j) 1)≤_
  apply ciSup_le
  intro g
  simp only [map_sum,map_smul,smul_eq_mul]
  have hT : 0 ≤ ∑ j ∈ A,(a j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := Finset.sum_mul_sq_le_sq_mul_sq A a (fun j => g.val (v j))
  have hc := mul_le_mul_of_nonneg_left (hg g) hT
  have hh : |∑ j ∈ A,a j*g.val (v j)| ≤ Real.sqrt (∑ j ∈ A,(a j)^2) := by
    nlinarith [Real.sq_sqrt hT,Real.sqrt_nonneg (∑ j ∈ A,(a j)^2),
      sq_abs (∑ j ∈ A,a j*g.val (v j)),abs_nonneg (∑ j ∈ A,a j*g.val (v j))]
  simpa [finitePairing,Finsupp.linearCombination_single] using hh

lemma core_children_weaklyNull {h : ℕ} (s : Tree h) (hs : s.val.length < h) :
    WeaklyNull (fun j => coordinateVector unitTests (treeNode h (child s hs j))) :=
  weaklyNull_of_hilbert_upper _ (core_child_hilbert_upper s hs)

theorem incomparable_core_renorming_obstruction {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : DualCore ≃L[ℝ] Y) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α*‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β*‖x‖) :
    oneSidedModulus Y (α/(2*β))=0 := by
  have hb : ∀ h, 1 ≤ h → ∀ s : Tree h, (1:ℝ) ≤ ‖boundedPath h s‖ ∧ ‖boundedPath h s‖ ≤ 1 := by
    intro h hh s
    simp [boundedPath_norm]
  have hw : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h),
      WeaklyNull (fun j => boundedPath h (child s hs j)-boundedPath h s) := by
    intro h hh s hs
    simpa only [boundedPath_increment] using core_children_weaklyNull s hs
  have hi : ∀ h, 1 ≤ h → ∀ (s : Tree h) (hs : s.val.length < h) (j : ℕ),
      (1:ℝ) ≤ ‖boundedPath h (child s hs j)-boundedPath h s‖ := by
    intro h hh s hs j
    simp only [boundedPath_increment,norm_coordinateVector,le_refl]
  simpa only [mul_one] using bounded_tree_renorming_obstruction boundedPath zero_lt_one le_rfl
    zero_lt_one hb hw hi e hα hαβ he

theorem incomparable_renorming_obstruction {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Dual ≃L[ℝ] Y) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (he : ∀ x, α*‖x‖ ≤ ‖e x‖ ∧ ‖e x‖ ≤ β*‖x‖) :
    oneSidedModulus Y (α/(2*β))=0 := by
  apply incomparable_core_renorming_obstruction (coreDualEquiv.toContinuousLinearEquiv.trans e) hα hαβ
  intro x
  simpa only [ContinuousLinearEquiv.trans_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    coreDualEquiv.norm_map] using he (coreDualEquiv x)

theorem incomparable_no_equivalent_AUC {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (e : Dual ≃L[ℝ] Y) : ¬IsAUC Y := by
  obtain ⟨α,β,hα,hαβ,he⟩ := continuousEquiv_bounds e
  have hβ : 0 < β := hα.trans_le hαβ
  intro hauc
  have hh := hauc (α/(2*β)) (by positivity)
  rw [incomparable_renorming_obstruction e hα hαβ he] at hh
  exact lt_irrefl _ hh

lemma core_head_approx (x : DualCore) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset Node, Initial (E : Set Node) ∧ ‖completedTail unitTests E x‖ < ε := by
  obtain ⟨w,hw⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  let z := testVectorEquiv unitTests w
  let E := prefixClosure z.support
  have hE : Initial (E : Set Node) := initial_prefixClosure z.support
  have hz : Finsupp.filter (fun v => v ∈ E) z=z := by
    ext v
    by_cases hv : v ∈ z.support
    · have hvE : v ∈ E := subset_prefixClosure z.support hv
      simp [hvE]
    · simp [Finsupp.filter_apply,Finsupp.notMem_support_iff.mp hv]
  have hhead : completedHead unitTests E (w : DualCore)=(w : DualCore) := by
    rw [completedHead_coe]
    change (((testVectorEquiv unitTests).symm (Finsupp.filter (fun v => v ∈ E) z) : TestVector unitTests) : DualCore)=_
    rw [hz]
    rfl
  have he : completedTail unitTests E x=completedTail unitTests E (x-(w : DualCore)) := by
    simp only [map_sub,completedTail_apply,hhead,sub_self,sub_zero]
  refine ⟨E,hE,?_⟩
  rw [he]
  exact (core_tail_norm E hE _).trans_lt (by simpa only [dist_eq_norm] using hw)

lemma incomparable_squared_core {E : Finset Node} (hE : Initial (E : Set Node))
    (x y : DualCore) (hx : completedHead unitTests E x=x) {R : ℝ}
    (hp : ‖x+y‖ ≤ R) (hm : ‖x-y‖ ≤ R) :
    ‖completedTail unitTests E y‖^2 ≤ (Real.sqrt 2+Real.sqrt 6)^2*R*(R-‖x‖) := by
  have hxn : ‖x‖ ≤ R := by linarith [norm_center_le_avg x y]
  have hyn : ‖y‖ ≤ R := by linarith [norm_displacement_le_avg x y]
  have hR : 0 ≤ R := (norm_nonneg x).trans hxn
  by_cases hz : R=0
  · have hy0 : y=0 := norm_eq_zero.mp (by linarith [norm_nonneg y])
    subst y
    rw [map_zero,norm_zero,hz]
    ring_nf
    exact le_refl _
  · have hRp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    have hxp : completedHead unitTests E (R⁻¹ • x)=R⁻¹ • x := by rw [map_smul,hx]
    have hpn : ‖R⁻¹ • x+R⁻¹ • y‖ ≤ 1 := by
      rw [← smul_add,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)]
      exact (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hR)).trans_eq (inv_mul_cancel₀ hz)
    have hmn : ‖R⁻¹ • x-R⁻¹ • y‖ ≤ 1 := by
      rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)]
      exact (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hR)).trans_eq (inv_mul_cancel₀ hz)
    have hh := incomparable_tail_core hE (R⁻¹ • x) (R⁻¹ • y) hxp hpn hmn
    rw [map_smul,norm_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hR)] at hh
    have hgap : 0 ≤ 1-R⁻¹*‖x‖ := by
      have he := mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hR)
      rw [inv_mul_cancel₀ hz] at he
      linarith
    have hs := Real.sq_sqrt hgap
    have hn := Real.sqrt_nonneg (1-R⁻¹*‖x‖)
    have hK : 0 ≤ Real.sqrt 2+Real.sqrt 6 := by positivity
    have he : (R⁻¹*‖completedTail unitTests E y‖)^2 ≤
        (Real.sqrt 2+Real.sqrt 6)^2*(1-R⁻¹*‖x‖) := by
      have hp := mul_nonneg (sub_nonneg.mpr hh)
        (show 0 ≤ (Real.sqrt 2+Real.sqrt 6)*Real.sqrt (1-R⁻¹*‖x‖)+R⁻¹*‖completedTail unitTests E y‖ by positivity)
      nlinarith
    have ht := mul_le_mul_of_nonneg_left he (sq_nonneg R)
    field_simp [hz] at ht
    nlinarith

/-- The separated-midpoint estimate on the isometric core, without finite-support assumptions on the center or sequence. -/

theorem incomparable_separated_core (x : DualCore) (u : ℕ → DualCore)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : ∀ j, ‖x+u j‖ ≤ 1) (hm : ∀ j, ‖x-u j‖ ≤ 1)
    (hsep : ∀ i j, i ≠ j → 2*c ≤ ‖u i-u j‖) :
    ‖x‖ ≤ 1-(c/(Real.sqrt 2+Real.sqrt 6))^2 ∧ 1-(c/(Real.sqrt 2+Real.sqrt 6))^2 < 1 := by
  let K := Real.sqrt 2+Real.sqrt 6
  have hcK : c < K := hc1.trans_lt (by
    dsimp [K]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ),
      Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 6)])
  have hK : 0 < K := hc.trans hcK
  have hxn : ‖x‖ ≤ 1 := by linarith [norm_center_le_avg x (u 0),hp 0,hm 0]
  have hun (j : ℕ) : ‖u j‖ ≤ 1 := by linarith [norm_displacement_le_avg x (u j),hp j,hm j]
  have hb {δ : ℝ} (hδ : 0 < δ) : c^2 ≤ K^2*(1+2*δ)*(1+3*δ-‖x‖)+2*δ+δ^2 := by
    obtain ⟨E,hE,happrox⟩ := core_head_approx x hδ
    obtain ⟨i,j,hij,hclose⟩ := finiteRank_close_pair (completedHead unitTests E) u hun
      (show 0 < 2*δ by positivity)
    let P := completedHead unitTests E
    let Q := completedTail unitTests E
    let w : DualCore := (1/2:ℝ) • (u i-u j)
    have hwc : c ≤ ‖w‖ := by
      dsimp [w]
      rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      linarith [hsep i j hij]
    have hPw : ‖P w‖ < δ := by
      dsimp [w,P]
      rw [map_smul,map_sub,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      linarith
    have hwends := lens_half_difference x (u i) (u j) (hp i) (hm i) (hp j) (hm j)
    change ‖x+w‖ ≤ 1 ∧ ‖x-w‖ ≤ 1 at hwends
    have hwn : ‖w‖ ≤ 1 := by linarith [norm_displacement_le_avg x w]
    have hQw : ‖Q w‖ ≤ 1 := (core_tail_norm E hE w).trans hwn
    have hdist : ‖P x-x‖ < δ := by
      rw [norm_sub_rev]
      exact happrox
    have hpn : ‖P x+Q w‖ ≤ 1+2*δ := by
      have he : P x+Q w=(x+w)+(P x-x)-P w := by dsimp [Q,P]; abel
      rw [he]
      have hh1 := norm_sub_le (x+w+(P x-x)) (P w)
      have hh2 := norm_add_le (x+w) (P x-x)
      linarith [hwends.1]
    have hmn : ‖P x-Q w‖ ≤ 1+2*δ := by
      have he : P x-Q w=(x-w)+(P x-x)+P w := by dsimp [Q,P]; abel
      rw [he]
      have hh1 := norm_add_le (x-w+(P x-x)) (P w)
      have hh2 := norm_add_le (x-w) (P x-x)
      linarith [hwends.2]
    have hs := incomparable_squared_core hE (P x) (Q w) (completedHead_idem unitTests E x) hpn hmn
    rw [completedTail_idem] at hs
    change ‖Q w‖^2 ≤ K^2*(1+2*δ)*(1+2*δ-‖P x‖) at hs
    have hnx : ‖x‖-δ ≤ ‖P x‖ := by
      have hh := norm_sub_norm_le x (P x)
      rw [norm_sub_rev] at hh
      linarith
    have hwt : ‖w‖ ≤ ‖Q w‖+‖P w‖ := by
      have he : w=Q w+P w := by dsimp [Q,P]; abel
      conv_lhs => rw [he]
      exact norm_add_le _ _
    have hcsq : c^2 ≤ (‖Q w‖+δ)^2 := by nlinarith [norm_nonneg (Q w)]
    have hmono := mul_le_mul_of_nonneg_left hnx
      (show 0 ≤ K^2*(1+2*δ) by positivity)
    nlinarith [mul_nonneg (le_of_lt hδ) (sub_nonneg.mpr hQw)]
  have hc2 : c^2 ≤ K^2*(1-‖x‖) := by
    have ht : Continuous (fun δ : ℝ => K^2*(1+2*δ)*(1+3*δ-‖x‖)+2*δ+δ^2) := by fun_prop
    have hh := le_of_tendsto_of_tendsto (f := fun _ : ℝ => c^2)
      (b := 𝓝[Set.Ioi (0:ℝ)] 0) tendsto_const_nhds
      (ht.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (a:=(0:ℝ)) (s:=Set.Ioi (0:ℝ))))
      (Filter.Eventually.mono self_mem_nhdsWithin (fun δ hδ => hb hδ))
    simpa only [mul_zero,add_zero,zero_add,zero_pow (by decide : 2 ≠ 0),mul_one] using hh
  have hdiv : (c/K)^2 ≤ 1-‖x‖ := by
    rw [div_pow,div_le_iff₀ (sq_pos_of_pos hK)]
    simpa only [mul_comm] using hc2
  exact ⟨by linarith,by change 1-(c/K)^2<1; nlinarith [sq_pos_of_pos (div_pos hc hK)]⟩

theorem incomparable_separated_midpoints (x : Dual) (u : ℕ → Dual)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hp : ∀ j, ‖x+u j‖ ≤ 1) (hm : ∀ j, ‖x-u j‖ ≤ 1)
    (hsep : ∀ i j, i ≠ j → 2*c ≤ ‖u i-u j‖) :
    ‖x‖ ≤ 1-(c/(Real.sqrt 2+Real.sqrt 6))^2 ∧ 1-(c/(Real.sqrt 2+Real.sqrt 6))^2 < 1 := by
  have h := incomparable_separated_core (coreDualEquiv.symm x) (fun j => coreDualEquiv.symm (u j)) hc hc1
    (fun j => by simpa only [← map_add,coreDualEquiv.symm.norm_map] using hp j)
    (fun j => by simpa only [← map_sub,coreDualEquiv.symm.norm_map] using hm j)
    (fun i j hij => by simpa only [← map_sub,coreDualEquiv.symm.norm_map] using hsep i j hij)
  simpa only [coreDualEquiv.symm.norm_map] using h

end BoundedTreePotentials.Segments

end

end OAI
