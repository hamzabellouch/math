import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.ColoredEdge
import OAI.Combinatorics.MatchingCount.Graphs.Related

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

lemma row_nonempty (x : V) : (Finset.univ.erase x : Finset V).Nonempty := by
  obtain ⟨y,hy⟩ := exists_ne x
  exact ⟨y,by simp [hy]⟩

noncomputable def sourceHeight (w : V → V → ℝ) (x : V) : ℝ :=
  (Finset.univ.erase x).sup' (row_nonempty x) (bottleneck w x)

lemma bottleneck_le_sourceHeight (w : V → V → ℝ) {x y : V} (hxy : x ≠ y) :
    bottleneck w x y ≤ sourceHeight w x :=
  Finset.le_sup' (bottleneck w x) (by simp [hxy.symm])

lemma one_le_sourceHeight (w : V → V → ℝ) (x : V) : 1 ≤ sourceHeight w x := by
  obtain ⟨y,hy⟩ := exists_ne x
  exact (one_le_bottleneck w x y).trans (bottleneck_le_sourceHeight w hy.symm)

lemma sourceHeight_nonneg (w : V → V → ℝ) (x : V) : 0 ≤ sourceHeight w x :=
  zero_le_one.trans (one_le_sourceHeight w x)

lemma sourceHeight_bound (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (x : V) : sourceHeight w x ≤ 4^K := by
  apply Finset.sup'_le
  intro y hy
  exact bottleneck_le_row_bound w x (4^K) (one_le_pow₀ (by norm_num)) (hw x) y

noncomputable def maxSourceHeight (w : V → V → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (sourceHeight w)

lemma sourceHeight_le_max (w : V → V → ℝ) (x : V) : sourceHeight w x ≤ maxSourceHeight w :=
  Finset.le_sup' (sourceHeight w) (Finset.mem_univ x)

lemma one_le_maxSourceHeight (w : V → V → ℝ) : 1 ≤ maxSourceHeight w := by
  obtain ⟨x⟩ := (inferInstance : Nonempty V)
  exact (one_le_sourceHeight w x).trans (sourceHeight_le_max w x)

lemma maxSourceHeight_bound (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) : maxSourceHeight w ≤ 4^K := by
  exact Finset.sup'_le _ _ (fun x _ => sourceHeight_bound w K hw x)

noncomputable def sourceLevels (w : V → V → ℝ) (K : ℕ) : ℕ :=
  (dyadicLevel (2*K) (maxSourceHeight w)).val

lemma sourceLevels_le (w : V → V → ℝ) (K : ℕ) : sourceLevels w K ≤ 2*K := by
  have := (dyadicLevel (2*K) (maxSourceHeight w)).isLt
  dsimp [sourceLevels]; omega

lemma maxSourceHeight_lt (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) :
    maxSourceHeight w < (2:ℝ)^(sourceLevels w K+1) := by
  apply dyadic_upper
  convert maxSourceHeight_bound w K hw using 1
  rw [pow_mul]; norm_num

abbrev SourceVertex (V : Type*) [LinearOrder V] (K : ℕ) := Vertex V (LogicalEdge V) (4*(2*K+2))

abbrev SourceRealEdge (V : Type*) [LinearOrder V] (K : ℕ) := LogicalEdge V × Fin (4*(2*K+2)+1)

def realLeft (K : ℕ) (e : SourceRealEdge V K) : SourceVertex V K :=
  atVertex source target (4*(2*K+2)) e.1 e.2.castSucc

def realRight (K : ℕ) (e : SourceRealEdge V K) : SourceVertex V K :=
  atVertex source target (4*(2*K+2)) e.1 e.2.succ

noncomputable def sourceRealB (w : V → V → ℝ) (K : ℕ) : SourceVertex V K → SourceVertex V K → ℝ :=
  realBottleneck source target (2*K+2) (fun e => bottleneck w (source e) (target e))
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w)

lemma source_profile_strength (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (e : SourceRealEdge V K) :
    sourceRealB w K (realLeft K e) (realRight K e) =
      profileActivity (2*K+2) (bottleneck w (source e.1) (target e.1))
        (sourceHeight w (source e.1)) (sourceHeight w (target e.1))
        (bottleneck w (source e.1) (target e.1)) e.2 := by
  apply source_effective_profile
  · omega
  · intro e; exact sourceHeight_nonneg w _
  · intro e; exact sourceHeight_nonneg w _
  · intro f
    rw [show 2*K+2-1=2*K+1 by omega]
    exact profile_innermost K _ _ (one_le_bottleneck _ _ _) (sourceHeight_bound w K hw _)

lemma source_strength_incident_near (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K)
    (x : SourceVertex V K) (e f : SourceRealEdge V K)
    (he : Incident (realLeft K) (realRight K) e x)
    (hf : Incident (realLeft K) (realRight K) f x) :
    sourceRealB w K (realLeft K e) (realRight K e) ≤ 2*sourceRealB w K (realLeft K f) (realRight K f) := by
  simp only [source_profile_strength w K hw]
  apply effective_profile_incident_near source target (2*K+2) (by omega)
    (fun e => bottleneck w (source e) (target e)) (sourceHeight w)
  · intro e; exact zero_le_one.trans (one_le_bottleneck _ _ _)
  · exact sourceHeight_nonneg w
  · intro e
    exact ⟨bottleneck_le_sourceHeight w (source_ne_target e),by
      rw [bottleneck_comm]; exact bottleneck_le_sourceHeight w (source_ne_target e).symm⟩
  · intro e
    rw [show 2*K+2-1=2*K+1 by omega]
    exact profile_innermost K _ _ (one_le_bottleneck _ _ _) (sourceHeight_bound w K hw _)
  · intro e
    rw [show 2*K+2-1=2*K+1 by omega]
    exact profile_innermost K _ _ (one_le_bottleneck _ _ _) (sourceHeight_bound w K hw _)
  · exact he
  · exact hf

lemma profile_upper (p : ℕ) (B HU HV lam T : ℝ) (hB : B ≤ T) (hU : HU ≤ T) (hV : HV ≤ T)
    (hU0 : 0 ≤ HU) (hV0 : 0 ≤ HV) (hlam : lam ≤ T) (i : Fin (4*p+1)) :
    profileActivity p B HU HV lam i ≤ T := by
  rcases lt_trichotomy i.val (2*p) with h | h | h
  · rw [profile_left _ _ _ _ _ _ h]
    exact max_le hB ((div_le_self hU0 (one_le_pow₀ (by norm_num))).trans hU)
  · have hi : i=⟨2*p,by omega⟩ := Fin.ext h
    rw [hi,profile_center]; exact hlam
  · rw [profile_right _ _ _ _ _ _ h]
    exact max_le hB ((div_le_self hV0 (one_le_pow₀ (by norm_num))).trans hV)

lemma source_strength_le_max (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (e : SourceRealEdge V K) :
    sourceRealB w K (realLeft K e) (realRight K e) ≤ maxSourceHeight w := by
  rw [source_profile_strength w K hw]
  have hb := (bottleneck_le_sourceHeight w (source_ne_target e.1)).trans (sourceHeight_le_max w _)
  exact profile_upper _ _ _ _ _ _ hb (sourceHeight_le_max w _) (sourceHeight_le_max w _)
    (sourceHeight_nonneg w _) (sourceHeight_nonneg w _) hb _

lemma sourceRealB_comm (w : V → V → ℝ) (K : ℕ) (x y : SourceVertex V K) :
    sourceRealB w K x y = sourceRealB w K y x := bottleneck_comm _ _ _

lemma sourceRealB_tri (w : V → V → ℝ) (K : ℕ) (x y z : SourceVertex V K)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    min (sourceRealB w K x z) (sourceRealB w K z y) ≤ sourceRealB w K x y :=
  bottleneck_ultrametric _ _ _ _ hxy hxz hyz

lemma sourceRealB_floor (w : V → V → ℝ) (K : ℕ) (x y : SourceVertex V K) :
    1 ≤ sourceRealB w K x y := one_le_bottleneck _ _ _

abbrev SourceLabel (w : V → V → ℝ) (K : ℕ) :=
  Label (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K) (sourceLevels w K)

noncomputable def sourceBags (w : V → V → ℝ) (K : ℕ) (x : SourceVertex V K) :
    Finset (SourceLabel w K) :=
  memberships (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K)
    (realLeft K) (realRight K) (sourceLevels w K) x

noncomputable abbrev sourceTree (w : V → V → ℝ) (K : ℕ) : SimpleGraph (SourceLabel w K) :=
  tree (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K)

lemma sourceTree_isTree (w : V → V → ℝ) (K : ℕ) : (sourceTree w K).IsTree := by
  exact ⟨tree_connected _ _ _ (sourceRealB_floor w K) _,tree_acyclic _ _ _ _⟩

lemma sourceBag_card_le_two (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K) (x : SourceVertex V K) :
    (sourceBags w K x).card ≤ 2 := by
  apply membership_count
  · exact sourceRealB_floor w K
  · intro e
    exact (source_strength_le_max w K hw e).trans_lt (maxSourceHeight_lt w K hw)
  · exact source_strength_incident_near w K hw

lemma sourceBag_tree_adjacent (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y, x ≠ y → edgeActivity w x y ≤ (4:ℝ)^K)
    (x : SourceVertex V K) (a b : SourceLabel w K)
    (ha : a ∈ sourceBags w K x) (hb : b ∈ sourceBags w K x) :
    a=b ∨ (sourceTree w K).Adj a b := by
  apply memberships_tree_bags _ _ _ (sourceRealB_floor w K) (realLeft K) (realRight K)
    (sourceLevels w K) (fun e => (source_strength_le_max w K hw e).trans_lt
      (maxSourceHeight_lt w K hw)) (source_strength_incident_near w K hw) x a b ha hb

lemma sourceBag_height (w : V → V → ℝ) (K : ℕ) {x y : SourceVertex V K}
    (hxy : x ≠ y) (l : SourceLabel w K) (hx : l ∈ sourceBags w K x)
    (hy : l ∈ sourceBags w K y) : (2:ℝ)^l.1.val ≤ sourceRealB w K x y := by
  exact common_height_le _ _ _ (sourceRealB_floor w K) (realLeft K) (realRight K)
    (sourceLevels w K) hxy hx hy

end MatchingFPRAS.Enlargement

namespace MatchingFPRAS.Transport

section

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

noncomputable def support (Q : Finset E) : Finset V := by
  classical
  exact Finset.univ.filter fun v => ∃ e ∈ Q, inc e v

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma mem_support (Q : Finset E) (v : V) : v ∈ support inc Q ↔ ∃ e ∈ Q, inc e v := by
  classical
  simp [support]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma support_eq_of_matching {Q : Finset E} {U : Finset V} (h : MatchingOn inc Q U) :
    support inc Q=U := by
  ext v
  rw [mem_support]
  constructor
  · rintro ⟨e,he,hv⟩; exact h.1 e he v hv
  · intro hv
    obtain ⟨e,he,_⟩ := h.2 v hv
    exact ⟨e,he⟩

abbrev Partial := {Q : Finset E // MatchingOn inc Q (support inc Q)}

abbrev Matchings (U : Finset V) := {M : Finset E // MatchingOn inc M U}

noncomputable instance partialFintype : Fintype (Partial inc) := Fintype.ofFinite _

noncomputable instance matchingsFintype (U : Finset V) : Fintype (Matchings inc U) := Fintype.ofFinite _

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma submatching {M Q : Finset E} {U : Finset V} (hM : MatchingOn inc M U) (hQ : Q⊆M) :
    MatchingOn inc Q (support inc Q) := by
  refine ⟨?_,?_⟩
  · intro e he v hv; exact (mem_support inc Q v).mpr ⟨e,he,hv⟩
  · intro v hv
    obtain ⟨e,he,hev⟩ := (mem_support inc Q v).mp hv
    refine ⟨e,⟨he,hev⟩,?_⟩
    intro f hf
    exact hM.unique (hM.1 e (hQ he) v hev) (hQ hf.1) hf.2 (hQ he) hev

omit [Fintype E] [DecidableEq E] in
lemma support_sdiff_disjoint (Q : Finset E) : Disjoint (support inc Q) (univ \ support inc Q) := by
  exact Finset.disjoint_left.mpr (fun x hx hy => (Finset.mem_sdiff.mp hy).2 hx)

noncomputable def expansionEquiv (hinc : ∀ e, ∃ v, inc e v) :
    (Σ M : Matchings inc univ, {Q : Finset E // Q⊆M.val}) ≃
      Σ Q : Partial inc, Matchings inc (univ \ support inc Q.val) where
  toFun a := ⟨⟨a.2.val,submatching inc a.1.property a.2.property⟩,
    ⟨a.1.val \ a.2.val,a.1.property.sdiff
      (submatching inc a.1.property a.2.property) a.2.property⟩⟩
  invFun a := ⟨⟨a.1.val ∪ a.2.val,by
      have h := a.1.property.union a.2.property (support_sdiff_disjoint inc a.1.val)
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)] at h
      exact h⟩,⟨a.1.val,Finset.subset_union_left⟩⟩
  left_inv a := by
    rcases a with ⟨M,Q,hQ⟩
    have h : Q ∪ (M.val \ Q)=M.val := Finset.union_sdiff_of_subset hQ
    apply Sigma.ext (Subtype.ext h)
    change HEq (⟨Q,Finset.subset_union_left⟩ : {R : Finset E // R ⊆ Q ∪ (M.val \ Q)})
      (⟨Q,hQ⟩ : {R : Finset E // R ⊆ M.val})
    exact (Subtype.heq_iff_coe_eq (fun R => by rw [h])).mpr rfl
  right_inv a := by
    rcases a with ⟨Q,M⟩
    have hd : Disjoint Q.val M.val := Q.property.disjoint_edges M.property hinc
      (support_sdiff_disjoint inc Q.val)
    change (⟨Q,⟨(Q.val ∪ M.val) \ Q.val,_⟩⟩ :
      Σ Q : Partial inc, Matchings inc (univ \ support inc Q.val)) = ⟨Q,M⟩
    apply congrArg (fun R : Matchings inc (univ \ support inc Q.val) =>
      (⟨Q,R⟩ : Σ Q : Partial inc, Matchings inc (univ \ support inc Q.val)))
    exact Subtype.ext (Finset.union_sdiff_cancel_left hd)

noncomputable def partitionWeight {R : Type*} [CommSemiring R] (w : E → R) (U : Finset V) : R :=
  ∑ M : Matchings inc U, ∏ e ∈ M.val, w e

theorem partition_add {R : Type*} [CommSemiring R] (r v : E → R)
    (hinc : ∀ e, ∃ x, inc e x) :
    partitionWeight inc (fun e => r e+v e) univ =
      ∑ Q : Partial inc, (∏ e ∈ Q.val, v e) * partitionWeight inc r (univ \ support inc Q.val) := by
  classical
  unfold partitionWeight
  have hex (M : Matchings inc univ) :
      (∏ e ∈ M.val, (r e+v e)) =
        ∑ Q : {Q : Finset E // Q⊆M.val}, (∏ e ∈ Q.val, v e) * ∏ e ∈ M.val \ Q.val, r e := by
    rw [show (∏ e ∈ M.val, (r e+v e))=(∏ e ∈ M.val, (v e+r e)) by
      apply Finset.prod_congr rfl; intro e he; exact add_comm _ _]
    rw [Finset.prod_add]
    exact Finset.sum_subtype _ (fun Q => Finset.mem_powerset)
      (fun Q => (∏ e ∈ Q, v e) * ∏ e ∈ M.val \ Q, r e)
  simp_rw [hex,Finset.mul_sum]
  have h := (expansionEquiv inc hinc).sum_comp
    (fun a => (∏ e ∈ a.1.val, v e) * ∏ e ∈ a.2.val, r e)
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at h
  exact h

end

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
@[simp] lemma support_empty : support inc ∅=∅ := by
  ext x; simp [support]

noncomputable def emptyPartial : Partial inc := ⟨∅,by simp [MatchingOn]⟩

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma partial_eq_empty_iff (Q : Partial inc) : Q=emptyPartial inc ↔ Q.val=∅ := by
  exact Subtype.ext_iff

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma partitionWeight_nonneg (r : E → ℝ) (hr : ∀ e,0≤r e) (U : Finset V) :
    0≤partitionWeight inc r U := Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun e _ => hr e))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma partitionWeight_mono (r w : E → ℝ) (hr : ∀ e,0≤r e) (hrw : ∀ e,r e≤w e)
    (U : Finset V) : partitionWeight inc r U≤partitionWeight inc w U :=
  Finset.sum_le_sum (fun _ _ => Finset.prod_le_prod₀ (fun e _ => hr e) (fun e _ => hrw e))

lemma pow_mul_linear_le_one (x : ℝ) (hx : 0≤x) (m : ℕ) :
    (1+x)^m * (1-(m:ℝ)*x) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,Nat.cast_succ]
    have hp : 0≤(1+x)^m := pow_nonneg (by linarith) _
    have h : (1+x) * (1-((m:ℝ)+1)*x) ≤ 1-(m:ℝ)*x := by
      have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg x,mul_nonneg hm (sq_nonneg x)]
    calc
      _ = (1+x)^m * ((1+x) * (1-((m:ℝ)+1)*x)) := by ring
      _ ≤ (1+x)^m * (1-(m:ℝ)*x) := mul_le_mul_of_nonneg_left h hp
      _ ≤ 1 := ih

lemma pow_small_le (x : ℝ) (hx : 0≤x) (m : ℕ) (hm : (m:ℝ)*x≤1/100) :
    (1+x)^m≤100/99 := by
  have hp : 0≤(1+x)^m := pow_nonneg (by linarith) _
  have h := pow_mul_linear_le_one x hx m
  nlinarith [mul_nonneg hp (show 0≤1/100-(m:ℝ)*x by linarith)]

lemma all_subsets_pow (x : ℝ) :
    (∑ Q : Finset E, x^Q.card)=(1+x)^Fintype.card E := by
  classical
  have h := Finset.prod_add (fun _ : E => x) (fun _ => (1:ℝ)) univ
  simpa [Finset.prod_const,Finset.prod_const_one,add_comm] using h.symm

omit [DecidableEq V] in
lemma partial_pow_sum_le (x : ℝ) (hx : 0≤x) :
    (∑ Q : Partial inc, x^Q.val.card) ≤ (1+x)^Fintype.card E := by
  classical
  rw [←all_subsets_pow]
  calc
    _ = ∑ Q ∈ univ.image (Subtype.val : Partial inc → Finset E), x^Q.card :=
      (Finset.sum_image (fun a _ b _ h => Subtype.ext h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun Q _ _ => pow_nonneg hx _)

theorem finite_inflation (r v : E → ℝ) (hr : ∀ e,0≤r e) (hv : ∀ e,0≤v e)
    (hinc : ∀ e,∃ x,inc e x) (hz : 0<partitionWeight inc r univ)
    (x : ℝ) (hx : 0≤x) (hm : (Fintype.card E:ℝ)*x≤1/100)
    (hlocal : ∀ Q : Partial inc, Q.val≠∅ →
      (∏ e ∈ Q.val, v e) * partitionWeight inc r (univ \ support inc Q.val) /
        partitionWeight inc r univ ≤ 2*x^Q.val.card) :
    1 ≤ partitionWeight inc (fun e => r e+v e) univ / partitionWeight inc r univ ∧
    partitionWeight inc (fun e => r e+v e) univ / partitionWeight inc r univ ≤ 2 := by
  classical
  constructor
  · apply (le_div_iff₀ hz).mpr
    simpa using partitionWeight_mono inc r (fun e => r e+v e) hr (fun e => le_add_of_nonneg_right (hv e)) univ
  · let mass (Q : Partial inc) := (∏ e ∈ Q.val, v e) *
      partitionWeight inc r (univ \ support inc Q.val) / partitionWeight inc r univ
    have hmass : ∀ Q : Partial inc, mass Q+(if Q=emptyPartial inc then 1 else 0)≤2*x^Q.val.card := by
      intro Q
      by_cases he : Q=emptyPartial inc
      · subst Q
        norm_num [mass,emptyPartial,hz.ne']
      · simpa only [ite_eq_right he,add_zero] using hlocal Q (fun h => he ((partial_eq_empty_iff inc Q).mpr h))
    have hs := Finset.sum_le_sum (s := (univ : Finset (Partial inc))) (fun Q _ => hmass Q)
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      ←Finset.mul_sum] at hs
    have hsum := partial_pow_sum_le inc x hx
    have hpow := pow_small_le x hx (Fintype.card E) hm
    rw [partition_add inc r v hinc,Finset.sum_div]
    change (∑ Q : Partial inc, mass Q) ≤ 2
    linarith

end MatchingFPRAS.Transport

end OAI
