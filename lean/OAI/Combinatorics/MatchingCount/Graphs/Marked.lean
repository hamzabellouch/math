import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.PM

namespace OAI

namespace MatchingFPRAS.Marking

open Finset MatchingFPRAS.Transport

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

variable [DecidableEq V] [DecidableEq E] [DecidableEq I]

variable (inc : E → V → Prop)

abbrev Marked := Σ M : Matchings inc univ, (↥M.val → I)

noncomputable def mass (part : E → I → ℝ) (a : Marked (I:=I) inc) : ℝ :=
  ∏ e : a.1.val, part e.val (a.2 e)

def collapse (part : E → I → ℝ) (e : E) : ℝ := ∑ i,part e i

omit [Fintype E] [DecidableEq V] [DecidableEq I] in
lemma sum_marks (part : E → I → ℝ) (M : Matchings inc univ) :
    (∑ m : (↥M.val → I),mass inc part ⟨M,m⟩)=∏ e ∈ M.val,collapse part e := by
  classical
  rw [Finset.prod_subtype M.val (fun _ => Iff.rfl)]
  exact (Fintype.prod_sum (fun e : M.val => part e.val)).symm

omit [DecidableEq V] [DecidableEq I] in
theorem total_mass (part : E → I → ℝ) :
    (∑ a : Marked (I:=I) inc,mass inc part a)=partitionWeight inc (collapse part) univ := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun M _ => sum_marks inc part M

omit [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma mass_nonneg (part : E → I → ℝ) (hp : ∀ e i,0 ≤ part e i) (a : Marked (I:=I) inc) :
    0 ≤ mass inc part a := Finset.prod_nonneg fun _ _ => hp _ _

noncomputable def law (part : E → I → ℝ) (a : Marked (I:=I) inc) : ℝ :=
  mass inc part a/partitionWeight inc (collapse part) univ

omit [DecidableEq V] [DecidableEq I] in
lemma law_nonneg (part : E → I → ℝ) (hp : ∀ e i,0 ≤ part e i) (a : Marked (I:=I) inc) :
    0 ≤ law inc part a := by
  apply div_nonneg (mass_nonneg inc part hp a)
  rw [←total_mass inc part]
  exact Finset.sum_nonneg fun a _ => mass_nonneg inc part hp a

omit [DecidableEq V] [DecidableEq I] in
lemma law_sum (part : E → I → ℝ) (hz : partitionWeight inc (collapse part) univ ≠ 0) :
    ∑ a : Marked (I:=I) inc,law inc part a=1 := by
  simp only [law,←Finset.sum_div,total_mass,div_self hz]

omit [DecidableEq V] [DecidableEq I] in
lemma law_marginal (part : E → I → ℝ) (M : Matchings inc univ) :
    (∑ m : (↥M.val → I),law inc part ⟨M,m⟩)=
      (∏ e ∈ M.val,collapse part e)/partitionWeight inc (collapse part) univ := by
  simp only [law,←Finset.sum_div,sum_marks]

omit [DecidableEq V] in
lemma pattern_sum (part : E → I → ℝ)
    (pattern : (M : Matchings inc univ) → ↥M.val → I)
    (u : Matchings inc univ → ℝ) :
    (∑ a : Marked (I:=I) inc, if a.2=pattern a.1 then mass inc part a*u a.1 else 0)=
      ∑ M : Matchings inc univ,(∏ e : M.val,part e.val (pattern M e))*u M := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro M _
  simp only [Finset.sum_ite_eq',mem_univ,ite_true,mass]

omit [DecidableEq V] in
lemma allReal_mean (part : E → I → ℝ) (real : I) (u : E → ℝ) :
    (∑ a : Marked (I:=I) inc,law inc part a *
      (if a.2=(fun _ => real) then ∏ e ∈ a.1.val,u e else 0))=
    partitionWeight inc (fun e => part e real*u e) univ /
      partitionWeight inc (collapse part) univ := by
  classical
  calc
    _ = (∑ a : Marked (I:=I) inc,
        if a.2=(fun _ => real) then mass inc part a*(∏ e ∈ a.1.val,u e) else 0) /
        partitionWeight inc (collapse part) univ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [law,mul_zero,zero_div,div_mul_eq_mul_div]
    _ = _ := by
      congr 1
      rw [pattern_sum inc part (fun _ _ => real) (fun M => ∏ e ∈ M.val,u e)]
      unfold partitionWeight
      apply Finset.sum_congr rfl
      intro M _
      rw [←Finset.prod_subtype M.val (fun _ => Iff.rfl) (fun e => part e real),
        ←Finset.prod_mul_distrib]

noncomputable def completionEquiv (hinc : ∀ e,∃ x,inc e x) (Q : Partial inc) :
    {M : Matchings inc univ // Q.val⊆M.val} ≃ Matchings inc (univ \ support inc Q.val) where
  toFun M := ⟨M.val.val \ Q.val,M.val.property.sdiff Q.property M.property⟩
  invFun M := ⟨⟨Q.val∪M.val,by
    have h := Q.property.union M.property (support_sdiff_disjoint inc Q.val)
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ _)] at h
    exact h⟩,Finset.subset_union_left⟩
  left_inv M := by
    apply Subtype.ext
    exact Subtype.ext (Finset.union_sdiff_of_subset M.property)
  right_inv M := by
    have hd := Q.property.disjoint_edges M.property hinc (support_sdiff_disjoint inc Q.val)
    exact Subtype.ext (Finset.union_sdiff_cancel_left hd)

lemma completion_sum (hinc : ∀ e,∃ x,inc e x) (Q : Partial inc) (r : E → ℝ) :
    (∑ M : {M : Matchings inc univ // Q.val⊆M.val},∏ e ∈ M.val.val \ Q.val,r e)=
      partitionWeight inc r (univ \ support inc Q.val) := by
  exact Fintype.sum_equiv (completionEquiv inc hinc Q) _ _ (fun _ => rfl)

noncomputable def conditional (part : E → I → ℝ) (M : Matchings inc univ)
    (m : ↥M.val → I) : ℝ := ∏ e : M.val,part e.val (m e)/collapse part e.val

omit [Fintype E] [DecidableEq V] [DecidableEq I] in
lemma conditional_sum (part : E → I → ℝ) (hc : ∀ e,collapse part e≠0)
    (M : Matchings inc univ) : ∑ m : (↥M.val → I),conditional inc part M m=1 := by
  unfold conditional
  rw [←Fintype.prod_sum (fun e : M.val => fun i : I => part e.val i / collapse part e.val)]
  apply Finset.prod_eq_one
  intro e _
  rw [←Finset.sum_div]
  exact div_self (hc _)

omit [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma law_from_reveal (part : E → I → ℝ) (hc : ∀ e,collapse part e≠0)
    (a : Marked (I:=I) inc) :
    ((∏ e ∈ a.1.val,collapse part e)/partitionWeight inc (collapse part) univ) *
      conditional inc part a.1 a.2 = law inc part a := by
  classical
  rw [conditional,Finset.prod_div_distrib,←Finset.prod_subtype a.1.val (fun _ => Iff.rfl)]
  have hn : (∏ e ∈ a.1.val,collapse part e)≠0 := Finset.prod_ne_zero_iff.mpr (fun e _ => hc e)
  unfold law mass
  field_simp

omit [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq I] in
lemma fixed_pattern_mass (part : E → I → ℝ) (real probe : I)
    (Q : Finset E) (M : Matchings inc univ) (hQ : Q⊆M.val) :
    (∏ e : M.val,part e.val (if e.val∈Q then probe else real))=
      (∏ e ∈ Q,part e probe)*(∏ e ∈ M.val \ Q,part e real) := by
  classical
  rw [←Finset.prod_subtype M.val (fun _ => Iff.rfl)
    (fun e : E => part e (if e∈Q then probe else real))]
  calc
    _ = (∏ e ∈ Q,part e (if e∈Q then probe else real))*
        (∏ e ∈ M.val \ Q,part e (if e∈Q then probe else real)) := by
      rw [←Finset.prod_union (Finset.disjoint_left.mpr (fun e he hf => (Finset.mem_sdiff.mp hf).2 he)),Finset.union_sdiff_of_subset hQ]
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl; intro e he; simp only [ite_eq_left he]
      · apply Finset.prod_congr rfl; intro e he; simp only [ite_eq_right (mem_sdiff.mp he).2]

lemma sum_if_subtype {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (f : A → ℝ) :
    (∑ a,if P a then f a else 0)=∑ a : {a // P a},f a.val := by
  classical
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) f

omit [Fintype I] [DecidableEq I] in
lemma fixed_pattern_sum (hinc : ∀ e,∃ x,inc e x)
    (part : E → I → ℝ) (real probe : I) (Q : Partial inc) (u : E → ℝ) :
    (∑ M : Matchings inc univ,
      (∏ e : M.val,part e.val (if e.val∈Q.val then probe else real))*
      (if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,u e else 0))=
    (∏ e ∈ Q.val,part e probe)*partitionWeight inc (fun e => part e real*u e)
      (univ \ support inc Q.val) := by
  classical
  have he (M : Matchings inc univ) :
      (∏ e : M.val,part e.val (if e.val∈Q.val then probe else real))*
      (if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,u e else 0)=
      (∏ e ∈ Q.val,part e probe)*
        (if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,part e real*u e else 0) := by
    by_cases hs : Q.val⊆M.val
    · simp only [ite_eq_left hs,fixed_pattern_mass inc part real probe Q.val M hs]
      rw [mul_assoc,←Finset.prod_mul_distrib]
    · simp only [ite_eq_right hs,mul_zero]
  simp_rw [he]
  rw [←Finset.mul_sum,sum_if_subtype]
  rw [completion_sum inc hinc Q]

theorem fixed_probe_mean (hinc : ∀ e,∃ x,inc e x)
    (part : E → I → ℝ) (real probe : I) (Q : Partial inc) (u : E → ℝ) :
    (∑ a : Marked (I:=I) inc,law inc part a *
      (if Q.val⊆a.1.val ∧ a.2=(fun e => if e.val∈Q.val then probe else real)
        then ∏ e ∈ a.1.val \ Q.val,u e else 0))=
    ((∏ e ∈ Q.val,part e probe)*partitionWeight inc (fun e => part e real*u e)
      (univ \ support inc Q.val))/partitionWeight inc (collapse part) univ := by
  classical
  calc
    _ = (∑ a : Marked (I:=I) inc,
        if a.2=(fun e => if e.val∈Q.val then probe else real) then
          mass inc part a*(if Q.val⊆a.1.val then ∏ e ∈ a.1.val \ Q.val,u e else 0)
        else 0)/partitionWeight inc (collapse part) univ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hQ : Q.val⊆a.1.val <;>
        by_cases hm : a.2=(fun e => if e.val∈Q.val then probe else real) <;>
        simp only [hQ,hm,and_true,and_false,ite_true,ite_false,
          law,mul_zero,zero_div,div_mul_eq_mul_div]
    _ = _ := by
      congr 1
      rw [pattern_sum inc part (fun M e => if e.val∈Q.val then probe else real)
        (fun M => if Q.val⊆M.val then ∏ e ∈ M.val \ Q.val,u e else 0)]
      exact fixed_pattern_sum inc hinc part real probe Q u

end MatchingFPRAS.Marking

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Representation Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def frozenActivity (w w₁ : V → V → ℝ) (K : ℕ)
    (e : SourceRealEdge V K) : ℝ :=
  pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e))
    (logicalActivity w₁) e.1 e.2

noncomputable def frozenPortion (w w₁ : V → V → ℝ) (K : ℕ) : BagEdge (sourceBags w K) → ℝ :=
  by classical exact edgeExtension (sourceRealEmbedding w K) (frozenActivity w w₁ K)

noncomputable def sourceC (w : V → V → ℝ) (K : ℕ) : ℝ :=
  ∏ e : LogicalEdge V,pathConstant (2*K+2) (bottleneck w (source e) (target e))
    (sourceHeight w (source e)) (sourceHeight w (target e))

lemma sourceC_pos (w : V → V → ℝ) (K : ℕ) : 0 < sourceC w K := by
  exact Finset.prod_pos fun e _ => pathConstant_pos _ _ _ _
    (zero_lt_one.trans_le (one_le_bottleneck _ _ _))

lemma frozenPortion_partition (w w₁ : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w₁)) := by
  classical
  rw [show frozenPortion w w₁ K=edgeExtension (sourceRealEmbedding w K) (frozenActivity w w₁ K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

lemma frozenPortion_full (w w₁ : V → V → ℝ) (hz : 0 < partition w₁ ∅) (K : ℕ) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K) univ=sourceC w K*partition w₁ ∅ := by
  rw [←survivors_empty (V:=V) K,frozenPortion_partition,intact_partition_identity w₁ hz]
  rfl

lemma frozenPortion_probe (w w₁ : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    partitionWeight BagEdge.Incident (frozenPortion w w₁ K)
      (survivors (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀))=
    sourceC w K*partition w₁ {source e₀,target e₀} := by
  rw [frozenPortion_partition]
  change realHolePartition source target (4*(2*K+2)) ∅
    (singleProbeHoles (2*K+2) (by omega) e₀)
    (fun e => profileActivity (2*K+2) (bottleneck w (source e) (target e))
      (sourceHeight w (source e)) (sourceHeight w (target e)) (logicalActivity w₁ e))=_
  rw [singleProbe_partition _ _ _ _ _ (source_ne_target e₀),
    logical_partition_redundant w₁ _ e₀ (by simp)]
  rfl

lemma profile_reweight (p : ℕ) (B Hu Hv lam r : ℝ) (i : Fin (4*p+1)) :
    profileActivity p B Hu Hv (lam*r) i =
      profileActivity p B Hu Hv lam i*(if i.val=2*p then r else 1) := by
  rcases lt_trichotomy i.val (2*p) with hi|hi|hi
  · rw [profile_left _ _ _ _ _ _ hi,profile_left _ _ _ _ _ _ hi,ite_eq_right (ne_of_lt hi),mul_one]
  · have he : i=⟨2*p,by omega⟩ := Fin.ext hi
    rw [he]; simp
  · rw [profile_right _ _ _ _ _ _ hi,profile_right _ _ _ _ _ _ hi,ite_eq_right (ne_of_gt hi),mul_one]

noncomputable def rawReweight (w w₁ : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) : ℝ :=
  if e.2.val=2*(2*K+2) then logicalActivity w₁ e.1/logicalActivity w e.1 else 1

noncomputable def bagReweight (w w₁ : V → V → ℝ) (K : ℕ) (q : BagEdge (sourceBags w K)) : ℝ := by
  classical
  exact if h : ∃ e,sourceRealEmbedding w K e=q then rawReweight w w₁ K h.choose else 1

lemma bagReweight_on (w w₁ : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) :
    bagReweight w w₁ K (sourceRealEmbedding w K e)=rawReweight w w₁ K e := by
  classical
  unfold bagReweight
  rw [dite_eq_left ⟨e,rfl⟩]
  exact congrArg (rawReweight w w₁ K) ((sourceRealEmbedding w K).injective
    (Exists.choose_spec (show ∃ e',sourceRealEmbedding w K e'=sourceRealEmbedding w K e from ⟨e,rfl⟩)))

lemma bagReweight_identity (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K : ℕ) :
    (fun e => sourceRealPortion w K e*bagReweight w w₁ K e)=frozenPortion w w₁ K := by
  classical
  funext e
  by_cases he : ∃ q,sourceRealEmbedding w K q=e
  · obtain ⟨q,rfl⟩ := he
    rw [sourceRealPortion,frozenPortion,edgeExtension_on,edgeExtension_on,bagReweight_on]
    have hl : logicalActivity w q.1≠0 := by
      unfold logicalActivity edgeActivity
      split_ifs <;> exact (hw _ _).ne'
    dsimp only [sourceRealActivity,frozenActivity,pathActivity,rawReweight]
    rw [←profile_reweight,mul_div_cancel₀ _ hl]
  · rw [sourceRealPortion,frozenPortion,edgeExtension_off _ _ _ he,edgeExtension_off _ _ _ he,zero_mul]

lemma bagReweight_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ bagReweight w w₁ K e ∧ bagReweight w w₁ K e ≤ 1 := by
  classical
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · have h₀ : 0 < logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw _ _
      have h₁ : 0 ≤ logicalActivity w₁ he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw₁ _ _
      have h₂ : logicalActivity w₁ he.choose.1 ≤ logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hle _ _
      exact ⟨div_nonneg h₁ h₀.le,(div_le_one h₀).mpr h₂⟩
    · norm_num
  · norm_num

noncomputable def centralEdge (w : V → V → ℝ) (K : ℕ) (e : LogicalEdge V) : BagEdge (sourceBags w K) :=
  sourceRealEmbedding w K (e,⟨2*(2*K+2),by omega⟩)

lemma centralEdge_injective (w : V → V → ℝ) (K : ℕ) : Function.Injective (centralEdge w K) := by
  intro e f h
  exact congrArg Prod.fst ((sourceRealEmbedding w K).injective h)

noncomputable def probePortion (w : V → V → ℝ) (K D : ℕ) (q : BagEdge (sourceBags w K)) : ℝ := by
  classical
  exact if ∃ e,centralEdge w K e=q then 1/(D:ℝ) else 0

lemma probePortion_on (w : V → V → ℝ) (K D : ℕ) (e : LogicalEdge V) :
    probePortion w K D (centralEdge w K e)=1/(D:ℝ) := by
  classical
  simp [probePortion]

noncomputable def sourcePortions (w : V → V → ℝ) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) : Fin 3 → ℝ :=
  ![sourceRealPortion w K e,bagHeight w K e.val.val.2/D-probePortion w K D e,probePortion w K D e]

lemma sourcePortions_collapse (w : V → V → ℝ) (K D : ℕ) :
    Marking.collapse (sourcePortions w K D)=sourceBagWeight w K D := by
  funext e
  simp [Marking.collapse,sourcePortions,Fin.sum_univ_succ,sourceBagWeight]

lemma sourcePortions_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) (i : Fin 3) : 0 ≤ sourcePortions w K D e i := by
  classical
  fin_cases i
  · exact sourceRealPortion_nonneg w hw K e
  · change 0 ≤ bagHeight w K e.val.val.2/D-probePortion w K D e
    apply sub_nonneg.mpr
    unfold probePortion
    split_ifs
    · exact div_le_div_of_nonneg_right (bagHeight_one w K _) (Nat.cast_nonneg D)
    · exact div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D)
  · change 0 ≤ probePortion w K D e
    unfold probePortion
    split_ifs <;> positivity

lemma centralEdge_ends (w : V → V → ℝ) (K : ℕ) (e : LogicalEdge V) :
    (centralEdge w K e).val.val.1 =
    s((Sum.inr (e,(⟨2*(2*K+2)-1,by omega⟩ : Fin (4*(2*K+2)))) : SourceVertex V K),
      Sum.inr (e,⟨2*(2*K+2),by omega⟩)) := by
  change edge source target (4*(2*K+2)) e ⟨2*(2*K+2),by omega⟩=_
  simp only [edge,atVertex,Fin.val_castSucc,Fin.val_succ]
  simp only [show 2*(2*K+2)≠0 by omega,show 2*(2*K+2)≠4*(2*K+2)+1 by omega,
    show 2*(2*K+2)+1≠0 by omega, show 2*(2*K+2)+1≠4*(2*K+2)+1 by omega,
    dite_false,Nat.add_sub_cancel]

lemma probe_support (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    support BagEdge.Incident {centralEdge w K e₀}=
      enlargedHoles (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀) := by
  classical
  ext x
  rw [mem_support]
  simp only [mem_singleton,exists_eq_left,BagEdge.Incident,ColoredEdge.Incident,centralEdge_ends,Sym2.mem_iff]
  cases x with
  | inl x => simp
  | inr ei =>
    rcases ei with ⟨e,i⟩
    by_cases he : e=e₀
    · subst e
      simp [singleProbeHoles,probeHoles]
    · simp [singleProbeHoles,he]

lemma probe_survivors (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    univ \ support BagEdge.Incident {centralEdge w K e₀}=
      survivors (4*(2*K+2)) ∅ (singleProbeHoles (2*K+2) (by omega) e₀) := by
  rw [probe_support]
  ext x
  cases x with
  | inl x => simp
  | inr ei => rcases ei with ⟨e,i⟩; simp

noncomputable def probePartial (w : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V) :
    Partial (BagEdge.Incident (bags:=sourceBags w K)) := by
  classical
  refine ⟨{centralEdge w K e₀},?_,?_⟩
  · intro e he x hx
    exact (mem_support _ _ _).mpr ⟨e,he,hx⟩
  · intro x hx
    obtain ⟨e,he,hex⟩ := (mem_support _ _ _).mp hx
    refine ⟨e,⟨he,hex⟩,?_⟩
    intro f hf
    exact (mem_singleton.mp hf.1).trans (mem_singleton.mp he).symm

open scoped Classical

abbrev SourceMarked (w : V → V → ℝ) (K : ℕ) :=
  Marking.Marked (I:=Fin 3) (BagEdge.Incident (bags:=sourceBags w K))

noncomputable def sourceLaw (w : V → V → ℝ) (K D : ℕ) : SourceMarked w K → ℝ :=
  Marking.law BagEdge.Incident (sourcePortions w K D)

noncomputable def observableA (w : V → V → ℝ) (K : ℕ) (a : SourceMarked w K) : ℝ := by
  classical exact if a.2=(fun _ => 0) then 1 else 0

noncomputable def observableD (w w₁ : V → V → ℝ) (K : ℕ) (a : SourceMarked w K) : ℝ := by
  classical exact if a.2=(fun _ => 0) then ∏ e ∈ a.1.val,bagReweight w w₁ K e else 0

noncomputable def observableProbe (w w₁ : V → V → ℝ) (K : ℕ) (e₀ : LogicalEdge V)
    (a : SourceMarked w K) : ℝ := by
  classical exact if {centralEdge w K e₀}⊆a.1.val ∧
      a.2=(fun e => if e.val∈({centralEdge w K e₀} : Finset _) then 2 else 0)
    then ∏ e ∈ a.1.val \ {centralEdge w K e₀},bagReweight w w₁ K e else 0

noncomputable def sourceBagZ (w : V → V → ℝ) (K D : ℕ) : ℝ :=
  partitionWeight BagEdge.Incident (sourceBagWeight w K D) univ

lemma sourceLaw_sum (w : V → V → ℝ) (K D : ℕ) (hz : sourceBagZ w K D≠0) :
    ∑ a : SourceMarked w K,sourceLaw w K D a=1 := by
  apply Marking.law_sum
  simpa only [sourcePortions_collapse,sourceBagZ] using hz

lemma sourceLaw_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (hz : 0 ≤ sourceBagZ w K D) (a : SourceMarked w K) : 0 ≤ sourceLaw w K D a := by
  unfold sourceLaw Marking.law
  rw [sourcePortions_collapse]
  exact div_nonneg (Marking.mass_nonneg _ _ (sourcePortions_nonneg w hw K D) a) hz

theorem observableA_mean (w : V → V → ℝ) (hz : 0 < partition w ∅) (K D : ℕ) :
    (∑ a : SourceMarked w K,sourceLaw w K D a*observableA w K a)=
      sourceC w K*partition w ∅/sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (fun _ => 1)
  simpa only [sourceLaw,observableA,Finset.prod_const_one,sourcePortions,Matrix.cons_val_zero,
    mul_one,sourcePortions_collapse,sourceRealPortion_full w hz,sourceC,sourceBagZ] using h

theorem observableD_mean (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hz₁ : 0 < partition w₁ ∅) (K D : ℕ) :
    (∑ a : SourceMarked w K,sourceLaw w K D a*observableD w w₁ K a)=
      sourceC w K*partition w₁ ∅/sourceBagZ w K D := by
  classical
  have h := Marking.allReal_mean BagEdge.Incident (sourcePortions w K D) (0 : Fin 3) (bagReweight w w₁ K)
  simp only [sourcePortions,Matrix.cons_val_zero] at h
  rw [bagReweight_identity w w₁ hw K,frozenPortion_full w w₁ hz₁] at h
  simpa only [sourceLaw,observableD,sourcePortions_collapse,sourceBagZ] using h

theorem observableProbe_mean (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (K D : ℕ) (e₀ : LogicalEdge V) :
    (∑ a : SourceMarked w K,sourceLaw w K D a*observableProbe w w₁ K e₀ a)=
      (sourceC w K*partition w₁ {source e₀,target e₀}/D)/sourceBagZ w K D := by
  classical
  have h := Marking.fixed_probe_mean BagEdge.Incident BagEdge.exists_incident
    (sourcePortions w K D) (0 : Fin 3) 2 (probePartial w K e₀) (bagReweight w w₁ K)
  simp only [sourcePortions,Matrix.cons_val_zero,Matrix.cons_val_two,
    probePartial,Finset.prod_singleton,probePortion_on] at h
  rw [bagReweight_identity w w₁ hw K,probe_survivors,frozenPortion_probe] at h
  calc
    _ = ((1/(D:ℝ))*(sourceC w K*partition w₁ {source e₀,target e₀}))/sourceBagZ w K D := by
      simpa [sourceLaw,observableProbe,sourcePortions_collapse,sourceBagZ,Matrix.vecHead,Matrix.vecTail] using h
    _ = _ := by ring

lemma observableA_range (w : V → V → ℝ) (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableA w K a ∧ observableA w K a ≤ 1 := by
  classical
  unfold observableA
  split_ifs <;> norm_num

lemma observableD_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y)
    (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableD w w₁ K a ∧ observableD w w₁ K a ≤ 1 := by
  classical
  unfold observableD
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one₀ (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

lemma observableProbe_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,w₁ x y ≤ w x y)
    (K : ℕ) (e₀ : LogicalEdge V) (a : SourceMarked w K) :
    0 ≤ observableProbe w w₁ K e₀ a ∧ observableProbe w w₁ K e₀ a ≤ 1 := by
  classical
  unfold observableProbe
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one₀ (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

end MatchingFPRAS.Enlargement

end OAI
