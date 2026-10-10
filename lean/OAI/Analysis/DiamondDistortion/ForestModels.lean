import OAI.Analysis.DiamondDistortion.Orthogonality

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

def ForestNode := {hw : ℕ × List ℕ // 1 ≤ hw.1 ∧ hw.2.length ≤ hw.1}

def ForestAncestor (a b : ForestNode) : Prop :=
  a.val.1 = b.val.1 ∧ a.val.2.IsPrefix b.val.2

@[instance_reducible] def forestAncestry : Ancestry ForestNode where
  le := ForestAncestor
  lt a b := ForestAncestor a b ∧ ¬ ForestAncestor b a
  le_refl a := ⟨rfl, List.prefix_refl _⟩
  le_trans _ _ _ hab hbc := ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩
  le_antisymm a b hab hba := by
    apply Subtype.ext
    exact Prod.ext hab.1 (hab.2.sublist.antisymm hba.2.sublist)
  predecessors_total hab hac := by
    rcases List.prefix_or_prefix_of_prefix hab.2 hac.2 with h | h
    · exact Or.inl ⟨hab.1.trans hac.1.symm, h⟩
    · exact Or.inr ⟨hac.1.trans hab.1.symm, h⟩

def forestSegments : SegmentSystem ForestNode :=
  Ancestry.segments (A := forestAncestry)

/-- Prefix order on all finite words, explicitly distinct from their lexicographic order. -/
@[instance_reducible] def infiniteAncestry : Ancestry (List ℕ) where
  le := List.IsPrefix
  lt a b := a.IsPrefix b ∧ ¬ b.IsPrefix a
  le_refl := List.prefix_refl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ hab hba := hab.sublist.antisymm hba.sublist
  predecessors_total := List.prefix_or_prefix_of_prefix

/-- The infinite-height tree of all finite words; this includes the empty root. -/
def infiniteSegments : SegmentSystem (List ℕ) :=
  Ancestry.segments (A := infiniteAncestry)

lemma infinite_finite_heads : ∀ S : Finset (List ℕ), ∃ K : Finset (List ℕ),
    S ⊆ K ∧ Ancestry.Ancestral (A := infiniteAncestry) (K : Set (List ℕ)) := by
  apply Ancestry.finite_heads_of_predecessors (A := infiniteAncestry)
  intro b
  exact b.inits.toFinset.finite_toSet.subset (by
    intro a ha
    exact List.mem_toFinset.mpr ((List.mem_inits a b).mpr ha))

lemma forest_finite_heads : ∀ S : Finset ForestNode, ∃ K : Finset ForestNode,
    S ⊆ K ∧ Ancestry.Ancestral (A := forestAncestry) (K : Set ForestNode) := by
  apply Ancestry.finite_heads_of_predecessors (A := forestAncestry)
  intro b
  have hfin : (({b.val.1} : Set ℕ) ×ˢ (b.val.2.inits.toFinset : Set (List ℕ))).Finite :=
    (Set.finite_singleton _).prod b.val.2.inits.toFinset.finite_toSet
  have hpre := hfin.preimage (f := (Subtype.val : ForestNode → ℕ × List ℕ)) Subtype.val_injective.injOn
  apply hpre.subset
  intro a ha
  exact ⟨ha.1, List.mem_toFinset.mpr ((List.mem_inits _ _).mpr ha.2)⟩

namespace Forest

def component (v : ForestNode) : ℕ := v.val.1

lemma same_component (S : Finset ForestNode) (hS : forestSegments.IsSegment S)
    (u : ForestNode) (hu : u ∈ S) (v : ForestNode) (hv : v ∈ S) :
    component u=component v := by
  obtain ⟨a,b,_,hm⟩ := hS
  exact ((hm u).mp hu).2.1.trans ((hm v).mp hv).2.1.symm

lemma segment_card_le (S : Finset ForestNode) (hS : forestSegments.IsSegment S)
    (u : ForestNode) (hu : u ∈ S) : S.card ≤ component u+1 := by
  obtain ⟨a,b,_,hm⟩ := hS
  have hcard : S.card ≤ (Finset.range (component b+1)).card := by
    apply Finset.card_le_card_of_injOn (fun v : ForestNode => v.val.2.length)
    · intro v hv
      have hvb := ((hm v).mp hv).2
      apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le (hvb.2.length_le.trans b.property.2)
    · intro v hv w hw he
      have hvb := ((hm v).mp hv).2
      have hwb := ((hm w).mp hw).2
      have hword : v.val.2=w.val.2 := by
        rcases List.prefix_or_prefix_of_prefix hvb.2 hwb.2 with h | h
        · exact h.eq_of_length he
        · exact (h.eq_of_length he.symm).symm
      exact Subtype.ext (Prod.ext (hvb.1.trans hwb.1.symm) hword)
  rw [Finset.card_range] at hcard
  have he : component u=component b := ((hm u).mp hu).2.1
  rwa [he]

lemma primal_sq_bounded_components (C : Finset ℕ) (p : ForestNode →₀ ℝ)
    (hp : ∀ v ∈ p.support, component v ∈ C) :
    (forestSegments.primalSeminorm p)^2 ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*(∑ v ∈ p.support,p v^2) := by
  apply forestSegments.primal_sq_le_of_segment p (by positivity)
  intro S hS
  by_cases hz : (∑ v ∈ S,p v)=0
  · rw [hz,zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  obtain ⟨u,hu,hpu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  have hcu := hp u (Finsupp.mem_support_iff.mpr hpu)
  have hcard : (S.card : ℝ) ≤ ((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1 := by
    have h := (segment_card_le S hS u hu).trans (Nat.add_le_add_right (Finset.le_sup (f := id) hcu) 1)
    exact_mod_cast h
  exact sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right hcard
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

def coefficients (C : Finset ℕ) (x : forestSegments.Dual) (v : ForestNode) : ℝ :=
  if component v ∈ C then x (forestSegments.unitVector v) else 0

lemma coefficients_bounded (C : Finset ℕ) (x : forestSegments.Dual) (S : Finset ForestNode) :
    (∑ v ∈ S,coefficients C x v^2) ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*‖x‖^2 := by
  classical
  let a := coefficients C x
  let p := SegmentSystem.finiteArray S a
  let B := ∑ v ∈ S,a v^2
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : ∀ v ∈ p.support,component v ∈ C := by
    intro v hv
    by_contra hn
    have hav : a v=0 := ite_eq_right hn
    have hpv : p v=0 := by rw [SegmentSystem.finiteArray_apply,hav]; split_ifs <;> rfl
    exact (Finsupp.mem_support_iff.mp hv) hpv
  have hpenergy := primal_sq_bounded_components C p hp
  rw [SegmentSystem.finiteArray_energy] at hpenergy
  have he : x (forestSegments.finiteEmbedding p)=B := by
    rw [forestSegments.finiteArray_pairing]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [a,coefficients]
    split_ifs <;> ring
  have hval : B ≤ ‖x‖*forestSegments.primalSeminorm p := by
    rw [← he]
    exact (Real.le_norm_self _).trans (by
      simpa only [SegmentSystem.finiteEmbedding_norm] using x.le_opNorm (forestSegments.finiteEmbedding p))
  have hsq := (sq_le_sq₀ hB
    (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).2 hval
  have hmul := mul_le_mul_of_nonneg_left hpenergy (sq_nonneg ‖x‖)
  change B ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*‖x‖^2
  by_contra hn
  have hpos : 0 < B := lt_of_le_of_lt (by positivity) (lt_of_not_ge hn)
  have hc := mul_pos hpos (sub_pos.mpr (lt_of_not_ge hn))
  change (forestSegments.primalSeminorm p)^2 ≤ (((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*B at hpenergy
  change ‖x‖^2*(forestSegments.primalSeminorm p)^2 ≤ ‖x‖^2*((((C.sup (id : ℕ → ℕ) : ℕ) : ℝ)+1)*B) at hmul
  nlinarith only [hsq,hmul,hc]

lemma finite_component_tail (C : Finset ℕ) (x : forestSegments.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ForestNode, ∀ p : ForestNode →₀ ℝ,
      (∀ v ∈ p.support, component v ∈ C) → (∀ v ∈ p.support,v ∉ S) →
      |x (forestSegments.finiteEmbedding p)| ≤ ε*forestSegments.primalSeminorm p := by
  classical
  obtain ⟨S,hS⟩ := SegmentSystem.finite_square_tails (coefficients C x)
    (coefficients_bounded C x) (sq_pos_of_pos hε)
  refine ⟨S,?_⟩
  intro p hp hout
  have hd : Disjoint S p.support := Finset.disjoint_left.mpr (fun v hv hvs => hout v hvs hv)
  have ha : Real.sqrt (∑ v ∈ p.support,coefficients C x v^2) ≤ ε :=
    (Real.sqrt_le_left hε.le).mpr (hS p.support hd).le
  have hb : Real.sqrt (∑ v ∈ p.support,p v^2) ≤ forestSegments.primalSeminorm p :=
    (Real.sqrt_le_left (apply_nonneg _ _)).mpr (forestSegments.coordinate_energy_le p p.support)
  have he : x (forestSegments.finiteEmbedding p) =
      ∑ v ∈ p.support,p v*coefficients C x v := by
    rw [SegmentSystem.finiteEmbedding_apply,SegmentSystem.dual_coe_apply]
    apply Finset.sum_congr rfl
    intro v hv
    rw [coefficients,ite_eq_left (hp v hv)]
    rfl
  rw [he]
  calc
    _ ≤ ∑ v ∈ p.support, |p v| * |coefficients C x v| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun v => p v*coefficients C x v) p.support
    _ ≤ Real.sqrt (∑ v ∈ p.support,p v^2) * Real.sqrt (∑ v ∈ p.support,coefficients C x v^2) := by
      simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt p.support
        (fun v => |p v|) (fun v => |coefficients C x v|)
    _ ≤ forestSegments.primalSeminorm p * ε := mul_le_mul hb ha (Real.sqrt_nonneg _) (apply_nonneg _ _)
    _ = _ := mul_comm _ _

lemma component_set_ancestral (C : Finset ℕ) :
    Ancestry.Ancestral (A := forestAncestry) {v : ForestNode | component v ∈ C} := by
  intro a b hab hb
  change ForestAncestor a b at hab
  change component a ∈ C
  change component b ∈ C at hb
  have he : component a=component b := hab.1
  rwa [he]

/-- The full finite-height forest dual really has finite ancestral head
    approximation. Both the component tail and coordinate tail arguments are
    proved from its disjoint-segment norm, rather than imposed as hypotheses. -/
lemma full_dual_approximation (x : forestSegments.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ForestNode, Ancestry.Ancestral (A := forestAncestry) (H : Set ForestNode) ∧
      ‖forestSegments.tailDual H x‖ < ε := by
  classical
  have hd : 0 < ε/4 := by positivity
  obtain ⟨C,hC⟩ := forestSegments.small_color_tail component same_component x hd
  obtain ⟨S,hS⟩ := finite_component_tail C x hd
  obtain ⟨H,hSH,hH⟩ := forest_finite_heads S
  refine ⟨H,hH,?_⟩
  have hbound : ‖forestSegments.tailDual H x‖ ≤ ε/2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    induction u using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih u =>
      let p := forestSegments.ofPrimal u
      let q := p.filter (fun v => v ∉ H)
      let qi := q.filter (fun v => component v ∈ C)
      let qo := q.filter (fun v => component v ∉ C)
      have hqi : ∀ v ∈ qi.support,component v ∈ C := by
        intro v hv
        rw [Finsupp.support_filter] at hv
        exact (Finset.mem_filter.mp hv).2
      have hqiS : ∀ v ∈ qi.support,v ∉ S := by
        intro v hv hvs
        rw [Finsupp.support_filter] at hv
        have hvq := (Finset.mem_filter.mp hv).1
        rw [Finsupp.support_filter] at hvq
        exact (Finset.mem_filter.mp hvq).2 (hSH hvs)
      have hqo : ∀ v ∈ qo.support,component v ∉ C := by
        intro v hv
        rw [Finsupp.support_filter] at hv
        exact (Finset.mem_filter.mp hv).2
      have hi := hS qi hqi hqiS
      have ho := hC qo hqo
      have hqin : forestSegments.primalSeminorm qi ≤ forestSegments.primalSeminorm q := by
        change (Ancestry.segments (A := forestAncestry)).primalSeminorm qi ≤
          (Ancestry.segments (A := forestAncestry)).primalSeminorm q
        convert Ancestry.primal_filter_le (A := forestAncestry) (component_set_ancestral C) q using 1
        all_goals dsimp [qi,qo]; congr
      have hqon : forestSegments.primalSeminorm qo ≤ forestSegments.primalSeminorm q := by
        change (Ancestry.segments (A := forestAncestry)).primalSeminorm qo ≤
          (Ancestry.segments (A := forestAncestry)).primalSeminorm q
        convert Ancestry.primal_filter_tail_le (A := forestAncestry) (component_set_ancestral C) q using 1
        all_goals dsimp [qi,qo]; congr
      have hqn : forestSegments.primalSeminorm q ≤ forestSegments.primalSeminorm p := by
        change (Ancestry.segments (A := forestAncestry)).primalSeminorm q ≤
          (Ancestry.segments (A := forestAncestry)).primalSeminorm p
        convert Ancestry.primal_filter_tail_le (A := forestAncestry) hH p using 1
        all_goals dsimp [q]; congr
      have hsum : qi+qo=q := by
        apply Finsupp.ext
        intro v
        by_cases hv : component v ∈ C <;> simp [qi,qo]
      have he : forestSegments.tailDual H x (u : forestSegments.JamesSpace) =
          x (forestSegments.finiteEmbedding q) := by
        rw [SegmentSystem.tailDual_apply_apply,SegmentSystem.headPrimal_coe,
          ← UniformSpace.Completion.coe_sub,SegmentSystem.sub_filterPrimal]
        congr 2
        apply Finsupp.ext
        intro v
        simp [SegmentSystem.filterPrimal,q,p,SegmentSystem.ofPrimal]
        congr
      rw [he,Real.norm_eq_abs,UniformSpace.Completion.norm_coe,SegmentSystem.norm_eq_primal]
      calc
        _ = |x (forestSegments.finiteEmbedding qi)+x (forestSegments.finiteEmbedding qo)| := by
          rw [← hsum,map_add,map_add]
        _ ≤ |x (forestSegments.finiteEmbedding qi)|+|x (forestSegments.finiteEmbedding qo)| := abs_add_le _ _
        _ ≤ (ε/4)*forestSegments.primalSeminorm qi+(ε/4)*forestSegments.primalSeminorm qo := add_le_add hi ho
        _ ≤ (ε/4)*forestSegments.primalSeminorm q+(ε/4)*forestSegments.primalSeminorm q :=
          add_le_add (mul_le_mul_of_nonneg_left hqin hd.le) (mul_le_mul_of_nonneg_left hqon hd.le)
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hqn hd.le]
  exact lt_of_le_of_lt hbound (by linarith)

end Forest

abbrev ForestDual := forestSegments.Dual
abbrev InfinitePredual := infiniteSegments.CoordinatePredual

end DiamondDistortion

end

end OAI
