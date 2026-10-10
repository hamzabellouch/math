import Mathlib
import OAI.Probability.UnimodularPercolation.Splicing.Geometry

namespace OAI

/-! Gap Codes for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceExecution
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev SpliceState (E : Type v) := Set E × (ℕ → Set E)

 

def exchangeState (mask : Set E) (i : ℕ) (s : SpliceState E) : SpliceState E :=
  (exchangeOn mask s.1 (s.2 i), Function.update s.2 i (exchangeOn mask (s.2 i) s.1))

@[simp] theorem exchangeState_first (mask : Set E) (i : ℕ) (s : SpliceState E) :
    (exchangeState mask i s).1 = exchangeOn mask s.1 (s.2 i) := rfl

@[simp] theorem exchangeState_at (mask : Set E) (i : ℕ) (s : SpliceState E) :
    (exchangeState mask i s).2 i = exchangeOn mask (s.2 i) s.1 := by
  simp [exchangeState]

theorem exchangeState_away (mask : Set E) (i l : ℕ) (s : SpliceState E) (hli : l ≠ i) :
    (exchangeState mask i s).2 l = s.2 l := by
  simp [exchangeState, Function.update_of_ne hli]

theorem exchangeState_involutive (mask : Set E) (i : ℕ) :
    Function.Involutive (exchangeState mask i (E := E)) := by
  intro s
  apply Prod.ext
  · simp only [exchangeState_first, exchangeState_at]
    exact exchangeOn_involutive mask s.1 (s.2 i)
  · funext l
    by_cases hli : l = i
    · subst l
      simp only [exchangeState_at, exchangeState_first]
      exact exchangeOn_involutive mask (s.2 i) s.1
    · rw [exchangeState_away _ _ _ _ hli, exchangeState_away _ _ _ _ hli]

 

def undoState (G : BondGraph V E) (x : V) (q : ℕ × E) (s : SpliceState E) :
    SpliceState E := exchangeState (recoveredMask G s.1 x q.2) q.1 s

 

def ValidSpliceStep (G : BondGraph V E) (x : V) (s : SpliceState E)
    (q : ℕ × E) (s' : SpliceState E) : Prop :=
  ∃ y a b,
    y ∉ cluster G s.1 x ∧ q.2 ∈ s.2 q.1 ∧ G q.2 = s(a,b) ∧
    a ∈ cluster G s.1 x ∧
    b ∈ cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y ∧
    s' = exchangeState
      (spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2) q.1 s

theorem undoState_of_valid (G : BondGraph V E) (x : V) (s s' : SpliceState E)
    (q : ℕ × E) (h : ValidSpliceStep G x s q s') : undoState G x q s' = s := by
  obtain ⟨y,a,b,hy,he,hab,ha,hb,rfl⟩ := h
  unfold undoState
  rw [show recoveredMask G
      (exchangeState (spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2) q.1 s).1 x q.2 =
      spliceMask G (cluster G s.1 x)
        (cluster G (s.2 q.1 ∩ internalEdges G (cluster G s.1 x)ᶜ) y) q.2 from
    recoveredMask_splice G s.1 (s.2 q.1) x y hy q.2 a b hab he ha hb]
  exact exchangeState_involutive _ _ s

 
inductive SpliceExecution (G : BondGraph V E) (x : V) :
    SpliceState E → List (ℕ × E) → SpliceState E → Prop
  | nil (s) : SpliceExecution G x s [] s
  | cons (s s' s'') (q qs)
      (hstep : ValidSpliceStep G x s q s')
      (hrest : SpliceExecution G x s' qs s'') : SpliceExecution G x s (q::qs) s''

 
def undoExecution (G : BondGraph V E) (x : V) :
    List (ℕ × E) → SpliceState E → SpliceState E
  | [], s => s
  | q::qs, s => undoState G x q (undoExecution G x qs s)

theorem SpliceExecution.undo (G : BondGraph V E) (x : V)
    (s s' : SpliceState E) (code : List (ℕ × E))
    (h : SpliceExecution G x s code s') : undoExecution G x code s' = s := by
  induction h with
  | nil => rfl
  | cons s s' s'' q qs hstep hrest ih =>
    change undoState G x q (undoExecution G x qs s'') = s
    rw [ih]
    exact undoState_of_valid G x s s' q hstep

 

theorem SpliceExecution.input_unique (G : BondGraph V E) (x : V)
    (s₁ s₂ out : SpliceState E) (code : List (ℕ × E))
    (h₁ : SpliceExecution G x s₁ code out) (h₂ : SpliceExecution G x s₂ code out) :
    s₁ = s₂ := by
  exact (h₁.undo G x s₁ out code).symm.trans (h₂.undo G x s₂ out code)

 

theorem SpliceTrace.realize (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (code : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω code ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
    ∃ θf, SpliceExecution G x (ω,θ) code (ωf,θf) := by
  induction h with
  | stop j ω hz =>
    intro θ _
    exact ⟨θ, SpliceExecution.nil _⟩
  | @step j i ω e a b rest ωf _ hji hik _ hy he hab ha hb ht ih =>
    intro θ hθ
    have hθi := hθ i hji hik
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let mask := spliceMask G S B e
    let next := exchangeState mask i (ω,θ)
    have hnext : next.1 = spliceField G S B e ω (η i) := by
      change exchangeOn mask ω (θ i) = exchangeOn mask ω (η i)
      rw [hθi]
    obtain ⟨θf,hexec⟩ := ih next.2 (by
      intro l hil hlk
      rw [exchangeState_away _ _ _ _ (by omega)]
      exact hθ l (hji.trans hil) hlk)
    refine ⟨θf, SpliceExecution.cons (ω,θ) next (ωf,θf) (i,e) rest ?_ ?_⟩
    · refine ⟨y i,a,b,hy,?_,hab,ha,?_,?_⟩
      · simpa only [hθi] using he
      · simpa only [hθi] using hb
      · dsimp only [next, mask, B, S]
        rw [hθi]
    · change SpliceExecution G x (next.1,next.2) rest (ωf,θf)
      rw [hnext]
      exact hexec

end SpliceExecution

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeCode
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pivotal_mem_trail (G : BondGraph V E) (ω : Set E) (x z : V)
    (l : List E) (hl : Along G x l z) (hopen : ∀ e ∈ l, e ∈ ω)
    {e : E} (he : OpenMarkedPivotal G ω {z} x e) : e ∈ l := by
  by_contra hnot
  apply he.2.2
  refine ⟨z,rfl,hl.conn ?_⟩
  intro f hf
  exact ⟨hopen f hf,fun hfe => hnot ((Set.mem_singleton_iff.mp hfe) ▸ hf)⟩

 
theorem finite_separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) :
    {e | OpenMarkedPivotal G ω {z} x e}.Finite := by
  by_cases hc : Conn G ω x z
  · obtain ⟨l,hl,_,ho⟩ := conn_exists_bond_trail G hc
    exact l.toFinset.finite_toSet.subset fun e he =>
      List.mem_toFinset.mpr (pivotal_mem_trail G ω x z l hl ho he)
  · have hempty : {e | OpenMarkedPivotal G ω {z} x e} = ∅ := by
      ext e
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      rintro ⟨_,⟨y,hy,hxy⟩,_⟩
      exact hc ((Set.mem_singleton_iff.mp hy) ▸ hxy)
    rw [hempty]
    exact Set.finite_empty

noncomputable def separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) : Finset E :=
  (finite_separatingBonds G ω x z).toFinset

@[simp] theorem mem_separatingBonds (G : BondGraph V E) (ω : Set E) (x z : V) (e : E) :
    e ∈ separatingBonds G ω x z ↔ OpenMarkedPivotal G ω {z} x e := by
  exact (finite_separatingBonds G ω x z).mem_toFinset

 
theorem pivotalRank_injective_of_cluster_finite (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) :
    Set.InjOn (pivotalRank G ω x) {e | OpenMarkedPivotal G ω m x e} := by
  have hcut (f : E) : (cluster G (ω \ {f}) x).Finite :=
    hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
  intro e he f hf heq
  by_contra hne
  rcases pivotal_rootSides_nested G ω m x he hf hne with h | h
  · exact (Nat.ne_of_lt (Set.ncard_lt_ncard h (hcut f))) heq
  · exact (Nat.ne_of_lt (Set.ncard_lt_ncard h (hcut e))) heq.symm

 

noncomputable def bridgeIndex (G : BondGraph V E) (ω : Set E) (x z : V) (e : E) : ℕ :=
  ((separatingBonds G ω x z).filter fun f => pivotalRank G ω x f ≤ pivotalRank G ω x e).card

theorem bridgeIndex_pos (G : BondGraph V E) (ω : Set E) (x z : V) {e : E}
    (he : OpenMarkedPivotal G ω {z} x e) : 0 < bridgeIndex G ω x z e := by
  apply Finset.card_pos.mpr
  exact ⟨e,Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z e).mpr he,le_refl _⟩⟩

theorem bridgeIndex_lt_of_rank_lt (G : BondGraph V E) (ω : Set E) (x z : V) {e f : E}
    (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    bridgeIndex G ω x z e < bridgeIndex G ω x z f := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      (Finset.mem_filter.mp hd).2.trans (Nat.le_of_lt hlt)⟩
  · intro heq
    have hmem : f ∈ (separatingBonds G ω x z).filter
        (fun d => pivotalRank G ω x d ≤ pivotalRank G ω x f) :=
      Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z f).mpr hf,le_refl _⟩
    rw [← heq] at hmem
    exact (Nat.not_le_of_lt hlt) (Finset.mem_filter.mp hmem).2

theorem bridgeIndex_injective (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) :
    Set.InjOn (bridgeIndex G ω x z) {e | OpenMarkedPivotal G ω {z} x e} := by
  intro e he f hf heq
  apply pivotalRank_injective_of_cluster_finite G ω {z} x hC he hf
  rcases lt_trichotomy (pivotalRank G ω x e) (pivotalRank G ω x f) with h | h | h
  · exact ((Nat.ne_of_lt (bridgeIndex_lt_of_rank_lt G ω x z hf h)) heq).elim
  · exact h
  · exact ((Nat.ne_of_lt (bridgeIndex_lt_of_rank_lt G ω x z he h)) heq.symm).elim

 
noncomputable def ordinalSpliceCode (G : BondGraph V E) (ω : Set E) (x z : V)
    (code : List (ℕ × E)) : List (ℕ × ℕ) :=
  code.map fun q => (q.1,bridgeIndex G ω x z q.2)

theorem ordinalSpliceCode_injective (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) (c₁ c₂ : List (ℕ × E))
    (h₁ : ∀ q ∈ c₁, OpenMarkedPivotal G ω {z} x q.2)
    (h₂ : ∀ q ∈ c₂, OpenMarkedPivotal G ω {z} x q.2)
    (heq : ordinalSpliceCode G ω x z c₁ = ordinalSpliceCode G ω x z c₂) : c₁ = c₂ := by
  induction c₁ generalizing c₂ with
  | nil =>
    cases c₂ with
    | nil => rfl
    | cons q qs => simp [ordinalSpliceCode] at heq
  | cons q qs ih =>
    cases c₂ with
    | nil => simp [ordinalSpliceCode] at heq
    | cons r rs =>
      have heq' := List.cons.inj heq
      have hqr : q = r := by
        apply Prod.ext
        · exact congrArg (fun t : ℕ × ℕ => t.1) heq'.1
        · exact bridgeIndex_injective G ω x z hC (h₁ q (by simp)) (h₂ r (by simp))
            (congrArg Prod.snd heq'.1)
      exact congrArg₂ List.cons hqr (ih rs
        (fun a ha => h₁ a (List.mem_cons_of_mem _ ha))
        (fun a ha => h₂ a (List.mem_cons_of_mem _ ha)) heq'.2)

 

theorem SpliceTrace.input_unique_of_ordinalCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : ordinalSpliceCode G ωf x (y₁ k) c₁ = ordinalSpliceCode G ωf x (y₁ k) c₂)
    (θf : ℕ → Set E)
    (he₁ : SpliceExecution G x (ω₁,η₁) c₁ (ωf,θf))
    (he₂ : SpliceExecution G x (ω₂,η₂) c₂ (ωf,θf)) :
    (ω₁,η₁) = (ω₂,η₂) := by
  have hc : c₁ = c₂ := ordinalSpliceCode_injective G ωf x (y₁ k) hC c₁ c₂
    (ht₁.seams_pivotal G x η₁ y₁ k j ω₁ ωf c₁)
    (by simpa only [hz] using ht₂.seams_pivotal G x η₂ y₂ k j ω₂ ωf c₂) heq
  subst c₂
  exact he₁.input_unique G x (ω₁,η₁) (ω₂,η₂) (ωf,θf) c₁ he₂

end BridgeCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def domainBits (Q : Finset E) (ω : Set E) : Finset E := Q.filter (· ∈ ω)

@[simp] theorem mem_domainBits (Q : Finset E) (ω : Set E) (e : E) :
    e ∈ domainBits Q ω ↔ e ∈ Q ∧ e ∈ ω := Finset.mem_filter

theorem domainBits_subset (Q : Finset E) (ω : Set E) : domainBits Q ω ⊆ Q :=
  Finset.filter_subset _ _

theorem domainBits_exchange (Q : Finset E) (M ω η : Set E) :
    domainBits Q (exchangeOn M ω η) =
      finiteExchange (domainBits Q M) (domainBits Q ω) (domainBits Q η) := by
  ext e
  simp only [mem_domainBits,exchangeOn,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,
    finiteExchange,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
  tauto

 

noncomputable def spliceTupleWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) : ℝ :=
  bernoulliWeight Q (domainBits Q s.1) p *
    ∏ i ∈ J, bernoulliWeight Q (domainBits Q (s.2 i)) p

theorem spliceTupleWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (s : SpliceState E) : 0 ≤ spliceTupleWeight Q J p s := by
  exact mul_nonneg (bernoulliWeight_nonneg _ _ p)
    (Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p)

 
theorem spliceTupleWeight_exchange (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : SpliceState E) (M : Set E) (i : ℕ) (hi : i ∈ J) :
    spliceTupleWeight Q J p (exchangeState M i s) = spliceTupleWeight Q J p s := by
  unfold spliceTupleWeight
  rw [← Finset.mul_prod_erase J (fun l =>
    bernoulliWeight Q (domainBits Q ((exchangeState M i s).2 l)) p) hi,
    ← Finset.mul_prod_erase J (fun l => bernoulliWeight Q (domainBits Q (s.2 l)) p) hi]
  have herase : (∏ l ∈ J.erase i,
      bernoulliWeight Q (domainBits Q ((exchangeState M i s).2 l)) p) =
      ∏ l ∈ J.erase i, bernoulliWeight Q (domainBits Q (s.2 l)) p := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [exchangeState_away _ _ _ _ (Finset.mem_erase.mp hl).1]
  rw [herase,exchangeState_first,exchangeState_at,← mul_assoc,← mul_assoc,
    domainBits_exchange,domainBits_exchange,
    bernoulliWeight_exchange _ _ _ _ (domainBits_subset Q s.1) (domainBits_subset Q (s.2 i)) p]

 
theorem SpliceExecution.weight (G : BondGraph V E) (x : V)
    (s s' : SpliceState E) (code : List (ℕ × E))
    (h : SpliceExecution G x s code s') (Q : Finset E) (J : Finset ℕ)
    (hJ : ∀ q ∈ code, q.1 ∈ J) (p : ℝ) :
    spliceTupleWeight Q J p s' = spliceTupleWeight Q J p s := by
  induction h with
  | nil => rfl
  | cons s s' s'' q code hstep hrest ih =>
    rw [ih (fun r hr => hJ r (List.mem_cons_of_mem _ hr))]
    obtain ⟨y,a,b,_,_,_,_,_,rfl⟩ := hstep
    exact spliceTupleWeight_exchange Q J p s _ q.1 (hJ q (List.mem_cons_self ..))

 

theorem splice_finite_weight_comparison (G : BondGraph V E) (x : V)
    (Q : Finset E) (J : Finset ℕ) (p : unitInterval) (code : List (ℕ × E))
    (hJ : ∀ q ∈ code, q.1 ∈ J) (A B : Finset (SpliceState E))
    (F : SpliceState E → SpliceState E)
    (hex : ∀ s ∈ A, SpliceExecution G x s code (F s))
    (hB : ∀ s ∈ A, F s ∈ B) :
    (∑ s ∈ A, spliceTupleWeight Q J p s) ≤ ∑ s ∈ B, spliceTupleWeight Q J p s := by
  have hinj : Set.InjOn F (A : Set (SpliceState E)) := by
    intro s hs t ht heq
    exact (hex s hs).input_unique G x s t (F s) code (heq.symm ▸ hex t ht)
  have hweight : (∑ s ∈ A, spliceTupleWeight Q J p s) =
      ∑ s ∈ A.image F, spliceTupleWeight Q J p s := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro s hs
    exact ((hex s hs).weight G x s (F s) code Q J hJ p).symm
  rw [hweight]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ht
    exact hB s hs
  · intro s _ _
    exact spliceTupleWeight_nonneg Q J p s

end SpliceWeight

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem pivotalRank_lt_iff_of_cluster_finite (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω m x e) (hf : OpenMarkedPivotal G ω m x f) :
    pivotalRank G ω x e < pivotalRank G ω x f ↔
      f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ := by
  have hcut (q : E) : (cluster G (ω \ {q}) x).Finite :=
    hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
  have hexterior (hout : f ∈ internalEdges G (cluster G (ω \ {e}) x)ᶜ) : e ≠ f := by
    obtain ⟨a,b,hab,hxa,_,_⟩ := openMarkedPivotal_oriented G ω m x he
    intro h; subst f
    exact ((mem_internalEdges_of_ends G _ e a b hab).mp hout).1 hxa
  constructor
  · intro hlt
    have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
    rcases pivotal_other_sides G ω m x he hf hne.symm with hinside | hout
    · obtain ⟨a,b,hab,_,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
      obtain ⟨y,hy,hby⟩ := hbm
      have hby' : Conn G (ω \ {f}) b y := conn_mono G
        (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩)
        (conn_delete_internal_of_outside G (ω \ {e}) x hinside hxb hby)
      have hb : b ∉ cluster G (ω \ {f}) x := fun h => hf.2.2 ⟨y,hy,h.trans hby'⟩
      have ha : a ∉ cluster G (ω \ {f}) x := fun h =>
        hb ((edge_cluster_sides G (ω \ {f}) x ⟨he.1,hne⟩ hab).mp h)
      have hs := pivotal_rootSide_ssubset G ω m x hf hne.symm
        ((mem_internalEdges_of_ends G _ e a b hab).mpr ⟨ha,hb⟩)
      have hrev := Set.ncard_lt_ncard hs (hcut e)
      exact (Nat.not_lt_of_ge (Nat.le_of_lt hrev) hlt).elim
    · exact hout
  · intro hout
    exact Set.ncard_lt_ncard (pivotal_rootSide_ssubset G ω m x he (hexterior hout) hout) (hcut f)

theorem pivotal_internal_of_rank_lt (G : BondGraph V E) (ω : Set E)
    (m : Set V) (x : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω m x e) (hf : OpenMarkedPivotal G ω m x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    e ∈ internalEdges G (cluster G (ω \ {f}) x) := by
  have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  rcases pivotal_other_sides G ω m x hf he hne with h | h
  · exact h
  · have hr := (pivotalRank_lt_iff_of_cluster_finite G ω m x hC hf he).mpr h
    omega

 
theorem conn_far_end_avoids_later_pivotal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hg : OpenMarkedPivotal G ω {z} x g)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x g)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a) :
    Conn G (ω \ {g}) x b := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp hlt
  have hne : e ≠ g := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  have hc : Conn G (ω \ {g}) x a :=
    conn_mono G (ω₁ := (ω \ {e}) \ {g}) (ω₂ := ω \ {g}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_exterior_of_inside G (ω \ {e}) x hout (conn_refl G _ x) ha)
  exact hc.tail ⟨e,⟨he.1,hne⟩,hab⟩

 
theorem conn_near_end_avoids_earlier_pivotal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {f g : E}
    (hf : OpenMarkedPivotal G ω {z} x f) (hg : OpenMarkedPivotal G ω {z} x g)
    (hlt : pivotalRank G ω x g < pivotalRank G ω x f)
    (c d : V) (hcd : G f = s(c,d)) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z) : Conn G (ω \ {g}) c z := by
  have hin := pivotal_internal_of_rank_lt G ω {z} x hC hg hf hlt
  have hne : f ≠ g := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h.symm)
  have hc : Conn G (ω \ {g}) d z :=
    conn_mono G (ω₁ := (ω \ {f}) \ {g}) (ω₂ := ω \ {g}) (fun _ h => ⟨h.1.1,h.2⟩)
      (conn_delete_internal_of_outside G (ω \ {f}) x hin hd hdz)
  exact (Relation.ReflTransGen.single ⟨f,⟨hf.1,hne⟩,hcd⟩).trans hc

 

theorem pivotal_between_is_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hg : OpenMarkedPivotal G ω {z} x g)
    (heg : pivotalRank G ω x e < pivotalRank G ω x g)
    (hgf : pivotalRank G ω x g < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    OpenMarkedPivotal G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) {c} b g := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp heg
  have hin := pivotal_internal_of_rank_lt G ω {z} x hC hg hf hgf
  refine ⟨⟨hg.1,fun v hv => ⟨hin v hv,hout v hv⟩⟩,⟨c,rfl,hbc⟩,?_⟩
  rintro ⟨w,hw,hbw⟩
  have hbc' : Conn G (ω \ {g}) b c := by
    have hw' : w = c := Set.mem_singleton_iff.mp hw
    subst w
    apply conn_mono G ?_ hbw
    intro q hq
    exact ⟨hq.1.1,hq.2⟩
  apply hg.2.2
  exact ⟨z,rfl,(conn_far_end_avoids_later_pivotal G ω x z hC he hg heg a b hab ha).trans
    (hbc'.trans (conn_near_end_avoids_earlier_pivotal G ω x z hC hf hg hgf c d hcd hd hdz))⟩

 
theorem pivotal_after_is_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e g : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hg : OpenMarkedPivotal G ω {z} x g)
    (heg : pivotalRank G ω x e < pivotalRank G ω x g)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hbz : Conn G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z) :
    OpenMarkedPivotal G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) {z} b g := by
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hg).mp heg
  have hin : g ∈ internalEdges G (cluster G ω x) := by
    obtain ⟨u,v,huv,hxu,_,_⟩ := openMarkedPivotal_oriented G ω {z} x hg
    have hu : u ∈ cluster G ω x := conn_mono G Set.sdiff_subset hxu
    exact (mem_internalEdges_of_ends G _ g u v huv).mpr
      ⟨hu,(edge_cluster_sides G ω x hg.1 huv).mp hu⟩
  refine ⟨⟨hg.1,fun v hv => ⟨hin v hv,hout v hv⟩⟩,⟨z,rfl,hbz⟩,?_⟩
  rintro ⟨w,hw,hbw⟩
  have hbz' : Conn G (ω \ {g}) b z := by
    have hw' : w = z := Set.mem_singleton_iff.mp hw
    subst w
    apply conn_mono G ?_ hbw
    intro q hq
    exact ⟨hq.1.1,hq.2⟩
  exact hg.2.2 ⟨z,rfl,
    (conn_far_end_avoids_later_pivotal G ω x z hC he hg heg a b hab ha).trans hbz'⟩

end BridgeGapGeometry

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgeGapCount
attribute [local instance] Classical.propDecidable Classical.decEq

@[simp] theorem separatingBonds_card (G : BondGraph V E) (ω : Set E) (x z : V) :
    (separatingBonds G ω x z).card = pivotalDistance G ω x z := by
  exact Set.ncard_coe_finset (separatingBonds G ω x z) |>.symm.trans (by
    congr 1
    ext e
    exact mem_separatingBonds G ω x z e)

 
noncomputable def bridgeInterval (G : BondGraph V E) (ω : Set E) (x z : V) (e f : E) : Finset E :=
  (separatingBonds G ω x z).filter fun g =>
    pivotalRank G ω x e < pivotalRank G ω x g ∧ pivotalRank G ω x g < pivotalRank G ω x f

theorem bridgeIndex_interval_identity (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) {e f : E}
    (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f) :
    bridgeIndex G ω x z f = bridgeIndex G ω x z e + (bridgeInterval G ω x z e f).card + 1 := by
  let P := separatingBonds G ω x z
  let A := P.filter fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e
  let B := bridgeInterval G ω x z e f
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro g hgA hgB
    have h₁ := (Finset.mem_filter.mp hgA).2
    have h₂ := (Finset.mem_filter.mp hgB).2.1
    omega
  have hnot : f ∉ A ∪ B := by
    intro hh
    rcases Finset.mem_union.mp hh with h | h
    · have hr := (Finset.mem_filter.mp h).2
      omega
    · exact (Nat.lt_irrefl _) (Finset.mem_filter.mp h).2.2
  have hset : P.filter (fun g => pivotalRank G ω x g ≤ pivotalRank G ω x f) = insert f (A ∪ B) := by
    ext g
    constructor
    · intro hg
      obtain ⟨hgP,hgf⟩ := Finset.mem_filter.mp hg
      by_cases hge : g = f
      · exact Finset.mem_insert.mpr (Or.inl hge)
      · apply Finset.mem_insert.mpr
        apply Or.inr
        by_cases hga : pivotalRank G ω x g ≤ pivotalRank G ω x e
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgP,hga⟩)
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨hgP,Nat.lt_of_not_ge hga,?_⟩
          apply lt_of_le_of_ne hgf
          intro hr
          exact hge (pivotalRank_injective_of_cluster_finite G ω {z} x hC
            ((mem_separatingBonds G ω x z g).mp hgP) hf hr)
    · intro hg
      rcases Finset.mem_insert.mp hg with heq | hg
      · subst g
        exact Finset.mem_filter.mpr ⟨(mem_separatingBonds G ω x z f).mpr hf,le_refl _⟩
      · rcases Finset.mem_union.mp hg with hg | hg
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
            (Finset.mem_filter.mp hg).2.trans (Nat.le_of_lt hlt)⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
            Nat.le_of_lt (Finset.mem_filter.mp hg).2.2⟩
  change (P.filter _).card = A.card+B.card+1
  rw [hset,Finset.card_insert_of_notMem hnot,Finset.card_union_of_disjoint hdis]

theorem bridgeInterval_card_le (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    (bridgeInterval G ω x z e f).card ≤ pivotalDistance G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  rw [← separatingBonds_card]
  apply Finset.card_le_card
  intro g hg
  obtain ⟨hgP,heg,hgf⟩ := Finset.mem_filter.mp hg
  apply (mem_separatingBonds _ _ _ _ _).mpr
  exact pivotal_between_is_internal G ω x z hC he hf
    ((mem_separatingBonds G ω x z g).mp hgP) heg hgf a b c d hab hcd ha hd hdz hbc

 
theorem bridge_gap_le_internal_distance (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hd : ¬Conn G (ω \ {f}) x d)
    (hdz : Conn G (ω \ {f}) d z)
    (hbc : Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c) :
    bridgeIndex G ω x z f - bridgeIndex G ω x z e ≤
      1 + pivotalDistance G (ω ∩ internalEdges G
        (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  have hid := bridgeIndex_interval_identity G ω x z hC hf hlt
  have hle := bridgeInterval_card_le G ω x z hC he hf a b c d hab hcd ha hd hdz hbc
  omega

 
theorem bridge_terminal_gap_le_internal_distance (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e : E}
    (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hbz : Conn G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z) :
    (separatingBonds G ω x z).card + 1 - bridgeIndex G ω x z e ≤
      1 + pivotalDistance G (ω ∩ internalEdges G
        (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
  let P := separatingBonds G ω x z
  let A := P.filter fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e
  let B := P.filter fun g => pivotalRank G ω x e < pivotalRank G ω x g
  have hid : A.card + B.card = P.card := by
    simpa only [A,B,not_le] using Finset.card_filter_add_card_filter_not
      (s := P) (fun g => pivotalRank G ω x g ≤ pivotalRank G ω x e)
  have hle : B.card ≤ pivotalDistance G (ω ∩ internalEdges G
      (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
    rw [← separatingBonds_card]
    apply Finset.card_le_card
    intro g hg
    obtain ⟨hgP,heg⟩ := Finset.mem_filter.mp hg
    apply (mem_separatingBonds _ _ _ _ _).mpr
    exact pivotal_after_is_internal G ω x z hC he
      ((mem_separatingBonds G ω x z g).mp hgP) heg a b hab ha hbz
  change P.card+1-A.card ≤ _
  omega

 
theorem pivotalDistance_le_cluster_card (G : BondGraph V E) (ω : Set E) (x z : V)
    (hC : (cluster G ω x).Finite) :
    pivotalDistance G ω x z ≤ (cluster G ω x).ncard - 1 := by
  rw [← separatingBonds_card]
  let N := (cluster G ω x).ncard
  have hm : Set.MapsTo (pivotalRank G ω x) (separatingBonds G ω x z : Set E)
      (Finset.Ico 1 N : Set ℕ) := by
    intro e he
    have he' := (mem_separatingBonds G ω x z e).mp he
    have hfin : (cluster G (ω \ {e}) x).Finite :=
      hC.subset (fun _ h => conn_mono G Set.sdiff_subset h)
    have hpos : 0 < pivotalRank G ω x e :=
      (Set.ncard_pos hfin).mpr ⟨x,conn_refl G _ x⟩
    have hlt : pivotalRank G ω x e < N := by
      apply Set.ncard_lt_ncard _ hC
      refine Set.ssubset_iff_subset_ne.mpr ⟨fun v hv => conn_mono G Set.sdiff_subset hv,?_⟩
      intro heq
      obtain ⟨v,hv,hxv⟩ := he'.2.1
      apply he'.2.2
      refine ⟨v,hv,?_⟩
      change v ∈ cluster G (ω \ {e}) x
      rw [heq]
      exact hxv
    exact Finset.mem_Ico.mpr ⟨hpos,hlt⟩
  have hi : Set.InjOn (pivotalRank G ω x) (separatingBonds G ω x z : Set E) := by
    intro e he f hf h
    exact pivotalRank_injective_of_cluster_finite G ω {z} x hC
      ((mem_separatingBonds G ω x z e).mp he) ((mem_separatingBonds G ω x z f).mp hf) h
  simpa only [Nat.card_Ico,N] using Finset.card_le_card_of_injOn (pivotalRank G ω x) hm hi

 

theorem inverse_contact_weight_le (K l : ℕ) (L : ℝ) (hK : 1 ≤ K) (hl : 1 ≤ l)
    (hL : 1 ≤ L) (hgap : (l:ℝ) ≤ 1 + K*L) :
    (K:ℝ)⁻¹ ≤ min 1 (2*L/l) := by
  have hKr : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hlr : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hKpos : (0:ℝ) < K := lt_of_lt_of_le zero_lt_one hKr
  have hlpos : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one hlr
  apply le_min
  · exact inv_le_one_of_one_le₀ hKr
  · apply (le_div_iff₀ hlpos).mpr
    apply (inv_mul_le_iff₀ hKpos).mpr
    by_cases h1 : l = 1
    · simp only [h1,Nat.cast_one]
      nlinarith
    · have h2 : (2:ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
      nlinarith

end BridgeGapCount

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section BridgePiecePath
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem conn_restrict_cluster_of_subset (G : BondGraph V E) (ω : Set E) (x : V)
    {η : Set E} (hη : η ⊆ ω) {a b : V} (ha : a ∈ cluster G ω x)
    (hab : Conn G η a b) : Conn G (η ∩ internalEdges G (cluster G ω x)) a b := by
  induction hab with
  | refl => exact conn_refl G _ a
  | @tail u v hau huv ih =>
    obtain ⟨e,he,heq⟩ := huv
    have hu : u ∈ cluster G ω x := ha.trans (conn_mono G hη hau)
    have hv : v ∈ cluster G ω x := (edge_cluster_sides G ω x (hη he) heq).mp hu
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e u v heq).mpr ⟨hu,hv⟩⟩,heq⟩

 

theorem conn_between_pivotals_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) (hC : (cluster G ω x).Finite) {e f : E}
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {z} x f)
    (hlt : pivotalRank G ω x e < pivotalRank G ω x f)
    (a b c d : V) (hab : G e = s(a,b)) (hcd : G f = s(c,d))
    (ha : Conn G (ω \ {e}) x a) (hb : ¬Conn G (ω \ {e}) x b)
    (hc : Conn G (ω \ {f}) x c) :
    Conn G (ω ∩ internalEdges G
      (cluster G (ω \ {f}) x \ cluster G (ω \ {e}) x)) b c := by
  have hne : e ≠ f := fun h => (Nat.ne_of_lt hlt) (congrArg (pivotalRank G ω x) h)
  have hout := (pivotalRank_lt_iff_of_cluster_finite G ω {z} x hC he hf).mp hlt
  have hcnot : c ∉ cluster G (ω \ {e}) x :=
    ((mem_internalEdges_of_ends G _ f c d hcd).mp hout).1
  have hins : insert e ((ω \ {e}) \ {f}) = ω \ {f} := by
    ext q
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨⟨hq,hqe⟩,hqf⟩)
      · exact ⟨he.1,hne⟩
      · exact ⟨hq,hqf⟩
    · rintro ⟨hq,hqf⟩
      by_cases hqe : q = e
      · exact Or.inl hqe
      · exact Or.inr ⟨⟨hq,hqe⟩,hqf⟩
  have hbc : Conn G ((ω \ {e}) \ {f}) b c := by
    rw [← hins,conn_insert_iff G _ e a b x c hab] at hc
    rcases hc with h | ⟨_,h⟩ | ⟨h,_⟩
    · exact (hcnot (conn_mono G Set.sdiff_subset h)).elim
    · exact h
    · exact (hb (conn_mono G Set.sdiff_subset h)).elim
  have hbo : b ∈ cluster G (ω \ {f}) x :=
    conn_far_end_avoids_later_pivotal G ω x z hC he hf hlt a b hab ha
  have hp := conn_restrict_cluster_compl_of_subset G (ω \ {e}) x Set.sdiff_subset hb hbc
  have hp' := conn_restrict_cluster_of_subset G (ω \ {f}) x
    (η := ((ω \ {e}) \ {f}) ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ)
    (fun _ h => ⟨h.1.1.1,h.1.2⟩) hbo hp
  apply conn_mono G ?_ hp'
  intro q hq
  exact ⟨hq.1.1.1.1,fun v hv => ⟨hq.2 v hv,hq.1.2 v hv⟩⟩

 
theorem conn_after_pivotal_internal (G : BondGraph V E) (ω : Set E)
    (x z : V) {e : E} (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (ha : Conn G (ω \ {e}) x a)
    (hb : ¬Conn G (ω \ {e}) x b) (hbz : Conn G (ω \ {e}) b z) :
    Conn G (ω ∩ internalEdges G (cluster G ω x \ cluster G (ω \ {e}) x)) b z := by
  have hbo : b ∈ cluster G ω x :=
    (conn_mono G Set.sdiff_subset ha).tail ⟨e,he.1,hab⟩
  have hp := conn_restrict_cluster_compl G (ω \ {e}) x hb hbz
  have hp' := conn_restrict_cluster_of_subset G ω x
    (η := (ω \ {e}) ∩ internalEdges G (cluster G (ω \ {e}) x)ᶜ)
    (fun _ h => h.1.1) hbo hp
  apply conn_mono G ?_ hp'
  intro q hq
  exact ⟨hq.1.1.1,fun v hv => ⟨hq.2 v hv,hq.1.2 v hv⟩⟩

 
theorem pivotalDistance_le_induced_card (G : BondGraph V E) (ω : Set E)
    (B : Set V) (hB : B.Finite) {a b : V} (ha : a ∈ B) :
    pivotalDistance G (ω ∩ internalEdges G B) a b ≤ B.ncard-1 := by
  have hsub : cluster G (ω ∩ internalEdges G B) a ⊆ B :=
    fun _ h => conn_internal_endpoint G B ha h
  exact (pivotalDistance_le_cluster_card G (ω ∩ internalEdges G B) a b (hB.subset hsub)).trans
    (Nat.sub_le_sub_right (Set.ncard_le_ncard hsub hB) 1)

end BridgePiecePath

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SplicePieceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem conn_after_pivotal_of_orientation (G : BondGraph V E) (ω : Set E)
    (x z : V) {e : E} (he : OpenMarkedPivotal G ω {z} x e)
    (a b : V) (hab : G e = s(a,b)) (hb : ¬Conn G (ω \ {e}) x b) :
    Conn G (ω \ {e}) b z := by
  have hins : insert e (ω \ {e}) = ω := by
    ext q
    simp only [Set.mem_insert_iff,Set.mem_sdiff,Set.mem_singleton_iff]
    by_cases hqe : q = e <;> simp_all [he.1]
  obtain ⟨w,hw,hxw⟩ := he.2.1
  have hw' : w = z := Set.mem_singleton_iff.mp hw
  subst w
  rw [← hins,conn_insert_iff G _ e a b x z hab] at hxw
  rcases hxw with h | ⟨_,h⟩ | ⟨h,_⟩
  · exact (he.2.2 ⟨z,rfl,h⟩).elim
  · exact h
  · exact (hb h).elim

 
theorem SpliceTrace.internal_agreement (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ internalEdges G (cluster G ω x), q ∈ ωf ↔ q ∈ ω := by
  induction h with
  | stop => exact fun _ _ => Iff.rfl
  | @step j i ω e a b rest ωf _ _ _ _ hy he hab ha hb ht ih =>
    intro q hq
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hB : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hbS : b ∉ S := hB hb
    have hqq : q ∈ internalEdges G (cluster G ω' x) := by
      rw [splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb]
      exact fun v hv => Or.inl (hq v hv)
    rw [ih q hqq]
    change q ∈ internalEdges G S at hq
    have hh := (splice_internal_fields G S B e ω (η i) a b hab hbS hB).1
    exact Iff.of_eq (show (q ∈ ω') = (q ∈ ω) from by
      have := congrArg (fun A : Set E => q ∈ A) hh
      simpa only [Set.mem_inter_iff,hq,and_true] using this)

 
theorem SpliceTrace.head_cut (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf) :
    cluster G (ωf \ {e}) x = cluster G ω x := by
  cases h with
  | step j i ω e a b rest ωf _ _ _ hmax hy he hab ha hb ht =>
    have hc := splice_close_seam_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    rw [SpliceTrace.preserve_cut G x η y k i _ ωf rest ht e]
    · exact hc
    · intro l hil hlk
      rw [hc]
      exact hmax l hil hlk

 
theorem contactSet_finite (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (B : Set V) (hB : B.Finite) : (contactSet G ω B).Finite := by
  let W := hB.toFinset
  have hWB : (W : Set V) = B := hB.coe_toFinset
  apply (incidentSupport G hloc W).finite_toSet.subset
  rintro e ⟨_,a,b,hab,ha,_⟩
  apply (mem_incidentSupport G hloc W e).mpr
  refine ⟨a,?_,?_⟩
  · change a ∈ (W : Set V)
    rw [hWB]
    exact ha
  · simp [hab]

 

theorem goodForScale_piece (G : BondGraph V E) (ω : Set E) (x : V) (L : ℝ)
    (hg : GoodForScale G ω x L) (B : Set V) (hB : B.Finite)
    (hBC : B ⊆ cluster G ω x)
    (hconn : ∀ a ∈ B, ∀ b ∈ B, Conn G (ω ∩ internalEdges G B) a b)
    (hK : 0 < (contactSet G ω B).ncard) {a b : V} (ha : a ∈ B) (hb : b ∈ B) :
    (pivotalDistance G (ω ∩ internalEdges G B) a b : ℝ) ≤
      (contactSet G ω B).ncard*L := by
  let W := hB.toFinset
  have hWB : (W : Set V) = B := hB.coe_toFinset
  have hh := hg W (by simpa only [hWB] using hBC)
    (by simpa only [← Finset.mem_coe,hWB] using hconn)
    (by simpa only [hWB] using hK) a (by simpa only [← Finset.mem_coe,hWB] using ha)
    b (by simpa only [← Finset.mem_coe,hWB] using hb)
  simpa only [hWB] using hh

 
theorem slit_piece_connected (G : BondGraph V E) (η : Set E) (S : Set V) (y : V)
    (_hy : y ∉ S) :
    let B := cluster G (η ∩ internalEdges G Sᶜ) y
    ∀ a ∈ B, ∀ b ∈ B, Conn G (η ∩ internalEdges G B) a b := by
  intro B a ha b hb
  have hc := conn_restrict_cluster G (η ∩ internalEdges G Sᶜ) y ha
    (conn_trans G _ (conn_symm G _ ha) hb)
  apply conn_mono G ?_ hc
  exact fun _ h => ⟨h.1.1,h.2⟩

end SplicePieceGeometry

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceGapBound
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def traceHeadGap (G : BondGraph V E) (ωf : Set E) (x z : V)
    (e : E) (rest : List (ℕ × E)) : ℕ :=
  (match rest with
    | [] => (separatingBonds G ωf x z).card + 1
    | (_,f)::_ => bridgeIndex G ωf x z f) - bridgeIndex G ωf x z e

 

theorem SpliceTrace.head_gap_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j i M : ℕ)
    (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hCf : (cluster G ωf x).Finite)
    (hCi : (cluster G (η i) (y i)).Finite)
    (hM : (cluster G (η i) (y i)).ncard ≤ M)
    (L : ℝ) (hgood : GoodForScale G (η i) (y i) L) :
    let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
    let K := (contactSet G (η i) B).ncard
    let l := traceHeadGap G ωf x (y k) e rest
    1 ≤ K ∧ 1 ≤ l ∧ l ≤ M ∧ (l:ℝ) ≤ 1 + K*L := by
  have hfull := h
  cases h with
  | step j i ω e a b rest ωf hn _ _ _ hy he hab ha hb ht =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    let K := (contactSet G (η i) B).ncard
    change 1 ≤ K ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧
      (traceHeadGap G ωf x (y k) e rest:ℝ) ≤ 1+K*L
    have hBo : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hBC : B ⊆ cluster G (η i) (y i) := fun _ h => conn_mono G Set.inter_subset_left h
    have hB : B.Finite := hCi.subset hBC
    have hKB : (contactSet G (η i) B).Finite := contactSet_finite G hloc (η i) B hB
    have heK : e ∈ contactSet G (η i) B :=
      ⟨he,b,a,hab.trans (Sym2.eq_swap ..),hb,fun h => hBo h ha⟩
    have hK : 0 < K := (Set.ncard_pos hKB).mpr ⟨e,heK⟩
    have hBpos : 0 < B.ncard := (Set.ncard_pos hB).mpr ⟨b,hb⟩
    have hBM : B.ncard ≤ M := (Set.ncard_le_ncard hBC hCi).trans hM
    have hcluster : cluster G ω' x = S ∪ B :=
      splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hcut : cluster G (ωf \ {e}) x = S :=
      SpliceTrace.head_cut G x η y k j i ω ωf e rest hfull
    have hpe : OpenMarkedPivotal G ωf {y k} x e :=
      SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::rest) hfull (i,e) (by simp)
    have hxa : Conn G (ωf \ {e}) x a := by
      change a ∈ cluster G (ωf \ {e}) x
      rw [hcut]
      exact ha
    have hxb : ¬Conn G (ωf \ {e}) x b := by
      change b ∉ cluster G (ωf \ {e}) x
      rw [hcut]
      exact hBo hb
    have hbits : ωf ∩ internalEdges G B = η i ∩ internalEdges G B := by
      have hii := (splice_internal_fields G S B e ω (η i) a b hab (hBo hb) hBo).2
      ext q
      by_cases hq : q ∈ internalEdges G B
      · have hq' : q ∈ internalEdges G (cluster G ω' x) := by
          rw [hcluster]
          exact fun v hv => Or.inr (hq v hv)
        have hiff := SpliceTrace.internal_agreement G x η y k i ω' ωf rest ht q hq'
        have hbit := congrArg (fun A : Set E => q ∈ A) hii
        simpa only [Set.mem_inter_iff,hq,and_true,hiff] using Iff.of_eq hbit
      · simp only [Set.mem_inter_iff,hq,and_false]
    have hconn := slit_piece_connected G (η i) S (y i) hy
    have finish (l : ℕ) (c : V) (hc : c ∈ B) (hl : 1 ≤ l)
        (hg : l ≤ 1 + pivotalDistance G (ωf ∩ internalEdges G B) b c) :
        1 ≤ l ∧ l ≤ M ∧ (l:ℝ) ≤ 1+K*L := by
      rw [hbits] at hg
      have hp := pivotalDistance_le_induced_card G (η i) B hB hb (b := c)
      have hg' : (l:ℝ) ≤ 1+(pivotalDistance G (η i ∩ internalEdges G B) b c:ℝ) := by
        exact_mod_cast hg
      have hgood' := goodForScale_piece G (η i) (y i) L hgood B hB hBC hconn hK hb hc
      refine ⟨hl,by omega,?_⟩
      change (l:ℝ) ≤ 1+(contactSet G (η i) B).ncard*L
      linarith
    refine ⟨hK,?_⟩
    cases rest with
    | nil =>
      have hfω : ωf = ω' := by cases ht; rfl
      have hdiff : cluster G ωf x \ cluster G (ωf \ {e}) x = B := by
        rw [hcut,hfω,hcluster]
        ext v
        constructor
        · rintro ⟨hv,hnv⟩
          exact hv.resolve_left hnv
        · intro hv
          exact ⟨Or.inr hv,hBo hv⟩
      have hyk : y k ∈ B := by
        have hz := SpliceTrace.endpoint G x η y k j ω ωf [(i,e)] hfull
        rw [hfω,hcluster] at hz
        exact hz.resolve_left hn
      have hconnz := conn_after_pivotal_of_orientation G ωf x (y k) hpe a b hab hxb
      have hp := conn_after_pivotal_internal G ωf x (y k) hpe a b hab hxa hxb hconnz
      have hg := bridge_terminal_gap_le_internal_distance G ωf x (y k) hCf hpe a b hab hxa hp
      rw [hdiff] at hg
      apply finish _ (y k) hyk _ hg
      have hcard : bridgeIndex G ωf x (y k) e ≤ (separatingBonds G ωf x (y k)).card :=
        Finset.card_filter_le _ _
      omega
    | cons q more =>
      obtain ⟨l,f⟩ := q
      have hcutf : cluster G (ωf \ {f}) x = S ∪ B := by
        rw [SpliceTrace.head_cut G x η y k i l ω' ωf f more ht,hcluster]
      have hss : cluster G (ωf \ {e}) x ⊂ cluster G (ωf \ {f}) x := by
        rw [hcut,hcutf]
        exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_union_left,fun heq =>
          hBo hb (heq.symm ▸ (show b ∈ S ∪ B from Or.inr hb))⟩
      have hfFin : (cluster G (ωf \ {f}) x).Finite :=
        hCf.subset (fun _ h => conn_mono G Set.sdiff_subset h)
      have hr : pivotalRank G ωf x e < pivotalRank G ωf x f := Set.ncard_lt_ncard hss hfFin
      have hpf : OpenMarkedPivotal G ωf {y k} x f :=
        SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::(l,f)::more) hfull (l,f) (by simp)
      obtain ⟨c,d,hcd,hxc,hxd,hdyk⟩ := openMarkedPivotal_oriented G ωf {y k} x hpf
      have hdy : Conn G (ωf \ {f}) d (y k) := by
        simpa only [MarkedEvent,Set.mem_singleton_iff,exists_eq_left] using hdyk
      have hdiff : cluster G (ωf \ {f}) x \ cluster G (ωf \ {e}) x = B := by
        rw [hcut,hcutf]
        ext v
        constructor
        · rintro ⟨hv,hnv⟩
          exact hv.resolve_left hnv
        · intro hv
          exact ⟨Or.inr hv,hBo hv⟩
      have hc : c ∈ B := by
        have hfout := (pivotalRank_lt_iff_of_cluster_finite G ωf {y k} x hCf hpe hpf).mp hr
        have hcnot := ((mem_internalEdges_of_ends G _ f c d hcd).mp hfout).1
        rw [hcut] at hcnot
        change c ∈ cluster G (ωf \ {f}) x at hxc
        rw [hcutf] at hxc
        exact hxc.resolve_left hcnot
      have hp := conn_between_pivotals_internal G ωf x (y k) hCf hpe hpf hr
        a b c d hab hcd hxa hxb (by change c ∈ cluster G (ωf \ {f}) x; rw [hcutf]; exact Or.inr hc)
      have hg := bridge_gap_le_internal_distance G ωf x (y k) hCf hpe hpf hr
        a b c d hab hcd hxa hxd hdy hp
      rw [hdiff] at hg
      apply finish _ c hc _ hg
      have hind := bridgeIndex_interval_identity G ωf x (y k) hCf hpf hr
      omega

end SpliceGapBound

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section GapCode
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.seam_data (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ q ∈ steps, j < q.1 ∧ q.1 ≤ k ∧ q.2 ∈ η q.1 ∧
      q.2 ∈ internalEdges G (cluster G (η q.1) (y q.1)) := by
  induction h with
  | stop => simp
  | @step j i ω e a b rest ωf _ hji hik _ _ he hab _ hb ht ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hb' : b ∈ cluster G (η i) (y i) := conn_mono G Set.inter_subset_left hb
      exact ⟨hji,hik,he,(mem_internalEdges_of_ends G _ e a b hab).mpr
        ⟨(edge_cluster_sides G (η i) (y i) he hab).mpr hb',hb'⟩⟩
    · obtain ⟨hqi,hqk,hqe,hqC⟩ := ih q hq
      exact ⟨hji.trans hqi,hqk,hqe,hqC⟩

 
theorem SpliceTrace.head_index_lt (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j i : ℕ) (ω ωf : Set E) (e : E) (rest : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω ((i,e)::rest) ωf)
    (hC : (cluster G ωf x).Finite) :
    ∀ q ∈ rest, bridgeIndex G ωf x (y k) e < bridgeIndex G ωf x (y k) q.2 := by
  have hfull := h
  have hc := SpliceTrace.head_cut G x η y k j i ω ωf e rest h
  have hseams := SpliceTrace.seams_pivotal G x η y k j ω ωf ((i,e)::rest) h
  cases h with
  | step j i ω e a b rest ωf _ _ _ hmax _ _ _ _ _ ht =>
    intro q hq
    obtain ⟨hqi,hqk,_,hqC⟩ := SpliceTrace.seam_data G x η y k i _ ωf rest ht q hq
    have hout : q.2 ∈ internalEdges G (cluster G (ωf \ {e}) x)ᶜ := by
      rw [hc]
      intro v hv hvS
      exact Set.disjoint_left.mp (hmax q.1 hqi hqk) (hqC v hv) hvS
    have hpe := hseams (i,e) (by simp)
    have hpq := hseams q (List.mem_cons_of_mem _ hq)
    exact bridgeIndex_lt_of_rank_lt G ωf x (y k) hpq
      ((pivotalRank_lt_iff_of_cluster_finite G ωf {y k} x hC hpe hpq).mpr hout)

 
noncomputable def gapSpliceCode (G : BondGraph V E) (ωf : Set E) (x z : V) :
    List (ℕ × E) → List (ℕ × ℕ)
  | [] => []
  | (i,e)::rest => (i,traceHeadGap G ωf x z e rest)::gapSpliceCode G ωf x z rest

 
def decodeGapOrdinals (N : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (i,l)::rest =>
    let decoded := decodeGapOrdinals N rest
    (i, (match decoded with | [] => N+1 | (_,r)::_ => r)-l)::decoded

 
theorem SpliceTrace.decode_gap_code (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (hC : (cluster G ωf x).Finite) :
    decodeGapOrdinals (separatingBonds G ωf x (y k)).card
      (gapSpliceCode G ωf x (y k) steps) = ordinalSpliceCode G ωf x (y k) steps := by
  induction steps generalizing j ω with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hlater := SpliceTrace.head_index_lt G x η y k j i ω ωf e rest h hC
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      have ih' := ih i _ ht
      simp only [gapSpliceCode,decodeGapOrdinals,ih',ordinalSpliceCode,List.map_cons]
      congr 2
      cases rest with
      | nil =>
        simp only [List.map_nil,traceHeadGap]
        have hle : bridgeIndex G ωf x (y k) e ≤ (separatingBonds G ωf x (y k)).card :=
          Finset.card_filter_le _ _
        omega
      | cons q qs =>
        obtain ⟨l,f⟩ := q
        have hle := hlater (l,f) (by simp)
        change bridgeIndex G ωf x (y k) e < bridgeIndex G ωf x (y k) f at hle
        simp only [List.map_cons,traceHeadGap]
        omega

 
theorem SpliceTrace.input_unique_of_gapCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : gapSpliceCode G ωf x (y₁ k) c₁ = gapSpliceCode G ωf x (y₁ k) c₂)
    (θf : ℕ → Set E)
    (he₁ : SpliceExecution G x (ω₁,η₁) c₁ (ωf,θf))
    (he₂ : SpliceExecution G x (ω₂,η₂) c₂ (ωf,θf)) :
    (ω₁,η₁) = (ω₂,η₂) := by
  apply SpliceTrace.input_unique_of_ordinalCode G x η₁ η₂ y₁ y₂ k j ω₁ ω₂ ωf
    c₁ c₂ ht₁ ht₂ hz hC _ θf he₁ he₂
  rw [← SpliceTrace.decode_gap_code G x η₁ y₁ k j ω₁ ωf c₁ ht₁ hC,
    heq,hz,SpliceTrace.decode_gap_code G x η₂ y₂ k j ω₂ ωf c₂ ht₂ hC]

end GapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section InverseCodeMass
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def gapWeight (L : ℝ) (l : ℕ) : ℝ := min 1 (2*L/l)

 
noncomputable def inverseCodeMass (M : ℕ) (L : ℝ) : ℝ :=
  1 + ∑ l ∈ Finset.Icc 1 M, gapWeight L l

 
noncomputable def gapLetterWeight (L : ℝ) (l : ℕ) : ℝ := if l = 0 then 1 else gapWeight L l

theorem gapWeight_nonneg (L : ℝ) (hL : 0 ≤ L) (l : ℕ) : 0 ≤ gapWeight L l := by
  exact le_min zero_le_one (by positivity)

theorem gapLetterWeight_nonneg (L : ℝ) (hL : 0 ≤ L) (l : ℕ) : 0 ≤ gapLetterWeight L l := by
  unfold gapLetterWeight
  split_ifs
  · exact zero_le_one
  · exact gapWeight_nonneg L hL l

theorem sum_fin_succ_eq_Icc (M : ℕ) (f : ℕ → ℝ) :
    ∑ l : Fin M, f (l.val+1) = ∑ l ∈ Finset.Icc 1 M, f l := by
  rw [Fin.sum_univ_eq_sum_range (fun l => f (l+1)) M]
  apply Finset.sum_bij (fun l _ => l+1)
  · intro l hl
    exact Finset.mem_Icc.mpr ⟨by omega,by have := Finset.mem_range.mp hl; omega⟩
  · intro l hl m hm h
    omega
  · intro l hl
    obtain ⟨h1,hM⟩ := Finset.mem_Icc.mp hl
    exact ⟨l-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intros
    rfl

theorem sum_gapLetterWeight (M : ℕ) (L : ℝ) :
    ∑ l : Fin (M+1), gapLetterWeight L l.val = inverseCodeMass M L := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,gapLetterWeight,Fin.val_succ,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,ite_false]
  exact congrArg (1+·) (sum_fin_succ_eq_Icc M (gapWeight L))

 

theorem total_gap_code_mass (k M : ℕ) (L : ℝ) :
    ∑ c : Fin k → Fin (M+1), ∏ i : Fin k, gapLetterWeight L (c i).val =
      inverseCodeMass M L ^ k := by
  rw [← Fintype.prod_sum (fun (_ : Fin k) (l : Fin (M+1)) => gapLetterWeight L l.val)]
  simp only [sum_gapLetterWeight,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

 
theorem valid_gap_code_mass_le (k M : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (valid : Finset (Fin k → Fin (M+1))) :
    ∑ c ∈ valid, ∏ i : Fin k, gapLetterWeight L (c i).val ≤ inverseCodeMass M L ^ k := by
  rw [← total_gap_code_mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun c _ _ => Finset.prod_nonneg (fun i _ => gapLetterWeight_nonneg L hL (c i).val))

theorem inverseCodeMass_le_harmonic (M : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    inverseCodeMass M L ≤ 1+2*L*(1+Real.log M) := by
  have hsum : ∑ l ∈ Finset.Icc 1 M, gapWeight L l ≤
      2*L*∑ l ∈ Finset.Icc 1 M, (l:ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    simpa only [gapWeight,div_eq_mul_inv] using min_le_right (1:ℝ) (2*L/l)
  have hh : ∑ l ∈ Finset.Icc 1 M, (l:ℝ)⁻¹ ≤ 1+Real.log M := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using
      harmonic_le_one_add_log M
  unfold inverseCodeMass
  have h := hsum.trans (mul_le_mul_of_nonneg_left hh (by positivity))
  linarith

 
theorem inverseCodeMass_le_log (M : ℕ) (L : ℝ) (hM : 2 ≤ M) (hL : 1 ≤ L) :
    inverseCodeMass M L ≤ 8*L*Real.log M := by
  have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 2 by norm_num)
    norm_num at hh ⊢
    exact hh
  have hlog : (1:ℝ)/2 ≤ Real.log M := hlog2.trans
    (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
  have hLl : L/2 ≤ L*Real.log M := by nlinarith
  have hbound := inverseCodeMass_le_harmonic M L (by linarith)
  nlinarith

 
def contactInterval (K a : ℕ) : Set unitInterval :=
  {u | (a:ℝ)/K ≤ (u:ℝ) ∧ (u:ℝ) < (a+1:ℕ)/K}

theorem volume_contactInterval (K a : ℕ) (ha : a < K) :
    volume (contactInterval K a) = ENNReal.ofReal ((K:ℝ)⁻¹) := by
  have hK : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hleft : (a:ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hK).mpr ?_⟩
    exact_mod_cast (Nat.le_of_lt ha)
  have hright : ((a+1:ℕ):ℝ)/K ∈ Set.Icc (0:ℝ) 1 := by
    refine ⟨by positivity,(div_le_one hK).mpr ?_⟩
    exact_mod_cast (show a+1 ≤ K by omega)
  let lo : unitInterval := ⟨_,hleft⟩
  let hi : unitInterval := ⟨_,hright⟩
  have heq : contactInterval K a = Set.Ico lo hi := rfl
  rw [heq,unitInterval.volume_Ico]
  congr 1
  dsimp only [lo,hi]
  push_cast
  field_simp
  ring

 

theorem volume_contact_cube {I : Type*} [Fintype I] (K a : I → ℕ)
    (ha : ∀ i, a i < K i) :
    (volume : Measure (I → unitInterval)) (Set.pi Set.univ (fun i => contactInterval (K i) (a i))) =
      ∏ i, ENNReal.ofReal ((K i:ℝ)⁻¹) := by
  rw [MeasureTheory.volume_pi,Measure.pi_pi]
  exact Finset.prod_congr rfl (fun i _ => volume_contactInterval (K i) (a i) (ha i))

theorem real_volume_contact_cube {I : Type*} [Fintype I] (K a : I → ℕ)
    (ha : ∀ i, a i < K i) :
    ((volume : Measure (I → unitInterval))
      (Set.pi Set.univ (fun i => contactInterval (K i) (a i)))).toReal =
      ∏ i, (K i:ℝ)⁻¹ := by
  rw [volume_contact_cube K a ha,ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => ENNReal.toReal_ofReal (by positivity))

end InverseCodeMass

end Percolation

end OAI
