import Mathlib
import OAI.Probability.UnimodularPercolation.Splicing.GapCodes

namespace OAI

/-! Replay for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SparseGapCode
attribute [local instance] Classical.propDecidable Classical.decEq

 

def ValidSparseGapCode (k M : ℕ) (c : List (ℕ × ℕ)) : Prop :=
  c.Pairwise (fun q r => q.1 < r.1) ∧
    ∀ q ∈ c, 1 ≤ q.1 ∧ q.1 ≤ k ∧ 1 ≤ q.2 ∧ q.2 ≤ M

def sparseGapValue : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (j,l)::c, i => if i = j then l else sparseGapValue c i

theorem sparseGapValue_zero (c : List (ℕ × ℕ)) (i : ℕ)
    (h : ∀ q ∈ c, i ≠ q.1) : sparseGapValue c i = 0 := by
  induction c with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨j,l⟩ := q
    rw [sparseGapValue,ite_eq_right (h (j,l) (by simp))]
    exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem sparseGapValue_bound (k M : ℕ) (c : List (ℕ × ℕ))
    (h : ValidSparseGapCode k M c) (i : ℕ) : sparseGapValue c i ≤ M := by
  induction c with
  | nil => exact Nat.zero_le _
  | cons q c ih =>
    obtain ⟨j,l⟩ := q
    rw [sparseGapValue]
    split_ifs
    · exact (h.2 (j,l) (by simp)).2.2.2
    · exact ih ⟨(List.pairwise_cons.mp h.1).2,fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

 
theorem sparseGapValue_injective (c d : List (ℕ × ℕ))
    (hc : c.Pairwise (fun q r => q.1 < r.1))
    (hd : d.Pairwise (fun q r => q.1 < r.1))
    (hpc : ∀ q ∈ c, 0 < q.2) (hpd : ∀ q ∈ d, 0 < q.2)
    (heq : ∀ i, sparseGapValue c i = sparseGapValue d i) : c = d := by
  induction c generalizing d with
  | nil =>
    cases d with
    | nil => rfl
    | cons q d =>
      obtain ⟨j,l⟩ := q
      have hh := heq j
      simp [sparseGapValue] at hh
      have := hpd (j,l) (by simp)
      omega
  | cons q c ih =>
    obtain ⟨i,l⟩ := q
    cases d with
    | nil =>
      have hh := heq i
      simp [sparseGapValue] at hh
      have := hpc (i,l) (by simp)
      omega
    | cons q d =>
      obtain ⟨j,m⟩ := q
      obtain ⟨hc0,hc1⟩ := List.pairwise_cons.mp hc
      obtain ⟨hd0,hd1⟩ := List.pairwise_cons.mp hd
      have hij : i = j := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hij | hji
        · have hz : sparseGapValue ((j,m)::d) i = 0 := by
            apply sparseGapValue_zero
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact hne
            · have := hd0 q hq
              change j < q.1 at this
              omega
          have hh := heq i
          rw [hz] at hh
          simp [sparseGapValue] at hh
          have := hpc (i,l) (by simp)
          omega
        · have hz : sparseGapValue ((i,l)::c) j = 0 := by
            apply sparseGapValue_zero
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact Ne.symm hne
            · have := hc0 q hq
              change i < q.1 at this
              omega
          have hh := heq j
          rw [hz] at hh
          simp [sparseGapValue] at hh
          have := hpd (j,m) (by simp)
          omega
      subst j
      have hlm : l = m := by simpa [sparseGapValue] using heq i
      subst m
      congr 1
      apply ih d hc1 hd1
        (fun q hq => hpc q (List.mem_cons_of_mem _ hq))
        (fun q hq => hpd q (List.mem_cons_of_mem _ hq))
      intro r
      by_cases hr : r = i
      · subst r
        rw [sparseGapValue_zero c i (fun q hq => (hc0 q hq).ne),
          sparseGapValue_zero d i (fun q hq => (hd0 q hq).ne)]
      · simpa only [sparseGapValue,ite_eq_right hr] using heq r

 
def sparseGapArray (k M : ℕ) (c : List (ℕ × ℕ)) (h : ValidSparseGapCode k M c) :
    Fin k → Fin (M+1) :=
  fun i => ⟨sparseGapValue c (i.val+1),Nat.lt_succ_of_le (sparseGapValue_bound k M c h _)⟩

theorem sparseGapArray_injective (k M : ℕ) (c d : List (ℕ × ℕ))
    (hc : ValidSparseGapCode k M c) (hd : ValidSparseGapCode k M d)
    (heq : sparseGapArray k M c hc = sparseGapArray k M d hd) : c = d := by
  apply sparseGapValue_injective c d hc.1 hd.1
    (fun q hq => (hc.2 q hq).2.2.1) (fun q hq => (hd.2 q hq).2.2.1)
  intro i
  by_cases hi : 1 ≤ i ∧ i ≤ k
  · have he := congrArg (fun f => (f ⟨i-1,by omega⟩).val) heq
    simpa only [sparseGapArray,show i-1+1 = i by omega] using he
  · rw [sparseGapValue_zero c i, sparseGapValue_zero d i]
    · intro q hq he
      have h := hd.2 q hq
      omega
    · intro q hq he
      have h := hc.2 q hq
      omega

 

theorem SpliceTrace.valid_gap_code (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L) :
    ValidSparseGapCode k M (gapSpliceCode G ωf x (y k) steps) ∧
      ∀ q ∈ gapSpliceCode G ωf x (y k) steps, j < q.1 := by
  induction steps generalizing j ω with
  | nil => simp [ValidSparseGapCode,gapSpliceCode]
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hs := h.seam_data G x η y k j ω ωf ((i,e)::rest) (i,e) (by simp)
    have hi : 1 ≤ i := by omega
    obtain ⟨hCi,hMi,hGi⟩ := hgood i hi hs.2.1
    have hg := h.head_gap_bounds G hloc x η y k j i M ω ωf e rest hCf hCi hMi L hGi
    change 1 ≤ _ ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧ _ at hg
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      obtain ⟨⟨hpair,hbounds⟩,hlater⟩ := ih i _ ht
      simp only [gapSpliceCode]
      refine ⟨⟨List.pairwise_cons.mpr ⟨?_,hpair⟩,?_⟩,?_⟩
      · exact hlater
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact ⟨hi,hs.2.1,hg.2.1,hg.2.2.1⟩
        · exact hbounds q hq
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hs.1
        · exact hs.1.trans (hlater q hq)

end SparseGapCode

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceContactMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def seamContactCount (G : BondGraph V E) (η : ℕ → Set E)
    (y : ℕ → V) (ωf : Set E) (x : V) (i : ℕ) (e : E) : ℕ :=
  (contactSet G (η i)
    (cluster G (η i ∩ internalEdges G (cluster G (ωf \ {e}) x)ᶜ) (y i))).ncard

 
noncomputable def traceContactCount (G : BondGraph V E) (η : ℕ → Set E)
    (y : ℕ → V) (ωf : Set E) (x : V) : List (ℕ × E) → ℕ → ℕ
  | [], _ => 1
  | (j,e)::c, i => if i = j then seamContactCount G η y ωf x j e
      else traceContactCount G η y ωf x c i

 
theorem SpliceTrace.contact_weight_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ) (hL : 1 ≤ L)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L) :
    ∀ i, 1 ≤ traceContactCount G η y ωf x steps i ∧
      (traceContactCount G η y ωf x steps i : ℝ)⁻¹ ≤
        gapLetterWeight L (sparseGapValue (gapSpliceCode G ωf x (y k) steps) i) := by
  induction steps generalizing j ω with
  | nil => simp [traceContactCount,gapSpliceCode,sparseGapValue,gapLetterWeight]
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    have hs := h.seam_data G x η y k j ω ωf ((i,e)::rest) (i,e) (by simp)
    have hi : 1 ≤ i := by omega
    obtain ⟨hCi,hMi,hGi⟩ := hgood i hi hs.2.1
    have hg := h.head_gap_bounds G hloc x η y k j i M ω ωf e rest hCf hCi hMi L hGi
    have hcut := h.head_cut G x η y k j i ω ωf e rest
    change 1 ≤ _ ∧ 1 ≤ traceHeadGap G ωf x (y k) e rest ∧
      traceHeadGap G ωf x (y k) e rest ≤ M ∧ _ at hg
    have hk : seamContactCount G η y ωf x i e =
      (contactSet G (η i) (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))).ncard := by
      unfold seamContactCount
      rw [hcut]
    rw [← hk] at hg
    cases h with
    | step j i ω e a b rest ωf _ _ _ _ _ _ _ _ _ ht =>
      intro r
      by_cases hr : r = i
      · subst r
        simp only [traceContactCount,gapSpliceCode,sparseGapValue,ite_true]
        refine ⟨hg.1,?_⟩
        rw [gapLetterWeight,ite_eq_right (by omega)]
        exact inverse_contact_weight_le _ _ L hg.1 hg.2.1 hL hg.2.2.2
      · simpa only [traceContactCount,gapSpliceCode,sparseGapValue,ite_eq_right hr] using ih i _ ht r

 

def contactChoiceSet (K a : ℕ) : Set unitInterval :=
  if K = 1 then Set.univ else contactInterval K a

theorem volume_contactChoiceSet (K a : ℕ) (ha : a < K) :
    volume (contactChoiceSet K a) = ENNReal.ofReal ((K:ℝ)⁻¹) := by
  unfold contactChoiceSet
  split_ifs with h
  · simp [h]
  · exact volume_contactInterval K a ha

theorem real_volume_contact_choice_cube {I : Type*} [Fintype I] (K a : I → ℕ)
    (ha : ∀ i, a i < K i) :
    ((volume : Measure (I → unitInterval))
      (Set.pi Set.univ (fun i => contactChoiceSet (K i) (a i)))).toReal =
      ∏ i, (K i:ℝ)⁻¹ := by
  rw [MeasureTheory.volume_pi,Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [volume_contactChoiceSet _ _ (ha i),ENNReal.toReal_ofReal (by positivity)]

 

theorem SpliceTrace.contact_cube_le_code_weight (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E)
    (steps : List (ℕ × E)) (h : SpliceTrace G x η y k j ω steps ωf)
    (hCf : (cluster G ωf x).Finite) (L : ℝ) (hL : 1 ≤ L)
    (hgood : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M ∧ GoodForScale G (η i) (y i) L)
    (a : Fin k → ℕ) (ha : ∀ i, a i < traceContactCount G η y ωf x steps (i.val+1)) :
    ((volume : Measure (Fin k → unitInterval))
      (Set.pi Set.univ (fun i => contactChoiceSet
        (traceContactCount G η y ωf x steps (i.val+1)) (a i)))).toReal ≤
    ∏ i : Fin k, gapLetterWeight L (sparseGapValue (gapSpliceCode G ωf x (y k) steps) (i.val+1)) := by
  rw [real_volume_contact_choice_cube _ _ ha]
  apply Finset.prod_le_prod₀
  · intros
    positivity
  · intro i _
    exact (h.contact_weight_bound G hloc x η y k j M ω ωf steps hCf L hL hgood (i.val+1)).2

 
theorem SpliceTrace.code_unique_of_gapCode (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j : ℕ) (ω₁ ω₂ ωf : Set E)
    (c₁ c₂ : List (ℕ × E))
    (ht₁ : SpliceTrace G x η₁ y₁ k j ω₁ c₁ ωf)
    (ht₂ : SpliceTrace G x η₂ y₂ k j ω₂ c₂ ωf)
    (hz : y₁ k = y₂ k) (hC : (cluster G ωf x).Finite)
    (heq : gapSpliceCode G ωf x (y₁ k) c₁ = gapSpliceCode G ωf x (y₁ k) c₂) : c₁ = c₂ := by
  apply ordinalSpliceCode_injective G ωf x (y₁ k) hC c₁ c₂
    (ht₁.seams_pivotal G x η₁ y₁ k j ω₁ ωf c₁)
    (by simpa only [hz] using ht₂.seams_pivotal G x η₂ y₂ k j ω₂ ωf c₂)
  rw [← ht₁.decode_gap_code G x η₁ y₁ k j ω₁ ωf c₁ hC,heq,hz,
    ht₂.decode_gap_code G x η₂ y₂ k j ω₂ ωf c₂ hC]

end TraceContactMass

end Percolation

 
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteInverseMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_inverse_contact_mass_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L) (p : unitInterval) (Q : Finset E)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (hir : Function.Injective (fun a => (inp a,steps a)))
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = z) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (rank : I → Fin k → ℕ)
    (hrank : ∀ a i, rank a i < traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1))
    (B : Finset (SpliceState E)) (hB : ∀ a, out a ∈ B) :
    (∑ a, spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) *
      ((volume : Measure (Fin k → unitInterval))
        (Set.pi Set.univ (fun i => contactChoiceSet
          (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1))
          (rank a i)))).toReal) ≤
      (∑ t ∈ B, spliceTupleWeight Q (Finset.Icc 1 k) p t) * inverseCodeMass M L ^ k := by
  let c : I → List (ℕ × ℕ) := fun a => gapSpliceCode G (out a).1 x z (steps a)
  have hvalid : ∀ a, ValidSparseGapCode k M (c a) := by
    intro a
    have hv := (htrace a).valid_gap_code G hloc x (inp a).2 (y a) k 0 M
      (inp a).1 (out a).1 (steps a) (hfin a) L (hgood a)
    simpa only [c,hz a] using hv.1
  let arr (a : I) : Fin k → Fin (M+1) := sparseGapArray k M (c a) (hvalid a)
  let f (a : I) : SpliceState E × (Fin k → Fin (M+1)) := (out a,arr a)
  have hinj : Function.Injective f := by
    intro a b he
    have ho : out a = out b := congrArg Prod.fst he
    have hc : c a = c b := sparseGapArray_injective k M (c a) (c b)
      (hvalid a) (hvalid b) (congrArg Prod.snd he)
    have hze : y a k = y b k := (hz a).trans (hz b).symm
    have htB : SpliceTrace G x (inp b).2 (y b) k 0 (inp b).1 (steps b) (out a).1 := by
      rw [ho]
      exact htrace b
    have heB : SpliceExecution G x (inp b) (steps b) (out a) := ho.symm ▸ hex b
    have hg : gapSpliceCode G (out a).1 x (y a k) (steps a) =
        gapSpliceCode G (out a).1 x (y a k) (steps b) := by
      simpa only [c,hz a,ho] using hc
    have hs := (htrace a).code_unique_of_gapCode G x (inp a).2 (inp b).2 (y a) (y b)
      k 0 (inp a).1 (inp b).1 (out a).1 (steps a) (steps b) htB hze (hfin a) hg
    have hi := (htrace a).input_unique_of_gapCode G x (inp a).2 (inp b).2 (y a) (y b)
      k 0 (inp a).1 (inp b).1 (out a).1 (steps a) (steps b) htB hze (hfin a) hg
      (out a).2 (hex a) heB
    exact hir (Prod.ext hi hs)
  let w (t : SpliceState E × (Fin k → Fin (M+1))) : ℝ :=
    spliceTupleWeight Q (Finset.Icc 1 k) p t.1 * ∏ i, gapLetterWeight L (t.2 i).val
  have hweight : ∀ a, spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) =
      spliceTupleWeight Q (Finset.Icc 1 k) p (out a) := by
    intro a
    apply ((hex a).weight G x (inp a) (out a) (steps a) Q (Finset.Icc 1 k) ?_ p).symm
    intro q hq
    have hq' := (htrace a).seam_data G x (inp a).2 (y a) k 0 (inp a).1 (out a).1 (steps a) q hq
    exact Finset.mem_Icc.mpr ⟨hq'.1,hq'.2.1⟩
  calc
    _ ≤ ∑ a, w (f a) := by
      apply Finset.sum_le_sum
      intro a _
      dsimp only [w,f,arr,sparseGapArray]
      rw [← hweight a]
      apply mul_le_mul_of_nonneg_left _ (spliceTupleWeight_nonneg _ _ p _)
      have hh := (htrace a).contact_cube_le_code_weight G hloc x (inp a).2 (y a)
        k 0 M (inp a).1 (out a).1 (steps a) (hfin a) L hL (hgood a) (rank a) (hrank a)
      simpa only [c,hz a] using hh
    _ = ∑ t ∈ Finset.univ.image f, w t := (Finset.sum_image hinj.injOn).symm
    _ ≤ ∑ t ∈ B ×ˢ (Finset.univ : Finset (Fin k → Fin (M+1))), w t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_product.mpr ⟨hB a,Finset.mem_univ _⟩
      · intro t _ _
        exact mul_nonneg (spliceTupleWeight_nonneg _ _ p _)
          (Finset.prod_nonneg (fun i _ => gapLetterWeight_nonneg L (by linarith) _))
    _ = _ := by
      rw [Finset.sum_product]
      simp only [w,← Finset.mul_sum,total_gap_code_mass,← Finset.sum_mul]

end FiniteInverseMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteSpliceGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

def GraphSeparated (G : BondGraph V E) (A B : Set V) : Prop :=
  Disjoint A B ∧ ∀ a ∈ A, ∀ b ∈ B, ¬Adj G a b

theorem GraphSeparated.symm (G : BondGraph V E) (A B : Set V)
    (h : GraphSeparated G A B) : GraphSeparated G B A := by
  refine ⟨h.1.symm,?_⟩
  intro b hb a ha hab
  obtain ⟨e,he⟩ := hab
  exact h.2 a ha b hb ⟨e,he.trans (Sym2.eq_swap ..)⟩

theorem GraphSeparated.mono (G : BondGraph V E) {A B C D : Set V}
    (h : GraphSeparated G A B) (hC : C ⊆ A) (hD : D ⊆ B) : GraphSeparated G C D := by
  exact ⟨h.1.mono hC hD,fun c hc d hd => h.2 c (hC hc) d (hD hd)⟩

theorem GraphSeparated.no_shared_incidence (G : BondGraph V E) (A B : Set V)
    (h : GraphSeparated G A B) (e : E) (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (hea : a ∈ G e) (heb : b ∈ G e) : False := by
  have hne : a ≠ b := by
    rintro rfl
    exact Set.disjoint_left.mp h.1 ha hb
  exact h.2 a ha b hb ⟨e,(Sym2.mem_and_mem_iff hne).mp ⟨hea,heb⟩⟩

 

theorem slit_cluster_remove_remote (G : BondGraph V E) (η : Set E) (S H : Set V)
    (y : V) (hy : y ∉ S)
    (hsep : GraphSeparated G (cluster G (η ∩ internalEdges G Sᶜ) y) H) :
    cluster G (η ∩ internalEdges G (S \ H)ᶜ) y = cluster G (η ∩ internalEdges G Sᶜ) y := by
  apply Set.Subset.antisymm
  · intro v hv
    induction hv with
    | refl => exact conn_refl G _ y
    | @tail a b hya hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      have hbH : b ∉ H := fun hb => hsep.2 a ih b hb ⟨e,hab⟩
      have hbS : b ∉ S := by
        have hb := ((mem_internalEdges_of_ends G _ e a b hab).mp he.2).2
        exact fun h => hb ⟨h,hbH⟩
      have haS := slit_cluster_subset G S η y hy ih
      exact ih.tail ⟨e,⟨he.1,(mem_internalEdges_of_ends G _ e a b hab).mpr ⟨haS,hbS⟩⟩,hab⟩
  · exact fun _ h => conn_mono G
      (Set.inter_subset_inter_right _ (internalEdges_mono G (by
        intro v hv hvS
        exact hv hvS.1))) h

 

theorem spliceMask_remove_remote (G : BondGraph V E) (S B H : Set V) (e : E)
    (hsep : GraphSeparated G B H) : spliceMask G (S \ H) B e = spliceMask G S B e := by
  ext f
  simp only [spliceMask,Set.mem_insert_iff,Set.mem_ofPred_eq]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨⟨b,hb,hbf⟩,hi⟩
    refine ⟨⟨b,hb,hbf⟩,?_⟩
    intro v hv hvS
    have hvH : v ∉ H := fun hh => hsep.no_shared_incidence G B H f b v hb hh hbf hv
    exact hi v hv ⟨hvS,hvH⟩
  · rintro ⟨hb,hi⟩
    exact ⟨hb,fun v hv h => hi v hv h.1⟩

 
theorem spliceMask_incident (G : BondGraph V E) (S B : Set V) (e : E)
    (b : V) (hb : b ∈ B) (heb : b ∈ G e) :
    ∀ f ∈ spliceMask G S B e, ∃ v ∈ B, v ∈ G f := by
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact ⟨b,hb,heb⟩
  · exact hf.1

 

theorem disjoint_spliceMasks (G : BondGraph V E) (S₁ S₂ B₁ B₂ : Set V) (e₁ e₂ : E)
    (b₁ b₂ : V) (hb₁ : b₁ ∈ B₁) (hb₂ : b₂ ∈ B₂) (he₁ : b₁ ∈ G e₁) (he₂ : b₂ ∈ G e₂)
    (hsep : GraphSeparated G B₁ B₂) :
    Disjoint (spliceMask G S₁ B₁ e₁) (spliceMask G S₂ B₂ e₂) := by
  apply Set.disjoint_left.mpr
  intro f hf₁ hf₂
  obtain ⟨a,ha,haf⟩ := spliceMask_incident G S₁ B₁ e₁ b₁ hb₁ he₁ f hf₁
  obtain ⟨b,hb,hbf⟩ := spliceMask_incident G S₂ B₂ e₂ b₂ hb₂ he₂ f hf₂
  exact hsep.no_shared_incidence G B₁ B₂ f a b ha hb haf hbf

end RemoteSpliceGeometry

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section RemoteReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

def replaySplice (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → Set E
  | [], ω => ω
  | (i,e)::rest, ω =>
    replaySplice G x η y rest (spliceField G (cluster G ω x)
      (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i))

 
def replayMasks (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → List (ℕ × Set E)
  | [], _ => []
  | (i,e)::rest, ω =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    (i,spliceMask G S B e)::replayMasks G x η y rest (spliceField G S B e ω (η i))

 
def replayContacts (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V) :
    List (ℕ × E) → Set E → List (Set E)
  | [], _ => []
  | (i,e)::rest, ω =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    contactSet G (η i) B::replayContacts G x η y rest (spliceField G S B e ω (η i))

theorem SpliceTrace.replay_eq (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) : replaySplice G x η y steps ω = ωf := by
  induction h with
  | stop => rfl
  | step => assumption

 

theorem SpliceTrace.remote_replay (G : BondGraph V E) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (H : Set V) (ω₀ : Set E)
    (hroot : cluster G ω₀ x = cluster G ω x \ H)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω x) H)
    (hzH : y k ∉ H) :
    SpliceTrace G x η y k j ω₀ steps (replaySplice G x η y steps ω₀) ∧
      cluster G (replaySplice G x η y steps ω₀) x = cluster G ωf x \ H ∧
      replayMasks G x η y steps ω₀ = replayMasks G x η y steps ω ∧
      replayContacts G x η y steps ω₀ = replayContacts G x η y steps ω := by
  induction h generalizing ω₀ with
  | stop j ω hs =>
    refine ⟨SpliceTrace.stop j ω₀ ?_,hroot,rfl,rfl⟩
    rw [hroot]
    exact ⟨hs,hzH⟩
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    let S₀ := cluster G ω₀ x
    let B₀ := cluster G (η i ∩ internalEdges G S₀ᶜ) (y i)
    let ω₀' := spliceField G S₀ B₀ e ω₀ (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hBo : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hretain : cluster G ω' x ⊆ cluster G ωf x := ht.cluster_subset G x η y k i ω' ωf rest
    have hBT : B ⊆ cluster G ωf x \ S := by
      intro v hv
      refine ⟨hretain ?_,hBo hv⟩
      rw [hC]
      exact Or.inr hv
    have hsepB : GraphSeparated G B H := hsep.mono G hBT Set.Subset.rfl
    have hBB : B₀ = B := by
      dsimp only [B₀,S₀]
      rw [hroot]
      exact slit_cluster_remove_remote G (η i) S H (y i) hy hsepB
    have haH : a ∉ H := fun hh => hsepB.2 b hb a hh ⟨e,hab.trans (Sym2.eq_swap ..)⟩
    have ha₀ : a ∈ S₀ := by rw [show S₀ = S \ H from hroot]; exact ⟨ha,haH⟩
    have hy₀ : y i ∉ S₀ := by rw [show S₀ = S \ H from hroot]; exact fun h => hy h.1
    have hb₀ : b ∈ B₀ := hBB.symm ▸ hb
    have hC₀ : cluster G ω₀' x = S₀ ∪ B₀ :=
      splice_cluster G ω₀ (η i) x (y i) hy₀ e a b hab he ha₀ hb₀
    have hroot' : cluster G ω₀' x = cluster G ω' x \ H := by
      rw [hC₀,hC,hBB,show S₀ = S \ H from hroot]
      ext v
      constructor
      · rintro (⟨hv,hvH⟩ | hv)
        · exact ⟨Or.inl hv,hvH⟩
        · exact ⟨Or.inr hv,fun hvH => Set.disjoint_left.mp hsepB.1 hv hvH⟩
      · rintro ⟨hv,hvH⟩
        exact hv.elim (fun h => Or.inl ⟨h,hvH⟩) Or.inr
    have hsep' : GraphSeparated G (cluster G ωf x \ cluster G ω' x) H := by
      apply hsep.mono G _ Set.Subset.rfl
      intro v hv
      refine ⟨hv.1,fun h => hv.2 ?_⟩
      rw [hC]
      exact Or.inl h
    obtain ⟨ht₀,hfinal,hmasks,hcontacts⟩ := ih ω₀' hroot' hsep'
    have hn₀ : y k ∉ S₀ := by rw [show S₀ = S \ H from hroot]; exact fun h => hn h.1
    have hmax₀ : ∀ l, i < l → l ≤ k → Disjoint (cluster G (η l) (y l)) S₀ := by
      intro l hil hlk
      apply (hmax l hil hlk).mono Set.Subset.rfl
      rw [show S₀ = S \ H from hroot]
      exact Set.sdiff_subset
    have hmask : spliceMask G S₀ B₀ e = spliceMask G S B e := by
      rw [hBB,show S₀ = S \ H from hroot,spliceMask_remove_remote G S B H e hsepB]
    refine ⟨SpliceTrace.step j i ω₀ e a b rest _ hn₀ hji hik hmax₀ hy₀ he hab ha₀ hb₀ ht₀,
      hfinal,?_,?_⟩
    · change (i,spliceMask G S₀ B₀ e)::replayMasks G x η y rest ω₀' =
      (i,spliceMask G S B e)::replayMasks G x η y rest ω'
      rw [hmask,hmasks]
    · change contactSet G (η i) B₀::replayContacts G x η y rest ω₀' =
        contactSet G (η i) B::replayContacts G x η y rest ω'
      rw [hBB,hcontacts]

end RemoteReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DeterministicReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

def FollowsContactRule (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (choose : ℕ → Set E → E) (steps : List (ℕ × E)) (ω : Set E) : Prop :=
  List.Forall₂ (fun q K => choose q.1 K = q.2) steps (replayContacts G x η y steps ω)

theorem followsContactRule_cons (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (choose : ℕ → Set E → E) (i : ℕ) (e : E)
    (rest : List (ℕ × E)) (ω : Set E) :
    FollowsContactRule G x η y choose ((i,e)::rest) ω ↔
      choose i (contactSet G (η i)
        (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i))) = e ∧
      FollowsContactRule G x η y choose rest
        (spliceField G (cluster G ω x)
          (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) e ω (η i)) := by
  simp only [FollowsContactRule,replayContacts,List.forall₂_cons]

 

theorem SpliceTrace.remote_follows_contact_rule (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) (H : Set V) (ω₀ : Set E)
    (hroot : cluster G ω₀ x = cluster G ω x \ H)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω x) H) (hzH : y k ∉ H)
    (choose : ℕ → Set E → E) (hc : FollowsContactRule G x η y choose steps ω) :
    FollowsContactRule G x η y choose steps ω₀ := by
  unfold FollowsContactRule at hc ⊢
  rw [(h.remote_replay G x η y k j ω ωf steps H ω₀ hroot hsep hzH).2.2.2]
  exact hc

 

theorem SpliceTrace.seeded_unique (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ω₁ ω₂ : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η y k j ω c₁ ω₁)
    (h₂ : SpliceTrace G x η y k j ω c₂ ω₂) (choose : ℕ → Set E → E)
    (hc₁ : FollowsContactRule G x η y choose c₁ ω)
    (hc₂ : FollowsContactRule G x η y choose c₂ ω) : c₁ = c₂ ∧ ω₁ = ω₂ := by
  induction h₁ generalizing c₂ ω₂ with
  | stop j ω hs =>
    cases h₂ with
    | stop => exact ⟨rfl,rfl⟩
    | step _ _ _ _ _ _ _ _ hn => exact (hn hs).elim
  | @step j i ω e a b rest ω₁ hn hji hik hmax hy he hab ha hb ht ih =>
    cases h₂ with
    | stop _ _ hs => exact (hn hs).elim
    | step _ l _ f c d tail ω₂ hn₂ hjl hlk hmax₂ hy₂ hf hcd hc hd ht₂ =>
      have haC : a ∈ cluster G (η i) (y i) :=
        (edge_cluster_sides G (η i) (y i) he hab).mpr (conn_mono G Set.inter_subset_left hb)
      have hcC : c ∈ cluster G (η l) (y l) :=
        (edge_cluster_sides G (η l) (y l) hf hcd).mpr (conn_mono G Set.inter_subset_left hd)
      have hil : i = l := by
        rcases lt_trichotomy i l with hil | hil | hli
        · exact (Set.disjoint_left.mp (hmax l hil hlk) hcC hc).elim
        · exact hil
        · exact (Set.disjoint_left.mp (hmax₂ i hli hik) haC ha).elim
      subst l
      obtain ⟨hec,hrest⟩ := (followsContactRule_cons G x η y choose i e rest ω).mp hc₁
      obtain ⟨hfc,htail⟩ := (followsContactRule_cons G x η y choose i f tail ω).mp hc₂
      have hef : e = f := hec.symm.trans hfc
      rw [← hef] at ht₂ htail ⊢
      obtain ⟨hcodes,houts⟩ := ih ω₂ tail ht₂ hrest htail
      exact ⟨congrArg (List.cons (i,e)) hcodes,houts⟩

end DeterministicReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TraceMaskSupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
def maskUnion (masks : List (ℕ × Set E)) : Set E :=
  {e | ∃ q ∈ masks, e ∈ q.2}

@[simp] theorem maskUnion_nil : maskUnion ([] : List (ℕ × Set E)) = ∅ := by
  ext e
  simp [maskUnion]

@[simp] theorem maskUnion_cons (i : ℕ) (M : Set E) (ms : List (ℕ × Set E)) :
    maskUnion ((i,M)::ms) = M ∪ maskUnion ms := by
  ext e
  simp [maskUnion,or_and_right,exists_or]

 
theorem SpliceTrace.masks_incident (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ f ∈ maskUnion (replayMasks G x η y steps ω),
      ∃ b ∈ cluster G ωf x \ cluster G ω x, b ∈ G f := by
  induction h with
  | stop => simp [replayMasks]
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    have hB : B ⊆ Sᶜ := slit_cluster_subset G S (η i) (y i) hy
    have hretain := ht.cluster_subset G x η y k i ω' ωf rest
    intro f hf
    change f ∈ maskUnion ((i,spliceMask G S B e)::replayMasks G x η y rest ω') at hf
    rw [maskUnion_cons] at hf
    rcases hf with hf | hf
    · obtain ⟨v,hv,hvf⟩ := spliceMask_incident G S B e b hb (by simp [hab]) f hf
      refine ⟨v,⟨hretain ?_,hB hv⟩,hvf⟩
      rw [hC]
      exact Or.inr hv
    · obtain ⟨v,hv,hvf⟩ := ih f hf
      refine ⟨v,⟨hv.1,fun h => hv.2 ?_⟩,hvf⟩
      rw [hC]
      exact Or.inl h

 
theorem replaySplice_off_masks (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (steps : List (ℕ × E)) (ω : Set E) (f : E)
    (hf : f ∉ maskUnion (replayMasks G x η y steps ω)) :
    f ∈ replaySplice G x η y steps ω ↔ f ∈ ω := by
  induction steps generalizing ω with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i,e⟩ := q
    simp only [replayMasks,maskUnion_cons,Set.mem_union,not_or] at hf
    change f ∈ replaySplice G x η y rest _ ↔ f ∈ ω
    rw [ih _ hf.2]
    simp only [spliceField,mem_exchangeOn,ite_eq_right hf.1]

 
theorem SpliceTrace.masks_disjoint (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    Disjoint (maskUnion (replayMasks G x η₁ y₁ c₁ ω₁))
      (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) := by
  apply Set.disjoint_left.mpr
  intro f hf₁ hf₂
  obtain ⟨a,ha,hea⟩ := h₁.masks_incident G x η₁ y₁ k j₁ ω₁ ωf c₁ f hf₁
  obtain ⟨b,hb,heb⟩ := h₂.masks_incident G x η₂ y₂ k j₂ ω₂ ωf c₂ f hf₂
  exact hsep.no_shared_incidence G _ _ f a b ha hb hea heb

 

theorem conn_delete_rootBridge (G : BondGraph V E) (ω η : Set E) (x z : V)
    (hη : η ⊆ ω) (e : E) (a b : V) (hab : G e = s(a,b))
    (hb : b ∉ cluster G (ω \ {e}) x) (hz : z ∈ cluster G (ω \ {e}) x)
    (hxz : Conn G η x z) : Conn G (η \ {e}) x z := by
  have hc : Conn G (insert e (η \ {e})) x z := conn_mono G (by
    intro f hf
    by_cases hfe : f = e
    · exact Or.inl hfe
    · exact Or.inr ⟨hf,hfe⟩) hxz
  have hs : η \ {e} ⊆ ω \ {e} := Set.sdiff_subset_sdiff_left hη
  rw [conn_insert_iff G _ e a b x z hab] at hc
  rcases hc with hc | ⟨_,hc⟩ | ⟨hc,_⟩
  · exact hc
  · exact (hb (hz.trans (conn_symm G _ (conn_mono G hs hc)))).elim
  · exact (hb (conn_mono G hs hc)).elim

 
theorem cluster_double_cut (G : BondGraph V E) (ω : Set E) (x : V) (e f : E)
    (a b : V) (hab : G f = s(a,b)) (hb : b ∉ cluster G (ω \ {f}) x) :
    cluster G ((ω \ {e}) \ {f}) x = cluster G (ω \ {e}) x ∩ cluster G (ω \ {f}) x := by
  apply Set.Subset.antisymm
  · intro v hv
    exact ⟨conn_mono G Set.sdiff_subset hv,
      conn_mono G (ω₁ := (ω \ {e}) \ {f}) (ω₂ := ω \ {f}) (fun _ h => ⟨h.1.1,h.2⟩) hv⟩
  · intro v hv
    exact conn_delete_rootBridge G ω (ω \ {e}) x v Set.sdiff_subset f a b hab hb hv.2 hv.1

end TraceMaskSupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointRoot
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem mask_not_crossing_remote (G : BondGraph V E) (U : Set E) (A B : Set V)
    (hU : ∀ e ∈ U, ∃ v ∈ B, v ∈ G e) (hBA : B ⊆ A)
    (e : E) (a b : V) (hab : G e = s(a,b)) (haB : a ∉ B) (hbA : b ∉ A) : e ∉ U := by
  intro he
  obtain ⟨v,hv,hve⟩ := hU e he
  have hvab : v = a ∨ v = b := by simpa only [hab,Sym2.mem_iff] using hve
  rcases hvab with rfl | rfl
  · exact haB hv
  · exact hbA (hBA hv)

 

theorem exchange_patch_symm (U₁ U₂ ω₁ ω₂ ωf : Set E)
    (hdis : Disjoint U₁ U₂)
    (h₁ : ∀ e ∉ U₁, e ∈ ω₁ ↔ e ∈ ωf)
    (h₂ : ∀ e ∉ U₂, e ∈ ω₂ ↔ e ∈ ωf) :
    exchangeOn U₂ ω₁ ω₂ = exchangeOn U₁ ω₂ ω₁ := by
  ext e
  by_cases he₁ : e ∈ U₁
  · have he₂ : e ∉ U₂ := fun h => Set.disjoint_left.mp hdis he₁ h
    simp only [mem_exchangeOn,ite_eq_right he₂,ite_eq_left he₁]
  · by_cases he₂ : e ∈ U₂
    · simp only [mem_exchangeOn,ite_eq_left he₂,ite_eq_right he₁]
    · simp only [mem_exchangeOn,ite_eq_right he₁,ite_eq_right he₂]
      exact (h₁ e he₁).trans (h₂ e he₂).symm

 

theorem SpliceTrace.joint_root (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ i₁ i₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (e₁ e₂ : E) (r₁ r₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ ((i₁,e₁)::r₁) ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ ((i₂,e₂)::r₂) ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    cluster G (exchangeOn (maskUnion (replayMasks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂)) ω₁ ω₂) x =
      cluster G ω₁ x ∩ cluster G ω₂ x := by
  let A₁ := cluster G ω₁ x
  let A₂ := cluster G ω₂ x
  let B₁ := cluster G ωf x \ A₁
  let B₂ := cluster G ωf x \ A₂
  let U₁ := maskUnion (replayMasks G x η₁ y₁ ((i₁,e₁)::r₁) ω₁)
  let U₂ := maskUnion (replayMasks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂)
  let ω₀ := exchangeOn U₂ ω₁ ω₂
  have hsub₁ := h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)
  have hsub₂ := h₂.cluster_subset G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)
  have hBA₁ : B₁ ⊆ A₂ := by
    intro v hv
    by_contra hn
    exact Set.disjoint_left.mp hsep.1 hv ⟨hv.1,hn⟩
  have hBA₂ : B₂ ⊆ A₁ := by
    intro v hv
    by_contra hn
    exact Set.disjoint_left.mp hsep.1 ⟨hv.1,hn⟩ hv
  have hU₁ : ∀ e ∈ U₁, ∃ v ∈ B₁, v ∈ G e :=
    h₁.masks_incident G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)
  have hU₂ : ∀ e ∈ U₂, ∃ v ∈ B₂, v ∈ G e :=
    h₂.masks_incident G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)
  have hdis : Disjoint U₁ U₂ := h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf
    ((i₁,e₁)::r₁) ((i₂,e₂)::r₂) h₂ hsep
  have hoff₁ : ∀ e ∉ U₁, e ∈ ω₁ ↔ e ∈ ωf := by
    intro e he
    rw [← h₁.replay_eq G x η₁ y₁ k j₁ ω₁ ωf ((i₁,e₁)::r₁)]
    exact (replaySplice_off_masks G x η₁ y₁ ((i₁,e₁)::r₁) ω₁ e he).symm
  have hoff₂ : ∀ e ∉ U₂, e ∈ ω₂ ↔ e ∈ ωf := by
    intro e he
    rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂)]
    exact (replaySplice_off_masks G x η₂ y₂ ((i₂,e₂)::r₂) ω₂ e he).symm
  have hsym : ω₀ = exchangeOn U₁ ω₂ ω₁ := exchange_patch_symm U₁ U₂ ω₁ ω₂ ωf hdis hoff₁ hoff₂
  have hcut₁ := h₁.head_cut G x η₁ y₁ k j₁ i₁ ω₁ ωf e₁ r₁
  have hcut₂ := h₂.head_cut G x η₂ y₂ k j₂ i₂ ω₂ ωf e₂ r₂
  obtain ⟨a,b,hab,_,hb,_⟩ := openMarkedPivotal_oriented G ωf {y₂ k} x
    (h₂.seams_pivotal G x η₂ y₂ k j₂ ω₂ ωf ((i₂,e₂)::r₂) (i₂,e₂) (by simp))
  have hdouble : cluster G ((ωf \ {e₁}) \ {e₂}) x = A₁ ∩ A₂ := by
    rw [cluster_double_cut G ωf x e₁ e₂ a b hab hb,hcut₁,hcut₂]
  change cluster G ω₀ x = A₁ ∩ A₂
  apply Set.Subset.antisymm
  · intro v hv
    induction hv with
    | refl => exact ⟨conn_refl G _ x,conn_refl G _ x⟩
    | @tail a b hxa hab ih =>
      obtain ⟨e,he,hab⟩ := hab
      constructor
      · by_contra hb
        have hno := mask_not_crossing_remote G U₂ A₁ B₂ hU₂ hBA₂ e a b hab
          (fun hh => hh.2 ih.2) hb
        have he₁ : e ∈ ω₁ := by simpa only [ω₀,mem_exchangeOn,ite_eq_right hno] using he
        exact hb ((edge_cluster_sides G ω₁ x he₁ hab).mp ih.1)
      · by_contra hb
        have hno := mask_not_crossing_remote G U₁ A₂ B₁ hU₁ hBA₁ e a b hab
          (fun hh => hh.2 ih.1) hb
        have he₂ : e ∈ ω₂ := by simpa only [hsym,mem_exchangeOn,ite_eq_right hno] using he
        exact hb ((edge_cluster_sides G ω₂ x he₂ hab).mp ih.2)
  · intro v hv
    have hc : Conn G ((ωf \ {e₁}) \ {e₂}) x v := by
      change v ∈ cluster G ((ωf \ {e₁}) \ {e₂}) x
      rw [hdouble]
      exact hv
    have hr := conn_restrict_cluster G ((ωf \ {e₁}) \ {e₂}) x (mem_cluster_self G _ x) hc
    apply conn_mono G _ hr
    intro e he
    have hi : e ∈ internalEdges G (A₁ ∩ A₂) := by
      simpa only [hdouble] using he.2
    have hno : e ∉ U₂ := by
      intro hu
      obtain ⟨b,hb,heb⟩ := hU₂ e hu
      exact hb.2 (hi b heb).2
    have he₁ : e ∈ ω₁ := (h₁.internal_agreement G x η₁ y₁ k j₁ ω₁ ωf
      ((i₁,e₁)::r₁) e (fun a ha => (hi a ha).1)).mp he.1.1.1
    simpa only [ω₀,mem_exchangeOn,ite_eq_right hno] using he₁

end JointRoot

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section MaskExecution
attribute [local instance] Classical.propDecidable Classical.decEq

 
def runMasks : List (ℕ × Set E) → SpliceState E → SpliceState E
  | [], s => s
  | (i,M)::ms, s => runMasks ms (exchangeState M i s)

 
def patchFirst (U τ : Set E) (s : SpliceState E) : SpliceState E :=
  (exchangeOn U s.1 τ,s.2)

theorem exchangeState_patchFirst (U τ M : Set E) (i : ℕ) (s : SpliceState E)
    (hdis : Disjoint M U) :
    exchangeState M i (patchFirst U τ s) = patchFirst U τ (exchangeState M i s) := by
  apply Prod.ext
  · ext e
    by_cases heM : e ∈ M
    · have heU : e ∉ U := fun he => Set.disjoint_left.mp hdis heM he
      simp only [exchangeState,patchFirst,mem_exchangeOn,ite_eq_left heM,ite_eq_right heU]
    · by_cases heU : e ∈ U <;>
      simp only [exchangeState,patchFirst,mem_exchangeOn,ite_eq_right heM,heU,ite_true,ite_false]
  · funext l
    by_cases hli : l = i
    · subst l
      ext e
      by_cases heM : e ∈ M
      · have heU : e ∉ U := fun he => Set.disjoint_left.mp hdis heM he
        simp only [exchangeState,patchFirst,Function.update_self,mem_exchangeOn,ite_eq_left heM,ite_eq_right heU]
      · simp only [exchangeState,patchFirst,Function.update_self,mem_exchangeOn,ite_eq_right heM]
    · simp only [exchangeState,patchFirst,Function.update_of_ne hli]

 

theorem runMasks_patchFirst (ms : List (ℕ × Set E)) (U τ : Set E) (s : SpliceState E)
    (hdis : Disjoint (maskUnion ms) U) :
    runMasks ms (patchFirst U τ s) = patchFirst U τ (runMasks ms s) := by
  induction ms generalizing s with
  | nil => rfl
  | cons q ms ih =>
    obtain ⟨i,M⟩ := q
    rw [maskUnion_cons,Set.disjoint_union_left] at hdis
    simp only [runMasks]
    rw [exchangeState_patchFirst U τ M i s hdis.1,ih _ hdis.2]

 

theorem SpliceTrace.runMasks_first (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (steps : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω steps ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
    (runMasks (replayMasks G x η y steps ω) (ω,θ)).1 = ωf := by
  induction h with
  | stop => exact fun _ _ => rfl
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    intro θ hθ
    have hθi := hθ i hji hik
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let M := spliceMask G S B e
    let ω' := spliceField G S B e ω (η i)
    let θ' := Function.update θ i (exchangeOn M (θ i) ω)
    have hstep : exchangeState M i (ω,θ) = (ω',θ') := by
      apply Prod.ext
      · change exchangeOn M ω (θ i) = exchangeOn M ω (η i)
        rw [hθi]
      · rfl
    change (runMasks (replayMasks G x η y rest ω') (exchangeState M i (ω,θ))).1 = ωf
    rw [hstep]
    apply ih θ'
    intro l hil hlk
    rw [show θ' l = θ l from Function.update_of_ne (by omega) _ _]
    exact hθ l (hji.trans hil) hlk

 
theorem runMasks_weight (ms : List (ℕ × Set E)) (s : SpliceState E)
    (Q : Finset E) (J : Finset ℕ) (p : ℝ) (hJ : ∀ q ∈ ms, q.1 ∈ J) :
    spliceTupleWeight Q J p (runMasks ms s) = spliceTupleWeight Q J p s := by
  induction ms generalizing s with
  | nil => rfl
  | cons q ms ih =>
    obtain ⟨i,M⟩ := q
    rw [runMasks,ih _ (fun q hq => hJ q (List.mem_cons_of_mem _ hq))]
    exact spliceTupleWeight_exchange Q J p s M i (hJ (i,M) (List.mem_cons_self ..))

 

theorem SpliceTrace.joint_replay_state (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let m₁ := replayMasks G x η₁ y₁ c₁ ω₁
    let m₂ := replayMasks G x η₂ y₂ c₂ ω₂
    let ω₀ := exchangeOn (maskUnion m₂) ω₁ ω₂
    runMasks m₁ (ω₀,η₁) = (ω₂,(runMasks m₁ (ω₁,η₁)).2) := by
  intro m₁ m₂ ω₀
  have hdis := h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep
  have hroot := h₁.runMasks_first G x η₁ y₁ k j₁ ω₁ ωf c₁ η₁ (by intros; rfl)
  have hpatch : exchangeOn (maskUnion m₂) ωf ω₂ = ω₂ := by
    ext e
    by_cases he : e ∈ maskUnion m₂
    · simp only [mem_exchangeOn,ite_eq_left he]
    · simp only [mem_exchangeOn,ite_eq_right he]
      rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf c₂]
      exact replaySplice_off_masks G x η₂ y₂ c₂ ω₂ e he
  change runMasks m₁ (patchFirst (maskUnion m₂) ω₂ (ω₁,η₁)) = _
  rw [runMasks_patchFirst m₁ _ ω₂ _ hdis]
  change (exchangeOn (maskUnion m₂) (runMasks m₁ (ω₁,η₁)).1 ω₂,_) = _
  rw [hroot,hpatch]

end MaskExecution

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointReplay
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.endpoint_not_mem_of_ne_nil (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (hc : c ≠ []) : y k ∉ cluster G ω x := by
  cases h with
  | stop => exact (hc rfl).elim
  | step _ _ _ _ _ _ _ _ hn => exact hn

 

theorem SpliceTrace.joint_virtual (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let ω₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂
    SpliceTrace G x η₁ y₁ k j₁ ω₀ c₁ ω₂ ∧
      replayMasks G x η₁ y₁ c₁ ω₀ = replayMasks G x η₁ y₁ c₁ ω₁ ∧
      replayContacts G x η₁ y₁ c₁ ω₀ = replayContacts G x η₁ y₁ c₁ ω₁ := by
  intro ω₀
  have hroot' : cluster G ω₀ x = cluster G ω₁ x ∩ cluster G ω₂ x := by
    cases c₁ with
    | nil => exact (hc₁ rfl).elim
    | cons q r₁ =>
      obtain ⟨i₁,e₁⟩ := q
      cases c₂ with
      | nil => exact (hc₂ rfl).elim
      | cons q r₂ =>
        obtain ⟨i₂,e₂⟩ := q
        exact h₁.joint_root G x η₁ η₂ y₁ y₂ k j₁ j₂ i₁ i₂ ω₁ ω₂ ωf e₁ e₂ r₁ r₂ h₂ hsep
  let H := cluster G ωf x \ cluster G ω₂ x
  have hroot : cluster G ω₀ x = cluster G ω₁ x \ H := by
    rw [hroot']
    ext v
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,fun hh => hh.2 h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨h1,?_⟩
      by_contra hn
      exact h2 ⟨h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf c₁ h1,hn⟩
  have hz : y₁ k ∉ H := fun hz => Set.disjoint_left.mp hsep.1
    ⟨h₁.endpoint G x η₁ y₁ k j₁ ω₁ ωf c₁,
      h₁.endpoint_not_mem_of_ne_nil G x η₁ y₁ k j₁ ω₁ ωf c₁ hc₁⟩ hz
  obtain ⟨ht,hout,hm,hcontacts⟩ := h₁.remote_replay G x η₁ y₁ k j₁ ω₁ ωf c₁ H ω₀ hroot hsep hz
  have hf := ht.runMasks_first G x η₁ y₁ k j₁ ω₀ (replaySplice G x η₁ y₁ c₁ ω₀) c₁ η₁
    (by intros; rfl)
  rw [hm] at hf
  have hs := h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep
  have heq : replaySplice G x η₁ y₁ c₁ ω₀ = ω₂ := hf.symm.trans (congrArg Prod.fst hs)
  rw [heq] at ht
  exact ⟨ht,hm,hcontacts⟩

 

theorem joint_restore_seeded_unique (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (choose₁ choose₂ : ℕ → Set E → E)
    (k j₁ j₂ : ℕ) (ω₁ ω₂ ωf σ₁ σ₂ σf : Set E)
    (c₁ c₂ d₁ d₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (g₁ : SpliceTrace G x η₁ y₁ k j₁ σ₁ d₁ σf)
    (g₂ : SpliceTrace G x η₂ y₂ k j₂ σ₂ d₂ σf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ []) (hd₁ : d₁ ≠ []) (hd₂ : d₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (gsep : GraphSeparated G (cluster G σf x \ cluster G σ₁ x)
      (cluster G σf x \ cluster G σ₂ x))
    (hr₁ : FollowsContactRule G x η₁ y₁ choose₁ c₁ ω₁)
    (hr₂ : FollowsContactRule G x η₂ y₂ choose₂ c₂ ω₂)
    (gr₁ : FollowsContactRule G x η₁ y₁ choose₁ d₁ σ₁)
    (gr₂ : FollowsContactRule G x η₂ y₂ choose₂ d₂ σ₂)
    (hrestore : exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂ =
      exchangeOn (maskUnion (replayMasks G x η₂ y₂ d₂ σ₂)) σ₁ σ₂) :
    c₁ = d₁ ∧ c₂ = d₂ ∧ ωf = σf ∧
      (runMasks (replayMasks G x η₁ y₁ c₁ ω₁) (ω₁,η₁)).2 =
        (runMasks (replayMasks G x η₁ y₁ d₁ σ₁) (σ₁,η₁)).2 ∧
      (runMasks (replayMasks G x η₂ y₂ c₂ ω₂) (ω₂,η₂)).2 =
        (runMasks (replayMasks G x η₂ y₂ d₂ σ₂) (σ₂,η₂)).2 := by
  let ω₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂
  let σ₀ := exchangeOn (maskUnion (replayMasks G x η₂ y₂ d₂ σ₂)) σ₁ σ₂
  obtain ⟨ht,hm,hcontact⟩ := h₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep
  obtain ⟨gt,gm,gcontact⟩ := g₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ σ₁ σ₂ σf d₁ d₂ g₂ hd₁ hd₂ gsep
  have hrc : FollowsContactRule G x η₁ y₁ choose₁ c₁ ω₀ := by
    unfold FollowsContactRule at hr₁ ⊢
    rw [hcontact]
    exact hr₁
  have grc : FollowsContactRule G x η₁ y₁ choose₁ d₁ σ₀ := by
    unfold FollowsContactRule at gr₁ ⊢
    rw [gcontact]
    exact gr₁
  change SpliceTrace G x η₁ y₁ k j₁ σ₀ d₁ σ₂ at gt
  change replayMasks G x η₁ y₁ c₁ ω₀ = _ at hm
  change replayMasks G x η₁ y₁ d₁ σ₀ = _ at gm
  have h00 : ω₀ = σ₀ := hrestore
  rw [← h00] at gt grc
  obtain ⟨hcode₁,hω₂⟩ := ht.seeded_unique G x η₁ y₁ k j₁ ω₀ ω₂ σ₂ c₁ d₁ gt choose₁ hrc grc
  rw [← hω₂] at g₂ gr₂
  obtain ⟨hcode₂,hout⟩ := h₂.seeded_unique G x η₂ y₂ k j₂ ω₂ ωf σf c₂ d₂ g₂ choose₂ hr₂ gr₂
  refine ⟨hcode₁,hcode₂,hout,?_,?_⟩
  · have hs := congrArg Prod.snd (h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep)
    have gs := congrArg Prod.snd (g₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ σ₁ σ₂ σf d₁ d₂
      (hω₂ ▸ g₂) gsep)
    change (runMasks _ (ω₀,η₁)).2 = _ at hs
    change (runMasks _ (σ₀,η₁)).2 = _ at gs
    rw [← hs,← gs,← hm,← gm,h00,hcode₁]
  · rw [hcode₂,hω₂]

end JointReplay

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointWeight
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev JointSpliceState (E : Type v) := Set E × (ℕ → Set E) × (ℕ → Set E)

noncomputable def jointTupleWeight (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (s : JointSpliceState E) : ℝ :=
  bernoulliWeight Q (domainBits Q s.1) p *
    (∏ i ∈ J₁, bernoulliWeight Q (domainBits Q (s.2.1 i)) p) *
    ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (s.2.2 i)) p

theorem jointTupleWeight_nonneg (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (p : unitInterval) (s : JointSpliceState E) : 0 ≤ jointTupleWeight Q J₁ J₂ p s := by
  exact mul_nonneg (spliceTupleWeight_nonneg Q J₁ p (s.1,s.2.1))
    (Finset.prod_nonneg fun _ _ => bernoulliWeight_nonneg _ _ p)

theorem replayMasks_indices (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) :
    (replayMasks G x η y c ω).map Prod.fst = c.map Prod.fst := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨i,e⟩ := q
    simp only [replayMasks,List.map_cons,ih]

theorem replayMasks_indices_mem (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (J : Finset ℕ)
    (hJ : ∀ q ∈ c, q.1 ∈ J) : ∀ q ∈ replayMasks G x η y c ω, q.1 ∈ J := by
  intro q hq
  have hq' : q.1 ∈ (replayMasks G x η y c ω).map Prod.fst := List.mem_map_of_mem hq
  rw [replayMasks_indices G x η y c ω] at hq'
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hq'
  exact he ▸ hJ r hr

 

theorem SpliceTrace.joint_weight (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (hJ₁ : ∀ q ∈ c₁, q.1 ∈ J₁) (hJ₂ : ∀ q ∈ c₂, q.1 ∈ J₂) :
    let m₁ := replayMasks G x η₁ y₁ c₁ ω₁
    let m₂ := replayMasks G x η₂ y₂ c₂ ω₂
    let ω₀ := exchangeOn (maskUnion m₂) ω₁ ω₂
    jointTupleWeight Q J₁ J₂ p (ωf,(runMasks m₁ (ω₁,η₁)).2,(runMasks m₂ (ω₂,η₂)).2) =
      jointTupleWeight Q J₁ J₂ p (ω₀,η₁,η₂) := by
  intro m₁ m₂ ω₀
  have hw₁ := runMasks_weight m₁ (ω₀,η₁) Q J₁ p
    (replayMasks_indices_mem G x η₁ y₁ c₁ ω₁ J₁ hJ₁)
  rw [h₁.joint_replay_state G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep] at hw₁
  have hw₂ := runMasks_weight m₂ (ω₂,η₂) Q J₂ p
    (replayMasks_indices_mem G x η₂ y₂ c₂ ω₂ J₂ hJ₂)
  unfold spliceTupleWeight at hw₁ hw₂
  rw [h₂.runMasks_first G x η₂ y₂ k j₂ ω₂ ωf c₂ η₂ (by intros; rfl)] at hw₂
  unfold jointTupleWeight
  dsimp only at hw₁ hw₂ ⊢
  calc
    _ = (bernoulliWeight Q (domainBits Q ωf) p *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q ((runMasks m₂ (ω₂,η₂)).2 i)) p) *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p := by ring
    _ = (bernoulliWeight Q (domainBits Q ω₂) p *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (η₂ i)) p) *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p := by rw [hw₂]
    _ = (bernoulliWeight Q (domainBits Q ω₂) p *
        ∏ i ∈ J₁, bernoulliWeight Q (domainBits Q ((runMasks m₁ (ω₁,η₁)).2 i)) p) *
        ∏ i ∈ J₂, bernoulliWeight Q (domainBits Q (η₂ i)) p := by ring
    _ = _ := by rw [hw₁]

end JointWeight

end Percolation

end OAI
