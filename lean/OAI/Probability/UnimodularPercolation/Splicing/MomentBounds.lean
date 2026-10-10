import Mathlib
import OAI.Probability.UnimodularPercolation.Splicing.ReferenceLaws

namespace OAI

/-! Moment Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceMeasurable
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem uniformRank_fiber_eq (K : ℕ) (hK : 0 < K) (a : Fin K) :
    {t : unitInterval | uniformRank K hK t = a} = contactInterval K a.val ∪
      (if uniformRank K hK 1 = a then {1} else ∅) := by
  ext t
  by_cases ht : t = 1
  · subst t
    have hnot : (1 : unitInterval) ∉ contactInterval K a.val := by
      intro h
      have hp : (0:ℝ) < K := by exact_mod_cast hK
      have hlt := (lt_div_iff₀ hp).mp h.2
      have ha : (a.val:ℝ)+1 ≤ K := by exact_mod_cast (show a.val+1 ≤ K by omega)
      push_cast at hlt
      norm_num at hlt
      linarith
    simp [hnot]
  · have hlt : (t:ℝ) < 1 := lt_of_le_of_ne t.property.2 (fun he => ht (Subtype.ext he))
    have he := uniformRank_eq_iff K hK t hlt a
    simp only [Set.mem_union,Set.mem_ofPred_eq]
    split_ifs <;> simpa [ht] using he

theorem measurableSet_contactInterval (K a : ℕ) : MeasurableSet (contactInterval K a) :=
  (measurableSet_le measurable_const measurable_subtype_coe).inter
    (measurableSet_lt measurable_subtype_coe measurable_const)

theorem measurableSet_uniformRank_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    MeasurableSet {t : unitInterval | uniformRank K hK t = a} := by
  rw [uniformRank_fiber_eq]
  apply (measurableSet_contactInterval K a.val).union
  split_ifs
  · exact measurableSet_singleton _
  · exact MeasurableSet.empty

theorem measurableSet_uniformContact_fiber (K : Finset E) (hK : K.Nonempty) (e : E) :
    MeasurableSet {t : unitInterval | uniformContact K hK t = e} := by
  by_cases he : e ∈ K
  · simp_rw [uniformContact_eq_iff K hK _ e he]
    exact measurableSet_uniformRank_fiber _ _ _
  · have hz : {t : unitInterval | uniformContact K hK t = e} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => he (h ▸ uniformContact_mem K hK t)
    rw [hz]
    exact MeasurableSet.empty

theorem measurableSet_chooseContact_fiber [Nonempty E] (i : ℕ) (K : Set E) (e : E) :
    MeasurableSet {t : unitInterval | chooseContact (fun _ => t) i K = e} := by
  unfold chooseContact
  split_ifs
  · exact measurableSet_uniformContact_fiber _ _ _
  · by_cases he : Classical.arbitrary E = e <;> simp [he]
  · by_cases he : Classical.arbitrary E = e <;> simp [he]

theorem measurableSet_replaySeedFiber [Nonempty E] (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (i : ℕ) :
    MeasurableSet (replaySeedFiber G x η y c ω i) := by
  induction c generalizing ω with
  | nil => exact MeasurableSet.univ
  | cons q c ih =>
    obtain ⟨j,e⟩ := q
    simp only [replaySeedFiber]
    split_ifs
    · exact measurableSet_chooseContact_fiber _ _ _
    · exact ih _

theorem SpliceTrace.measurableSet_seed_event [Nonempty E] (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf) :
    MeasurableSet {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω} := by
  rw [h.seed_event_eq_pi G x η y k j ω ωf c]
  exact MeasurableSet.univ_pi (fun i => measurableSet_replaySeedFiber G x η y c ω (i.val+1))

end SeededTraceMeasurable
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteTraceDistribution
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem finite_bounded_lists {A : Type*} (Q : Finset A) (k : ℕ) :
    {c : List A | c.length ≤ k ∧ ∀ q ∈ c, q ∈ Q}.Finite := by
  have hf := (List.finite_length_le ↥Q k).image (List.map Subtype.val)
  apply hf.subset
  rintro c ⟨hc,hQ⟩
  let d : List ↥Q := c.attach.map (fun q => ⟨q.val,hQ q.val q.property⟩)
  refine ⟨d,?_,?_⟩
  · simpa only [d,List.length_map,List.length_attach,Set.mem_ofPred_eq] using hc
  · simp [d,List.map_map]

noncomputable def boundedTraceCodes (Q : Finset E) (k : ℕ) : Finset (List (ℕ × E)) :=
  (finite_bounded_lists ((Finset.Icc 1 k) ×ˢ Q) k).toFinset

@[simp] theorem mem_boundedTraceCodes (Q : Finset E) (k : ℕ) (c : List (ℕ × E)) :
    c ∈ boundedTraceCodes Q k ↔ c.length ≤ k ∧ ∀ q ∈ c, 1 ≤ q.1 ∧ q.1 ≤ k ∧ q.2 ∈ Q := by
  simp [boundedTraceCodes,Finset.mem_product,and_assoc]

theorem SpliceTrace.length_le (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) : c.length ≤ k-j := by
  induction h with
  | stop => simp
  | step => simp only [List.length_cons]; omega

theorem SpliceTrace.mem_boundedTraceCodes (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E)) : c ∈ boundedTraceCodes Q k := by
  rw [Percolation.mem_boundedTraceCodes]
  refine ⟨(h.length_le G x η y k j ω ωf c).trans (Nat.sub_le ..),?_⟩
  intro q hq
  obtain ⟨hj,hk,he,_⟩ := h.seam_data G x η y k j ω ωf c q hq
  exact ⟨by omega,hk,hQ q.1 (by omega) hk he⟩

 

noncomputable def finiteTraceCodes (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω : Set E) (Q : Finset E) : Finset (List (ℕ × E)) :=
  (boundedTraceCodes Q k).filter (fun c =>
    SpliceTrace G x η y k j ω c (replaySplice G x η y c ω))

theorem mem_finiteTraceCodes_iff (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k j : ℕ) (ω : Set E) (Q : Finset E) (c : List (ℕ × E)) :
    c ∈ finiteTraceCodes G x η y k j ω Q ↔ c ∈ boundedTraceCodes Q k ∧
      SpliceTrace G x η y k j ω c (replaySplice G x η y c ω) := by
  simp [finiteTraceCodes]

 

theorem finite_trace_seed_partition [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k M : ℕ) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E))
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    let S := finiteTraceCodes G x η y k j ω Q
    let A := fun c => {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω}
    (⋃ c ∈ S, A c) = Set.univ ∧ Set.PairwiseDisjoint (↑S) A := by
  intro S A
  constructor
  · apply Set.eq_univ_of_forall
    intro u
    obtain ⟨c,ωf,ht,hr,_⟩ := exists_seeded_spliceTrace G hloc x η y k M hchain hcaps
      (chooseContact (finiteContactSeeds k u)) (chooseContact_mem _) j hj ω hyj _ hfin (le_refl _)
    have hc : c ∈ S := (mem_finiteTraceCodes_iff ..).mpr
      ⟨ht.mem_boundedTraceCodes G x η y k j ω ωf c Q hQ,
        (ht.replay_eq G x η y k j ω ωf c).symm ▸ ht⟩
    exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hc,hr⟩⟩
  · intro c hc d hd hcd
    apply Set.disjoint_left.mpr
    intro u huc hud
    have ht := (mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc
    have hs := (mem_finiteTraceCodes_iff G x η y k j ω Q d).mp hd
    exact hcd (ht.2.seeded_unique G x η y k j ω _ _ c d hs.2
      (chooseContact (finiteContactSeeds k u)) huc hud).1

 
theorem sum_finite_trace_probabilities [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (k M : ℕ) (Q : Finset E)
    (hQ : ∀ i, 1 ≤ i → i ≤ k → η i ⊆ (Q : Set E))
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    (∑ c ∈ finiteTraceCodes G x η y k j ω Q,
      ∏ i : Fin k, (traceContactCount G η y (replaySplice G x η y c ω) x c (i.val+1):ℝ)⁻¹) = 1 := by
  let S := finiteTraceCodes G x η y k j ω Q
  let A := fun c => {u : Fin k → unitInterval | FollowsContactRule G x η y
    (chooseContact (finiteContactSeeds k u)) c ω}
  have hpart := finite_trace_seed_partition G hloc x η y k M Q hQ hchain hcaps j hj ω hyj hfin
  have hm : ∀ c ∈ S, MeasurableSet (A c) := by
    intro c hc
    exact ((mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc).2.measurableSet_seed_event
      G x η y k j ω _ c
  have hsum : ∑ c ∈ S, volume (A c) = 1 := by
    rw [← measure_biUnion_finset hpart.2 hm,hpart.1,measure_univ]
  have hr := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum (fun c _ => measure_ne_top volume (A c)),ENNReal.toReal_one] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro c hc
  exact (((mem_finiteTraceCodes_iff G x η y k j ω Q c).mp hc).2.seed_probability
    G hloc x η y k j ω _ c (fun i hi hik => (hcaps i (Finset.mem_Icc.mpr ⟨hi,hik⟩)).1)).symm

end FiniteTraceDistribution
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSpliceState
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem SpliceTrace.runMasks_execution (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) :
    ∀ θ : ℕ → Set E, (∀ l, j < l → l ≤ k → θ l = η l) →
      SpliceExecution G x (ω,θ) c (runMasks (replayMasks G x η y c ω) (ω,θ)) := by
  induction h with
  | stop => intro θ _; exact SpliceExecution.nil _
  | @step j i ω e a b c ωf hn hji hik hm hy he hab ha hb ht ih =>
    intro θ hθ
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let M := spliceMask G S B e
    let ω' := spliceField G S B e ω (η i)
    let θ' := Function.update θ i (exchangeOn M (θ i) ω)
    have hθi := hθ i hji hik
    have hstep : exchangeState M i (ω,θ) = (ω',θ') := by
      apply Prod.ext
      · change exchangeOn M ω (θ i) = exchangeOn M ω (η i)
        rw [hθi]
      · rfl
    change SpliceExecution G x (ω,θ) ((i,e)::c)
      (runMasks (replayMasks G x η y c ω') (exchangeState M i (ω,θ)))
    rw [hstep]
    refine SpliceExecution.cons (ω,θ) (ω',θ') _ (i,e) c ?_ ?_
    · refine ⟨y i,a,b,hy,?_,hab,ha,?_,?_⟩
      · simpa only [hθi] using he
      · simpa only [hθi] using hb
      · simpa only [hθi] using hstep.symm
    · apply ih θ'
      intro l hil hlk
      rw [show θ' l = θ l from Function.update_of_ne (by omega) _ _]
      exact hθ l (hji.trans hil) hlk

abbrev FiniteSpliceData (Q : Finset E) (J : Finset ℕ) :=
  FiniteField Q × (↥J → FiniteField Q)

def encodeFiniteSplice (Q : Finset E) (J : Finset ℕ)
    (s : FiniteSpliceData Q J) : SpliceState E :=
  (finiteFieldSet Q s.1,finiteFieldFamily Q J s.2)

theorem encodeFiniteSplice_injective (Q : Finset E) (J : Finset ℕ) :
    Function.Injective (encodeFiniteSplice Q J) := by
  intro a b he
  exact Prod.ext (finiteFieldSet_injective Q (congrArg Prod.fst he))
    (finiteFieldFamily_injective Q J (congrArg Prod.snd he))

noncomputable def finiteSpliceDomain (Q : Finset E) (J : Finset ℕ) : Finset (SpliceState E) :=
  Finset.univ.image (encodeFiniteSplice Q J)

theorem spliceTupleWeight_encode (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (s : FiniteSpliceData Q J) : spliceTupleWeight Q J p (encodeFiniteSplice Q J s) =
      finiteFieldWeight Q p s.1 * finiteFamilyWeight Q J p s.2 := by
  simp only [spliceTupleWeight,encodeFiniteSplice,domainBits_finiteFieldSet,
    prod_fieldFamilyWeight,finiteFieldWeight]

theorem sum_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ) (p : ℝ) :
    ∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s = 1 := by
  rw [finiteSpliceDomain,Finset.sum_image (encodeFiniteSplice_injective Q J).injOn]
  simp only [spliceTupleWeight_encode,Fintype.sum_prod_type,← Finset.mul_sum,
    sum_finiteFamilyWeight,mul_one,sum_finiteFieldWeight]

 
theorem mem_finiteSpliceDomain_iff (Q : Finset E) (J : Finset ℕ) (s : SpliceState E) :
    s ∈ finiteSpliceDomain Q J ↔ s.1 ⊆ (Q : Set E) ∧
      (∀ i, s.2 i ⊆ (Q : Set E)) ∧ ∀ i ∉ J, s.2 i = ∅ := by
  constructor
  · intro hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨?_,?_,?_⟩
    · exact Finset.coe_subset.mpr (Finset.mem_powerset.mp a.1.property)
    · intro i
      by_cases hi : i ∈ J
      · simpa only [encodeFiniteSplice,finiteFieldFamily,dite_eq_left hi,finiteFieldSet] using
          Finset.coe_subset.mpr (Finset.mem_powerset.mp (a.2 ⟨i,hi⟩).property)
      · simp [encodeFiniteSplice,finiteFieldFamily,hi]
    · intro i hi
      simp [encodeFiniteSplice,finiteFieldFamily,hi]
  · rintro ⟨hω,hη,hz⟩
    let desc (ω : Set E) : FiniteField Q := ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩
    have he (ω : Set E) (h : ω ⊆ (Q : Set E)) : finiteFieldSet Q (desc ω) = ω := by
      ext e
      simp only [finiteFieldSet,desc,Finset.mem_coe,mem_domainBits]
      exact ⟨fun hh => hh.2,fun hh => ⟨h hh,hh⟩⟩
    refine Finset.mem_image.mpr ⟨(desc s.1,fun i => desc (s.2 i)),Finset.mem_univ _,?_⟩
    apply Prod.ext (he s.1 hω)
    funext i
    by_cases hi : i ∈ J
    · simp only [encodeFiniteSplice,finiteFieldFamily,dite_eq_left hi,he _ (hη i)]
    · simp only [encodeFiniteSplice,finiteFieldFamily,dite_eq_right hi,hz i hi]

theorem exchangeState_mem_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ)
    (s : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J) (i : ℕ) (hi : i ∈ J) (M : Set E) :
    exchangeState M i s ∈ finiteSpliceDomain Q J := by
  obtain ⟨hω,hη,hz⟩ := (mem_finiteSpliceDomain_iff Q J s).mp hs
  apply (mem_finiteSpliceDomain_iff Q J _).mpr
  refine ⟨exchangeOn_subset M _ _ _ hω (hη i),?_,?_⟩
  · intro l
    by_cases hli : l = i
    · simpa only [hli,exchangeState_at] using exchangeOn_subset M _ _ _ (hη i) hω
    · rw [exchangeState_away _ _ _ _ hli]
      exact hη l
  · intro l hl
    have hli : l ≠ i := by intro he; subst l; exact hl hi
    rw [exchangeState_away _ _ _ _ hli]
    exact hz l hl

theorem runMasks_mem_finiteSpliceDomain (Q : Finset E) (J : Finset ℕ)
    (s : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J) (ms : List (ℕ × Set E))
    (hJ : ∀ q ∈ ms, q.1 ∈ J) : runMasks ms s ∈ finiteSpliceDomain Q J := by
  induction ms generalizing s with
  | nil => exact hs
  | cons q ms ih =>
    apply ih _ (exchangeState_mem_finiteSpliceDomain Q J s hs q.1 (hJ q (by simp)) q.2)
    exact fun q hq => hJ q (by simp [hq])

end FiniteSpliceState

end Percolation

 
open MeasureTheory
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSwitchDensity
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteInverseLoad {I : Type*} [Fintype I]
    (out : I → SpliceState E) (mass : I → ℝ) (t : SpliceState E) : ℝ :=
  ∑ a, if out a = t then mass a else 0

theorem finiteInverseLoad_nonneg {I : Type*} [Fintype I]
    (out : I → SpliceState E) (mass : I → ℝ) (hm : ∀ a, 0 ≤ mass a) (t : SpliceState E) :
    0 ≤ finiteInverseLoad out mass t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hm a
  · exact le_refl 0

 

theorem finiteInverseLoad_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x z : V) (k M : ℕ)
    (L : ℝ) (hL : 1 ≤ L)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (hir : Function.Injective (fun a => (inp a,steps a)))
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (hz : ∀ a, y a k = z) (hfin : ∀ a, (cluster G (out a).1 x).Finite)
    (hgood : ∀ a i, 1 ≤ i → i ≤ k → (cluster G ((inp a).2 i) (y a i)).Finite ∧
      (cluster G ((inp a).2 i) (y a i)).ncard ≤ M ∧ GoodForScale G ((inp a).2 i) (y a i) L)
    (t : SpliceState E) :
    finiteInverseLoad out (fun a => ∏ i : Fin k,
      (traceContactCount G (inp a).2 (y a) (out a).1 x (steps a) (i.val+1):ℝ)⁻¹) t ≤
      inverseCodeMass M L ^ k := by
  let J := {a : I // out a = t}
  have hr (a : J) (i : Fin k) : 0 < traceContactCount G (inp a.val).2 (y a.val)
      (out a.val).1 x (steps a.val) (i.val+1) := by
    have hh := ((htrace a.val).contact_weight_bound G hloc x (inp a.val).2 (y a.val)
      k 0 M (inp a.val).1 (out a.val).1 (steps a.val) (hfin a.val) L hL
      (hgood a.val) (i.val+1)).1
    omega
  have hb := finite_inverse_contact_mass_le G hloc x z k M L hL (0 : unitInterval) ∅
    (fun a : J => inp a.val) (fun a : J => out a.val) (fun a : J => steps a.val)
    (fun a : J => y a.val)
    (fun a b he => Subtype.ext (hir he)) (fun a => htrace a.val) (fun a => hex a.val)
    (fun a => hz a.val) (fun a => hfin a.val) (fun a => hgood a.val)
    (fun _ _ => 0) hr {t} (fun a => by simpa only [Finset.mem_singleton] using a.property)
  simp only [real_volume_contact_choice_cube _ _ (hr _),spliceTupleWeight,domainBits,
    Finset.filter_empty,bernoulliWeight,Finset.card_empty,Nat.sub_self,pow_zero,
    Finset.prod_const_one,mul_one,one_mul,Finset.sum_singleton] at hb
  rw [finiteInverseLoad,← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun a : I => out a = t) _ (by intro a; simp) _]
  exact hb

 

theorem finiteInverseLoad_density {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E) (p : ℝ)
    (inp out : I → SpliceState E) (steps : I → List (ℕ × E)) (y : I → ℕ → V)
    (htrace : ∀ a, SpliceTrace G x (inp a).2 (y a) k 0 (inp a).1 (steps a) (out a).1)
    (hex : ∀ a, SpliceExecution G x (inp a) (steps a) (out a))
    (mass : I → ℝ) (B : Finset (SpliceState E)) (hB : ∀ a, out a ∈ B)
    (f : SpliceState E → ℝ) :
    (∑ a, spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) * mass a * f (out a)) =
      ∑ t ∈ B, spliceTupleWeight Q (Finset.Icc 1 k) p t * finiteInverseLoad out mass t * f t := by
  have hw (a : I) : spliceTupleWeight Q (Finset.Icc 1 k) p (inp a) =
      spliceTupleWeight Q (Finset.Icc 1 k) p (out a) := by
    symm
    apply (hex a).weight G x (inp a) (out a) (steps a) Q (Finset.Icc 1 k) _ p
    intro q hq
    have h := (htrace a).seam_data G x (inp a).2 (y a) k 0 (inp a).1 (out a).1 (steps a) q hq
    exact Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩
  simp only [finiteInverseLoad,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [mul_ite,mul_zero,ite_mul,zero_mul]
  rw [Finset.sum_ite_eq,ite_eq_left (hB a),hw a]

end FiniteSwitchDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteForwardDensity
attribute [local instance] Classical.propDecidable Classical.decEq

 

abbrev FiniteTraceIndex (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :=
  (s : ↥A) × ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)

def traceIndexInput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : SpliceState E := a.1.val

def traceIndexCode (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : List (ℕ × E) := a.2.val

def traceIndexOutput (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : SpliceState E :=
  runMasks (replayMasks G x a.1.val.2 (y a.1.val) a.2.val a.1.val.1) a.1.val

theorem traceIndex_valid (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) :
    SpliceTrace G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 a.2.val
      (traceIndexOutput G x k Q A y a).1 ∧
    SpliceExecution G x a.1.val a.2.val (traceIndexOutput G x k Q A y a) := by
  have ht := ((mem_finiteTraceCodes_iff G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 Q a.2.val).mp
    a.2.property).2
  have hf := ht.runMasks_first G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 _ a.2.val
    a.1.val.2 (by intros; rfl)
  refine ⟨?_,?_⟩
  · simpa only [traceIndexOutput,hf] using ht
  · exact ht.runMasks_execution G x a.1.val.2 (y a.1.val) k 0 a.1.val.1 _ a.2.val
      a.1.val.2 (by intros; rfl)

theorem traceIndex_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteTraceIndex G x k Q A y =>
      (traceIndexInput G x k Q A y a,traceIndexCode G x k Q A y a)) := by
  rintro ⟨a,c⟩ ⟨b,d⟩ he
  have hah : a = b := Subtype.ext (congrArg Prod.fst he)
  subst b
  have hcd : c = d := Subtype.ext (congrArg Prod.snd he)
  subst d
  rfl

theorem traceIndexOutput_mem (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (a : FiniteTraceIndex G x k Q A y) :
    traceIndexOutput G x k Q A y a ∈ finiteSpliceDomain Q (Finset.Icc 1 k) := by
  apply runMasks_mem_finiteSpliceDomain Q (Finset.Icc 1 k) a.1.val (hA a.1.property)
  intro q hq
  have hmap : q.1 ∈ (replayMasks G x a.1.val.2 (y a.1.val) a.2.val a.1.val.1).map Prod.fst :=
    List.mem_map.mpr ⟨q,hq,rfl⟩
  rw [replayMasks_indices] at hmap
  obtain ⟨r,hr,her⟩ := List.mem_map.mp hmap
  have h := (traceIndex_valid G x k Q A y a).1.seam_data G x a.1.val.2 (y a.1.val)
    k 0 a.1.val.1 _ a.2.val r hr
  exact her ▸ Finset.mem_Icc.mpr ⟨h.1,h.2.1⟩

 

noncomputable def traceIndexMass (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (a : FiniteTraceIndex G x k Q A y) : ℝ :=
  ∏ i : Fin k, (traceContactCount G a.1.val.2 (y a.1.val)
    (traceIndexOutput G x k Q A y a).1 x a.2.val (i.val+1):ℝ)⁻¹

noncomputable def finiteForwardLoad (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) (t : SpliceState E) : ℝ :=
  finiteInverseLoad (traceIndexOutput G x k Q A y) (traceIndexMass G x k Q A y) t

 

theorem finiteForwardLoad_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (x z : V) (k M : ℕ) (L : ℝ) (hL : 1 ≤ L) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hz : ∀ s ∈ A, y s k = z)
    (hgood : ∀ s ∈ A, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y s i)).Finite ∧
      (cluster G (s.2 i) (y s i)).ncard ≤ M ∧ GoodForScale G (s.2 i) (y s i) L)
    (t : SpliceState E) :
    0 ≤ finiteForwardLoad G x k Q A y t ∧ finiteForwardLoad G x k Q A y t ≤ inverseCodeMass M L ^ k := by
  constructor
  · exact finiteInverseLoad_nonneg _ _ (by intro a; unfold traceIndexMass; positivity) t
  · apply finiteInverseLoad_le G hloc x z k M L hL
      (traceIndexInput G x k Q A y) (traceIndexOutput G x k Q A y) (traceIndexCode G x k Q A y)
      (fun a => y a.1.val) (traceIndex_injective G x k Q A y)
      (fun a => (traceIndex_valid G x k Q A y a).1)
      (fun a => (traceIndex_valid G x k Q A y a).2) (fun a => hz a.1.val a.1.property)
      _ (fun a => hgood a.1.val a.1.property) t
    intro a
    have hs := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) _).mp
      (traceIndexOutput_mem G x k Q A y hA a)
    exact cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs.1) x

 

theorem finiteForwardLoad_mean [Nonempty E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (k M : ℕ) (Q : Finset E) (p : ℝ)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : ∀ s ∈ A, y s 0 ∈ cluster G s.1 x)
    (hchain : ∀ s ∈ A, ∀ i ∈ Finset.Icc 1 k, Conn G (s.2 i) (y s i) (y s (i-1)))
    (hcaps : ∀ s ∈ A, ∀ i ∈ Finset.Icc 1 k, (cluster G (s.2 i) (y s i)).Finite ∧
      (cluster G (s.2 i) (y s i)).ncard ≤ M) :
    (∑ t ∈ finiteSpliceDomain Q (Finset.Icc 1 k),
      spliceTupleWeight Q (Finset.Icc 1 k) p t * finiteForwardLoad G x k Q A y t) =
      ∑ s ∈ A, spliceTupleWeight Q (Finset.Icc 1 k) p s := by
  have hd := finiteInverseLoad_density G x k Q p
    (traceIndexInput G x k Q A y) (traceIndexOutput G x k Q A y) (traceIndexCode G x k Q A y)
    (fun a => y a.1.val) (fun a => (traceIndex_valid G x k Q A y a).1)
    (fun a => (traceIndex_valid G x k Q A y a).2)
    (traceIndexMass G x k Q A y) (finiteSpliceDomain Q (Finset.Icc 1 k))
    (traceIndexOutput_mem G x k Q A y hA) (fun _ => 1)
  simp only [mul_one] at hd
  unfold finiteForwardLoad
  rw [← hd,Fintype.sum_sigma]
  rw [← Finset.sum_coe_sort A (fun s => spliceTupleWeight Q (Finset.Icc 1 k) p s)]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ c : ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q),
    spliceTupleWeight Q (Finset.Icc 1 k) p s.val * traceIndexMass G x k Q A y ⟨s,c⟩) = _
  rw [← Finset.mul_sum]
  suffices hm : (∑ c : ↥(finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q),
      traceIndexMass G x k Q A y ⟨s,c⟩) = 1 by rw [hm,mul_one]
  have hs := (mem_finiteSpliceDomain_iff Q (Finset.Icc 1 k) s.val).mp (hA s.property)
  have hn := sum_finite_trace_probabilities G hloc x s.val.2 (y s.val) k M Q
    (fun i _ _ => hs.2.1 i) (hchain s.val s.property) (hcaps s.val s.property)
    0 (Nat.zero_le _) s.val.1 (hy s.val s.property)
    (cluster_finite_of_finite_edges G (Q.finite_toSet.subset hs.1) x)
  rw [← Finset.sum_coe_sort (finiteTraceCodes G x s.val.2 (y s.val) k 0 s.val.1 Q)] at hn
  rw [← hn]
  apply Finset.sum_congr rfl
  intro c _
  have ht := ((mem_finiteTraceCodes_iff G x s.val.2 (y s.val) k 0 s.val.1 Q c.val).mp c.property).2
  have hf := ht.runMasks_first G x s.val.2 (y s.val) k 0 s.val.1 _ c.val s.val.2 (by intros; rfl)
  simp only [traceIndexMass,traceIndexOutput,hf]

end FiniteForwardDensity

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ContactIntegratedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_event_mass_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : I → Set Ω)
    (hm : ∀ a, MeasurableSet (P a)) (w : I → ℝ) (B : ℝ)
    (hpoint : ∀ u, (∑ a, if u ∈ P a then w a else 0) ≤ B) :
    (∑ a, w a * μ.real (P a)) ≤ B := by
  let f (a : I) : Ω → ℝ := (P a).indicator (fun _ => w a)
  have hf : ∀ a, Integrable (f a) μ := fun a => (integrable_const _).indicator (hm a)
  have hi := integral_mono (integrable_finsetSum _ (fun a _ => hf a))
    (integrable_const B) (fun u => hpoint u)
  change (∫ u, ∑ a, f a u ∂μ) ≤ (∫ _ : Ω, B ∂μ) at hi
  rw [integral_finsetSum _ (fun a _ => hf a)] at hi
  simpa only [f,integral_indicator_const _ (hm _),smul_eq_mul,mul_comm,
    integral_const,probReal_univ,one_smul,mul_one] using hi

 

theorem finite_separated_contact_second_moment_le {I : Type*} [Fintype I] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₁ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₁ a i) (y₁ (η₁ a) i)).Finite)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) *
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyEvent Q (Finset.Icc 1 k) p (fun η => success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty) *
        finiteFamilyEvent Q (Finset.Icc 1 k) p (fun η => success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty) else 0) := by
  let S := Fin k → unitInterval
  let μ : Measure (S × S) := (volume : Measure S).prod volume
  let P₁ (a : I) : Set S := {u | FollowsContactRule G x (η₁ a) (y₁ (η₁ a))
    (chooseContact (finiteContactSeeds k u)) (c₁ a) (ω₁ a)}
  let P₂ (a : I) : Set S := {u | FollowsContactRule G x (η₂ a) (y₂ (η₂ a))
    (chooseContact (finiteContactSeeds k u)) (c₂ a) (ω₂ a)}
  let w (a : I) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a))
  have hm₁ (a : I) : MeasurableSet (P₁ a) :=
    (h₁ a).measurableSet_seed_event G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a)
  have hm₂ (a : I) : MeasurableSet (P₂ a) :=
    (h₂ a).measurableSet_seed_event G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a)
  have hp (a : I) : μ.real (P₁ a ×ˢ P₂ a) =
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹) := by
    rw [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      (h₁ a).seed_probability G hloc x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) (hcap₁ a),
      (h₂ a).seed_probability G hloc x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) (fun i hi hik => (hcap₂ a i hi hik).1)]
  conv_lhs => arg 2; ext a; rw [mul_assoc,← hp a]
  apply finite_event_mass_le μ (fun a => P₁ a ×ˢ P₂ a) (fun a => (hm₁ a).prod (hm₂ a)) w
  intro u
  let J := {a : I // u ∈ P₁ a ×ˢ P₂ a}
  have hb := finite_separated_second_moment_le G x k n M p Q
    (fun a : J => η₁ a.val) (fun a : J => η₂ a.val) y₁ y₂ success₁ success₂
    (chooseContact (finiteContactSeeds k u.1)) (chooseContact (finiteContactSeeds k u.2))
    (fun a : J => ω₁ a.val) (fun a : J => ω₂ a.val) (fun a : J => ωf a.val)
    (fun a : J => c₁ a.val) (fun a : J => c₂ a.val)
    (fun _ _ he => Subtype.ext (hir he)) (fun a => h₁ a.val) (fun a => h₂ a.val)
    (fun a => hc₁ a.val) (fun a => hc₂ a.val) (fun a => hsep a.val)
    (fun a => a.property.1) (fun a => a.property.2)
    (fun a => hbin a.val) (fun a => hcap₂ a.val) (fun a => hsc₁ a.val) (fun a => hsc₂ a.val)
    (fun a => hsω₁ a.val) (fun a => hsω₂ a.val) (fun a => hsη₁ a.val) (fun a => hsη₂ a.val)
    (fun a => hz₁ a.val) (fun a => hz₂ a.val)
  convert hb using 1
  have he := Finset.sum_subtype (p := fun a => u ∈ P₁ a ×ˢ P₂ a) (F := inferInstance) (Finset.univ.filter (fun a => u ∈ P₁ a ×ˢ P₂ a))
    (by intro a; simp) w
  simpa [Finset.sum_filter,w] using he

end ContactIntegratedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteRootLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteRootLoad (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : SpliceState E → ℝ) (ω : FiniteField Q) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η *
    f (finiteFieldSet Q ω,finiteFieldFamily Q J η)

theorem finiteRootLoad_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : SpliceState E → ℝ) (hf : ∀ s ∈ finiteSpliceDomain Q J, 0 ≤ f s)
    (ω : FiniteField Q) : 0 ≤ finiteRootLoad Q J p f ω := by
  apply Finset.sum_nonneg
  intro η _
  apply mul_nonneg (finiteFamilyWeight_nonneg Q J p η)
  exact hf _ (Finset.mem_image.mpr ⟨(ω,η),Finset.mem_univ _,rfl⟩)

theorem finiteRootLoad_le (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : SpliceState E → ℝ) (C : ℝ)
    (hf : ∀ s ∈ finiteSpliceDomain Q J, f s ≤ C)
    (ω : FiniteField Q) : finiteRootLoad Q J p f ω ≤ C := by
  calc
    _ ≤ ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η * C := by
      apply Finset.sum_le_sum
      intro η _
      apply mul_le_mul_of_nonneg_left _ (finiteFamilyWeight_nonneg Q J p η)
      exact hf _ (Finset.mem_image.mpr ⟨(ω,η),Finset.mem_univ _,rfl⟩)
    _ = C := by rw [← Finset.sum_mul,sum_finiteFamilyWeight,one_mul]

 
theorem finiteRootLoad_mean (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : SpliceState E → ℝ) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω * finiteRootLoad Q J p f ω) =
      ∑ s ∈ finiteSpliceDomain Q J, spliceTupleWeight Q J p s * f s := by
  rw [finiteSpliceDomain,Finset.sum_image (encodeFiniteSplice_injective Q J).injOn,
    Fintype.sum_prod_type]
  simp only [spliceTupleWeight,finiteRootLoad,Finset.mul_sum,encodeFiniteSplice,
    domainBits_finiteFieldSet,prod_fieldFamilyWeight,finiteFieldWeight,mul_assoc]

 

theorem finiteRootLoad_second_moment (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (f₁ f₂ : SpliceState E → ℝ) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J₁ p f₁ ω * finiteRootLoad Q J₂ p f₂ ω) =
    ∑ s : FiniteJointData Q J₁ J₂, jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) *
      f₁ (finiteFieldSet Q s.1,finiteFieldFamily Q J₁ s.2.1) *
      f₂ (finiteFieldSet Q s.1,finiteFieldFamily Q J₂ s.2.2) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  simp only [finiteRootLoad,Finset.mul_sum,Finset.sum_mul,jointTupleWeight_encode]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η₁ _
  apply Finset.sum_congr rfl
  intro η₂ _
  ring

 
theorem finiteForwardRootLoad_bounds (G : BondGraph V E) (hloc : LocallyFinite G)
    (x z : V) (k M : ℕ) (L : ℝ) (hL : 1 ≤ L) (Q : Finset E) (p : unitInterval)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hz : ∀ s ∈ A, y s k = z)
    (hgood : ∀ s ∈ A, ∀ i, 1 ≤ i → i ≤ k → (cluster G (s.2 i) (y s i)).Finite ∧
      (cluster G (s.2 i) (y s i)).ncard ≤ M ∧ GoodForScale G (s.2 i) (y s i) L)
    (ω : FiniteField Q) :
    0 ≤ finiteRootLoad Q (Finset.Icc 1 k) p (finiteForwardLoad G x k Q A y) ω ∧
    finiteRootLoad Q (Finset.Icc 1 k) p (finiteForwardLoad G x k Q A y) ω ≤ inverseCodeMass M L ^ k := by
  have hb := finiteForwardLoad_bounds G hloc x z k M L hL Q A y hA hz hgood
  exact ⟨finiteRootLoad_nonneg _ _ p _ (fun s _ => (hb s).1) _,
    finiteRootLoad_le _ _ p _ _ (fun s _ => (hb s).2) _⟩

 

theorem finiteForwardRootLoad_mean [Nonempty E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (k M : ℕ) (Q : Finset E) (p : ℝ)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V)
    (hA : A ⊆ finiteSpliceDomain Q (Finset.Icc 1 k))
    (hy : ∀ s ∈ A, y s 0 ∈ cluster G s.1 x)
    (hchain : ∀ s ∈ A, ∀ i ∈ Finset.Icc 1 k, Conn G (s.2 i) (y s i) (y s (i-1)))
    (hcaps : ∀ s ∈ A, ∀ i ∈ Finset.Icc 1 k, (cluster G (s.2 i) (y s i)).Finite ∧
      (cluster G (s.2 i) (y s i)).ncard ≤ M) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q (Finset.Icc 1 k) p (finiteForwardLoad G x k Q A y) ω) =
      ∑ s ∈ A, spliceTupleWeight Q (Finset.Icc 1 k) p s := by
  rw [finiteRootLoad_mean]
  exact finiteForwardLoad_mean G hloc x k M Q p A y hA hy hchain hcaps

end FiniteRootLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FinitePairLoad
attribute [local instance] Classical.propDecidable Classical.decEq

 
def pairSpliceOutput (s t : SpliceState E) : JointSpliceState E := (s.1,s.2,t.2)

theorem pairSpliceOutput_mem (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s t : SpliceState E) (hs : s ∈ finiteSpliceDomain Q J₁)
    (ht : t ∈ finiteSpliceDomain Q J₂) :
    pairSpliceOutput s t ∈ finiteJointDomain Q J₁ J₂ := by
  have h₁ := (mem_finiteSpliceDomain_iff Q J₁ s).mp hs
  have h₂ := (mem_finiteSpliceDomain_iff Q J₂ t).mp ht
  exact mem_finiteJointDomain_of_support Q J₁ J₂ _ h₁.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2

 
theorem finiteInverseLoad_mul {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ) (t : JointSpliceState E) :
    finiteInverseLoad out₁ m₁ (t.1,t.2.1) * finiteInverseLoad out₂ m₂ (t.1,t.2.2) =
    ∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 ∧ pairSpliceOutput (out₁ a) (out₂ b) = t
      then m₁ a * m₂ b else 0 := by
  simp only [finiteInverseLoad,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : (out₁ a = (t.1,t.2.1) ∧ out₂ b = (t.1,t.2.2)) ↔
      ((out₁ a).1 = (out₂ b).1 ∧ pairSpliceOutput (out₁ a) (out₂ b) = t) := by
    cases h₁ : out₁ a with | mk r₁ u₁ =>
      cases h₂ : out₂ b with | mk r₂ u₂ =>
        rcases t with ⟨r,u,v⟩
        simpa [pairSpliceOutput,Prod.mk.injEq] using
          (show (r₁ = r ∧ u₁ = u) ∧ (r₂ = r ∧ u₂ = v) ↔
            r₁ = r₂ ∧ r₁ = r ∧ u₁ = u ∧ u₂ = v from by aesop)
  simp only [← he]
  split_ifs <;> simp_all

 

theorem finiteRootLoad_pair_expansion {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]
    (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (out₁ : I₁ → SpliceState E) (out₂ : I₂ → SpliceState E)
    (m₁ : I₁ → ℝ) (m₂ : I₂ → ℝ)
    (hs₁ : ∀ a, out₁ a ∈ finiteSpliceDomain Q J₁)
    (hs₂ : ∀ b, out₂ b ∈ finiteSpliceDomain Q J₂) :
    (∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteRootLoad Q J₁ p (finiteInverseLoad out₁ m₁) ω *
      finiteRootLoad Q J₂ p (finiteInverseLoad out₂ m₂) ω) =
    ∑ a, ∑ b, if (out₁ a).1 = (out₂ b).1 then
      jointTupleWeight Q J₁ J₂ p (pairSpliceOutput (out₁ a) (out₂ b)) * m₁ a * m₂ b else 0 := by
  rw [finiteRootLoad_second_moment]
  have hdom : (∑ s : FiniteJointData Q J₁ J₂,
      jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) *
        finiteInverseLoad out₁ m₁ ((encodeFiniteJoint Q J₁ J₂ s).1,(encodeFiniteJoint Q J₁ J₂ s).2.1) *
        finiteInverseLoad out₂ m₂ ((encodeFiniteJoint Q J₁ J₂ s).1,(encodeFiniteJoint Q J₁ J₂ s).2.2)) =
      ∑ t ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p t *
        finiteInverseLoad out₁ m₁ (t.1,t.2.1) * finiteInverseLoad out₂ m₂ (t.1,t.2.2) := by
    rw [finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn]
  apply hdom.trans
  simp only [mul_assoc,finiteInverseLoad_mul,Finset.mul_sum,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : (out₁ a).1 = (out₂ b).1
  · simp only [he,true_and,ite_true]
    rw [Finset.sum_ite_eq,ite_eq_left (pairSpliceOutput_mem Q J₁ J₂ _ _ (hs₁ a) (hs₂ b))]
  · simp [he]

theorem traceIndex_output_code_injective (G : BondGraph V E) (x : V) (k : ℕ) (Q : Finset E)
    (A : Finset (SpliceState E)) (y : SpliceState E → ℕ → V) :
    Function.Injective (fun a : FiniteTraceIndex G x k Q A y =>
      (traceIndexOutput G x k Q A y a,traceIndexCode G x k Q A y a)) := by
  intro a b he
  have hc : traceIndexCode G x k Q A y a = traceIndexCode G x k Q A y b := congrArg Prod.snd he
  have ho : traceIndexOutput G x k Q A y a = traceIndexOutput G x k Q A y b := congrArg Prod.fst he
  apply traceIndex_injective G x k Q A y
  apply Prod.ext
  · apply SpliceExecution.input_unique G x _ _ _ (traceIndexCode G x k Q A y a)
      (traceIndex_valid G x k Q A y a).2
    change SpliceExecution G x b.1.val (traceIndexCode G x k Q A y a) (traceIndexOutput G x k Q A y a)
    rw [hc,ho]
    exact (traceIndex_valid G x k Q A y b).2
  · exact hc

end FinitePairLoad

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedJointMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem jointRestored_injective {I : Type*}
    (G : BondGraph V E) (x : V) (k : ℕ)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    : Function.Injective (fun a => jointRestored G x (η₁ a) (η₂ a)
      (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)) := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  change Function.Injective rest
  intro a b he
  have hη₁ : η₁ a = η₁ b := congrArg (fun s : JointSpliceState E => s.2.1) he
  have hη₂ : η₂ a = η₂ b := congrArg (fun s : JointSpliceState E => s.2.2) he
  have gb₁ : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ b) (c₁ b) (ωf b) := by
    rw [hη₁]; exact h₁ b
  have gb₂ : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ b) (c₂ b) (ωf b) := by
    rw [hη₂]; exact h₂ b
  have grb₁ : FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ b) (ω₁ b) := by
    rw [hη₁]; exact hr₁ b
  have grb₂ : FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ b) (ω₂ b) := by
    rw [hη₂]; exact hr₂ b
  have hfield : exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ a) (ω₂ a))) (ω₁ a) (ω₂ a) =
      exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ b) (ω₂ b))) (ω₁ b) (ω₂ b) := by
    have hh := congrArg Prod.fst he
    simpa only [rest,jointRestored,← hη₂] using hh
  obtain ⟨hcode₁,hcode₂,hfieldf,haux₁,haux₂⟩ := joint_restore_seeded_unique G x
    (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) choose₁ choose₂ k 0 0
    (ω₁ a) (ω₂ a) (ωf a) (ω₁ b) (ω₂ b) (ωf b)
    (c₁ a) (c₂ a) (c₁ b) (c₂ b) (h₁ a) (h₂ a) gb₁ gb₂
    (hc₁ a) (hc₂ a) (hc₁ b) (hc₂ b) (hsep a) (hsep b)
    (hr₁ a) (hr₂ a) grb₁ grb₂ hfield
  have hout : out a = out b := by
    apply Prod.ext hfieldf
    apply Prod.ext
    · simpa only [out,jointOutput,hη₁] using haux₁
    · simpa only [out,jointOutput,hη₂] using haux₂
  exact hir (Prod.ext hout (Prod.ext hcode₁ hcode₂))

 

theorem finite_joint_weighted_mass_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (B : Finset (JointSpliceState E))
    (hB : ∀ a, jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)) ≤
      ∑ s ∈ B, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s * m₁ s.2.1 * m₂ s.2.2 := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  have hinj : Function.Injective rest := jointRestored_injective G x k η₁ η₂ y₁ y₂ choose₁ choose₂
    ω₁ ω₂ ωf c₁ c₂ hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂
  have hw : ∀ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (out a) =
      jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (rest a) := by
    intro a
    apply (h₁ a).joint_weight G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) k 0 0
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hsep a) Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    · intro q hq
      have hr := (h₁ a).seam_data G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
    · intro q hq
      have hr := (h₂ a).seam_data G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
  change (∑ a, jointTupleWeight Q _ _ p (out a) * m₁ (η₁ a) * m₂ (η₂ a)) ≤ _
  simp_rw [hw]
  change (∑ a, jointTupleWeight Q _ _ p (rest a) * m₁ (rest a).2.1 * m₂ (rest a).2.2) ≤ _
  rw [← Finset.sum_image (f := fun s : JointSpliceState E =>
    jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s * m₁ s.2.1 * m₂ s.2.2) hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    exact hB a
  · intro s _ _
    exact mul_nonneg (mul_nonneg (jointTupleWeight_nonneg Q _ _ p s) (hm₁ _)) (hm₂ _)

end WeightedJointMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteFamilyIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 
noncomputable def finiteFamilyIntegral (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (f : (ℕ → Set E) → ℝ) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η * f (finiteFieldFamily Q J η)

theorem finiteFamilyIntegral_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f : (ℕ → Set E) → ℝ) (hf : ∀ η, 0 ≤ f η) : 0 ≤ finiteFamilyIntegral Q J p f := by
  exact Finset.sum_nonneg fun η _ => mul_nonneg (finiteFamilyWeight_nonneg Q J p η) (hf _)

theorem finiteFamilyIntegral_mono (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (f g : (ℕ → Set E) → ℝ) (hfg : ∀ η, f η ≤ g η) :
    finiteFamilyIntegral Q J p f ≤ finiteFamilyIntegral Q J p g := by
  exact Finset.sum_le_sum fun η _ => mul_le_mul_of_nonneg_left (hfg _) (finiteFamilyWeight_nonneg Q J p η)

theorem finiteFamilyIntegral_const (Q : Finset E) (J : Finset ℕ) (p c : ℝ) :
    finiteFamilyIntegral Q J p (fun _ => c) = c := by
  rw [finiteFamilyIntegral,← Finset.sum_mul,sum_finiteFamilyWeight,one_mul]

theorem finiteFamilyIntegral_sum {I : Type*} (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (S : Finset I) (f : I → (ℕ → Set E) → ℝ) :
    finiteFamilyIntegral Q J p (fun η => ∑ i ∈ S, f i η) =
      ∑ i ∈ S, finiteFamilyIntegral Q J p (f i) := by
  simp only [finiteFamilyIntegral,Finset.mul_sum]
  exact Finset.sum_comm

 
theorem finiteJointDomain_integral_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (f₁ f₂ : Set E → (ℕ → Set E) → ℝ) :
    (∑ s ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p s * f₁ s.1 s.2.1 * f₂ s.1 s.2.2) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      finiteFamilyIntegral Q J₁ p (f₁ (finiteFieldSet Q ω)) *
      finiteFamilyIntegral Q J₂ p (f₂ (finiteFieldSet Q ω)) := by
  rw [finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn]
  simp only [jointTupleWeight_encode]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  simp only [finiteFamilyIntegral,Finset.mul_sum,Finset.sum_mul,encodeFiniteJoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η₂ _
  apply Finset.sum_congr rfl
  intro η₁ _
  ring

theorem finiteJointDomain_weighted_event_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (P : Set E → Prop) (H₁ H₂ : Set E → (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) :
    (∑ s ∈ (finiteJointDomain Q J₁ J₂).filter (fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2),
      jointTupleWeight Q J₁ J₂ p s * m₁ s.2.1 * m₂ s.2.2) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if P (finiteFieldSet Q ω) then
        finiteFamilyIntegral Q J₁ p (fun η => if H₁ (finiteFieldSet Q ω) η then m₁ η else 0) *
        finiteFamilyIntegral Q J₂ p (fun η => if H₂ (finiteFieldSet Q ω) η then m₂ η else 0) else 0) := by
  rw [Finset.sum_filter]
  have he : (∑ s ∈ finiteJointDomain Q J₁ J₂,
      if P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2 then
        jointTupleWeight Q J₁ J₂ p s * m₁ s.2.1 * m₂ s.2.2 else 0) =
    ∑ s ∈ finiteJointDomain Q J₁ J₂, jointTupleWeight Q J₁ J₂ p s *
      (if P s.1 ∧ H₁ s.1 s.2.1 then m₁ s.2.1 else 0) *
      (if H₂ s.1 s.2.2 then m₂ s.2.2 else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp_all
  rw [he,finiteJointDomain_integral_factor Q J₁ J₂ p
    (fun ω η => if P ω ∧ H₁ ω η then m₁ η else 0)
    (fun ω η => if H₂ ω η then m₂ η else 0)]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hP : P (finiteFieldSet Q ω)
  · simp only [hP,true_and,ite_true,mul_assoc]
  · simp [hP,finiteFamilyIntegral]

end FiniteFamilyIntegral

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedSeparatedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_weighted_second_moment_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let J := Finset.Icc 1 k
  let P (ω : Set E) := (cluster G ω x).Finite ∧ n-k*M ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n
  let H₁ (ω : Set E) (η : ℕ → Set E) := success₁ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₁ η) k).Nonempty
  let H₂ (ω : Set E) (η : ℕ → Set E) := success₂ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₂ η) k).Nonempty
  let B := (finiteJointDomain Q J J).filter fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2
  have hB (a : I) : jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_finiteJointDomain_of_support Q J J _
      (exchangeOn_subset _ _ _ _ (hsω₁ a) (hsω₂ a)) (hsη₁ a) (hsη₂ a) (hz₁ a) (hz₂ a),?_⟩
    have hroot := (h₁ a).joint_restored_size G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 n M (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
      (hbin a).1 (hbin a).2.1 (hbin a).2.2 (hcap₂ a)
    have hhits := (h₁ a).joint_trajectory_hits G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
    exact ⟨hroot,⟨hsc₁ a,hhits.1⟩,hsc₂ a,hhits.2⟩
  have h := finite_joint_weighted_mass_le G x k p Q η₁ η₂ y₁ y₂ choose₁ choose₂ ω₁ ω₂ ωf c₁ c₂
    hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂ m₁ m₂ hm₁ hm₂ B hB
  apply h.trans_eq
  convert finiteJointDomain_weighted_event_factor Q J J p P H₁ H₂ m₁ m₂ using 1 <;>
    simp only [B, J, P, H₁, H₂]
  apply Finset.sum_congr rfl
  intro ω _
  apply congrArg (fun z : ℝ => finiteFieldWeight Q p ω * z)
  split_ifs
  · apply congrArg₂ (· * ·)
    · apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      split_ifs <;> rfl
    · apply congrArg (finiteFamilyIntegral Q (Finset.Icc 1 k) p)
      funext η
      split_ifs <;> rfl
  · rfl

end WeightedSeparatedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedContactSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_weighted_contact_second_moment_le {I : Type*} [Fintype I] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (m₁ m₂ : (ℕ → Set E) → ℝ) (hm₁ : ∀ η, 0 ≤ m₁ η) (hm₂ : ∀ η, 0 ≤ m₂ η)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₁ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₁ a i) (y₁ (η₁ a) i)).Finite)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a) *
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹)) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty then m₁ η else 0) *
        finiteFamilyIntegral Q (Finset.Icc 1 k) p (fun η => if success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty then m₂ η else 0) else 0) := by
  let S := Fin k → unitInterval
  let μ : Measure (S × S) := (volume : Measure S).prod volume
  let P₁ (a : I) : Set S := {u | FollowsContactRule G x (η₁ a) (y₁ (η₁ a))
    (chooseContact (finiteContactSeeds k u)) (c₁ a) (ω₁ a)}
  let P₂ (a : I) : Set S := {u | FollowsContactRule G x (η₂ a) (y₂ (η₂ a))
    (chooseContact (finiteContactSeeds k u)) (c₂ a) (ω₂ a)}
  let w (a : I) := jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)) * m₁ (η₁ a) * m₂ (η₂ a)
  have hmeas₁ (a : I) : MeasurableSet (P₁ a) :=
    (h₁ a).measurableSet_seed_event G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a)
  have hmeas₂ (a : I) : MeasurableSet (P₂ a) :=
    (h₂ a).measurableSet_seed_event G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a)
  have hp (a : I) : μ.real (P₁ a ×ˢ P₂ a) =
      (∏ i : Fin k, (traceContactCount G (η₁ a) (y₁ (η₁ a)) (ωf a) x (c₁ a) (i.val+1):ℝ)⁻¹) *
      (∏ i : Fin k, (traceContactCount G (η₂ a) (y₂ (η₂ a)) (ωf a) x (c₂ a) (i.val+1):ℝ)⁻¹) := by
    rw [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul,
      (h₁ a).seed_probability G hloc x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) (hcap₁ a),
      (h₂ a).seed_probability G hloc x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) (fun i hi hik => (hcap₂ a i hi hik).1)]
  conv_lhs => arg 2; ext a; rw [mul_assoc,← hp a]
  apply finite_event_mass_le μ (fun a => P₁ a ×ˢ P₂ a) (fun a => (hmeas₁ a).prod (hmeas₂ a)) w
  intro u
  let J := {a : I // u ∈ P₁ a ×ˢ P₂ a}
  have hb := finite_separated_weighted_second_moment_le G x k n M p Q
    (fun a : J => η₁ a.val) (fun a : J => η₂ a.val) y₁ y₂ success₁ success₂ m₁ m₂ hm₁ hm₂
    (chooseContact (finiteContactSeeds k u.1)) (chooseContact (finiteContactSeeds k u.2))
    (fun a : J => ω₁ a.val) (fun a : J => ω₂ a.val) (fun a : J => ωf a.val)
    (fun a : J => c₁ a.val) (fun a : J => c₂ a.val)
    (fun _ _ he => Subtype.ext (hir he)) (fun a => h₁ a.val) (fun a => h₂ a.val)
    (fun a => hc₁ a.val) (fun a => hc₂ a.val) (fun a => hsep a.val)
    (fun a => a.property.1) (fun a => a.property.2)
    (fun a => hbin a.val) (fun a => hcap₂ a.val) (fun a => hsc₁ a.val) (fun a => hsc₂ a.val)
    (fun a => hsω₁ a.val) (fun a => hsω₂ a.val) (fun a => hsη₁ a.val) (fun a => hsη₂ a.val)
    (fun a => hz₁ a.val) (fun a => hz₂ a.val)
  convert hb using 1
  have he := Finset.sum_subtype (p := fun a => u ∈ P₁ a ×ˢ P₂ a) (F := inferInstance) (Finset.univ.filter (fun a => u ∈ P₁ a ×ˢ P₂ a))
    (by intro a; simp) w
  simpa [Finset.sum_filter,w] using he

end WeightedContactSecondMoment

end Percolation

end OAI
