import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TierClamp

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

noncomputable def relationDestinations (R : Ω → Ω → Prop) (a : Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun b => a ≠ b ∧ R a b)

noncomputable def relationOff (R : Ω → Ω → Prop) (d : ℕ) (a b : Ω) : ℝ := by
  classical
  exact if b ∈ relationDestinations R a then (d:ℝ)⁻¹ else 0

noncomputable def relationProposal (R : Ω → Ω → Prop) (d : ℕ) (a b : Ω) : ℝ := by
  classical
  exact if a = b then 1-∑ z, relationOff R d a z else relationOff R d a b

lemma relationOff_self (R : Ω → Ω → Prop) (d : ℕ) (a : Ω) : relationOff R d a a = 0 := by
  classical
  simp [relationOff,relationDestinations]

lemma relationOff_nonneg (R : Ω → Ω → Prop) (d : ℕ) (a b : Ω) : 0 ≤ relationOff R d a b := by
  classical
  unfold relationOff; split_ifs <;> positivity

lemma relationOff_sum (R : Ω → Ω → Prop) (d : ℕ) (a : Ω) :
    (∑ b, relationOff R d a b) = (relationDestinations R a).card / (d:ℝ) := by
  classical
  unfold relationOff
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

lemma relationOff_sum_le_one (R : Ω → Ω → Prop) (d : ℕ) (a : Ω)
    (hd : (relationDestinations R a).card ≤ d) : (∑ b, relationOff R d a b) ≤ 1 := by
  rw [relationOff_sum]
  by_cases h : d = 0
  · simp [h]
  · apply (div_le_one (by positivity)).mpr
    exact_mod_cast hd

lemma relationProposal_nonneg (R : Ω → Ω → Prop) (d : ℕ)
    (hd : ∀ a, (relationDestinations R a).card ≤ d) (a b : Ω) : 0 ≤ relationProposal R d a b := by
  classical
  unfold relationProposal; split_ifs
  · exact sub_nonneg.mpr (relationOff_sum_le_one R d a (hd a))
  · exact relationOff_nonneg _ _ _ _

lemma relationProposal_row (R : Ω → Ω → Prop) (d : ℕ) (a : Ω) :
    (∑ b, relationProposal R d a b) = 1 := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
  have hh : (∑ b ∈ Finset.univ.erase a, relationProposal R d a b) =
      ∑ b, relationOff R d a b := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),relationOff_self,add_zero]
    apply Finset.sum_congr rfl; intro b hb
    simp only [relationProposal,ite_eq_right (Finset.ne_of_mem_erase hb).symm]
  rw [hh]
  simp only [relationProposal,ite_true]
  ring

lemma relationProposal_symmetric (R : Ω → Ω → Prop) (d : ℕ)
    (hR : ∀ a b, R a b ↔ R b a) (a b : Ω) : relationProposal R d a b = relationProposal R d b a := by
  classical
  by_cases h : a = b
  · subst b; rfl
  · simp [relationProposal,h,Ne.symm h,relationOff,relationDestinations,hR a b]

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def colorProposal (A B : PM (fun e v => v ∈ ends e)) : ℝ :=
  relationProposal (ColorChange ends) (Fintype.card V) A B

omit [DecidableEq V] in
lemma colorProposal_row (A : PM (fun e v => v ∈ ends e)) : (∑ B, colorProposal ends A B) = 1 :=
  relationProposal_row _ _ _

omit [DecidableEq V] in
lemma colorProposal_symmetric (A B : PM (fun e v => v ∈ ends e)) :
    colorProposal ends A B = colorProposal ends B A :=
  relationProposal_symmetric _ _ (fun _ _ => ⟨ColorChange.symm ends,ColorChange.symm ends⟩) A B

lemma colorProposal_nonneg (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) : 0 ≤ colorProposal ends A B := by
  classical
  apply relationProposal_nonneg
  intro C
  calc
    _ ≤ (colorDestinations ends C).card := Finset.card_le_card (by
      intro D hD; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hD).2).2⟩)
    _ ≤ 2*C.val.card := colorDestinations_card_bound ends hpar C
    _ = _ := C.twice_card ends hloop

lemma colorProposal_off (hloop : ∀ e, ¬(ends e).IsDiag)
    (A B : PM (fun e v => v ∈ ends e)) (h : A ≠ B) :
    colorProposal ends A B = if ColorChange ends A B then (2*(A.val.card:ℝ))⁻¹ else 0 := by
  classical
  have hn : (Fintype.card V:ℝ) = 2*(A.val.card:ℝ) := by exact_mod_cast (A.twice_card ends hloop).symm
  simp [colorProposal,relationProposal,relationOff,relationDestinations,h,hn]

theorem colorProposal_dirichlet (hloop : ∀ e, ¬(ends e).IsDiag)
    (w : E → ℝ) (f : Finset E → ℝ) :
    (∑ A : PM (fun e v => v ∈ ends e), ∑ B : PM (fun e v => v ∈ ends e),
      min (gibbs w A) (gibbs w B)*colorProposal ends A B*(f A.val-f B.val)^2) / 6 =
      colorDirichlet ends w f := by
  classical
  unfold colorDirichlet
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro A _
  rw [Finset.sum_div]
  unfold colorDestinations
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro B _
  by_cases h : A = B
  · subst B; simp
  · rw [colorProposal_off ends hloop A B h]
    by_cases hc : ColorChange ends A B
    · rw [ite_eq_left hc,ite_eq_left hc]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp [hc]

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] in
lemma TwoEdgeSwitch.symm {A B : PM inc} (h : TwoEdgeSwitch A B) : TwoEdgeSwitch B A := by
  obtain ⟨v,e,R,hv,he,hA,hB⟩ := h
  refine ⟨(fun i => v (i+1)),(fun i => e (i+1)),R,?_,?_,?_,?_⟩
  · exact hv.comp (fun _ _ h => add_right_cancel h)
  · intro i x
    simpa only [add_assoc] using he (i+1) x
  · simpa using hB
  · simpa [Finset.pair_comm] using hA

omit [DecidableEq V] [Fintype E] in
lemma TwoEdgeSwitch.normal_form {A B : PM inc} (h : TwoEdgeSwitch A B) :
    ∃ (v : Fin 4 → V) (e : Fin 4 → E), Function.Injective v ∧
      (∀ i x, inc (e i) x ↔ x = v i ∨ x = v (i+1)) ∧
      e 0 ≠ e 2 ∧ {e 0,e 2} ⊆ A.val ∧
      B.val = (A.val \ {e 0,e 2}) ∪ {e 1,e 3} := by
  classical
  obtain ⟨v,e,R,hv,he,hA,hB⟩ := h
  have hne (i j : Fin 4) (hij : i ≠ j) (hij' : i ≠ j+1) : e i ≠ e j := by
    intro h
    have hi := (he i (v i)).mpr (Or.inl rfl)
    rw [h] at hi
    rcases (he j (v i)).mp hi with h | h
    · exact hij (hv h)
    · exact hij' (hv h)
  have h01 : e 0 ≠ e 1 := hne 0 1 (by decide) (by decide)
  have h23 : e 2 ≠ e 3 := hne 2 3 (by decide) (by decide)
  have h02 : e 0 ≠ e 2 := hne 0 2 (by decide) (by decide)
  have hRB : R ⊆ B.val := by rw [hB]; exact Finset.subset_union_left
  have hb1 : e 1 ∈ B.val := by rw [hB]; simp
  have hb3 : e 3 ∈ B.val := by rw [hB]; simp
  have hr0 : e 0 ∉ R := by
    intro hr
    exact h01 (B.property.unique (Finset.mem_univ (v 1)) (hRB hr)
      ((he 0 (v 1)).mpr (Or.inr rfl)) hb1 ((he 1 (v 1)).mpr (Or.inl rfl)))
  have hr2 : e 2 ∉ R := by
    intro hr
    exact h23 (B.property.unique (Finset.mem_univ (v 3)) (hRB hr)
      ((he 2 (v 3)).mpr (Or.inr rfl)) hb3 ((he 3 (v 3)).mpr (Or.inl rfl)))
  have hR : A.val \ {e 0,e 2} = R := by
    rw [hA]
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · tauto
    · intro ha
      exact ⟨Or.inl ha,by rintro (rfl|rfl) <;> contradiction⟩
  exact ⟨v,e,hv,he,h02,by rw [hA]; exact Finset.subset_union_right,by rw [hR]; exact hB⟩

variable (ends : E → Sym2 V)

noncomputable def edgeEndpoints (e : E) : V × V :=
  Classical.choose (show ∃ p : V × V, ends e = s(p.1,p.2) from
    Sym2.inductionOn (ends e) (fun a b => ⟨(a,b),rfl⟩))

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma edgeEndpoints_spec (e : E) : ends e = s((edgeEndpoints ends e).1,(edgeEndpoints ends e).2) :=
  Classical.choose_spec (show ∃ p : V × V, ends e = s(p.1,p.2) from
    Sym2.inductionOn (ends e) (fun a b => ⟨(a,b),rfl⟩))

noncomputable def pairRep (I : Finset E) (h : I.card = 2) : E × E :=
  Classical.choose (show ∃ p : E × E, p.1 ≠ p.2 ∧ I = {p.1,p.2} from by
    obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp h
    exact ⟨(a,b),hab,he⟩)

omit [Fintype E] in
lemma pairRep_spec (I : Finset E) (h : I.card = 2) :
    (pairRep I h).1 ≠ (pairRep I h).2 ∧ I = {(pairRep I h).1,(pairRep I h).2} :=
  Classical.choose_spec (show ∃ p : E × E, p.1 ≠ p.2 ∧ I = {p.1,p.2} from by
    obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp h
    exact ⟨(a,b),hab,he⟩)

noncomputable def withEnds (a b : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ends e = s(a,b))

omit [Fintype V] [DecidableEq E] in
lemma mem_withEnds (a b : V) (e : E) : e ∈ withEnds ends a b ↔ ends e = s(a,b) := by
  classical
  simp [withEnds]

omit [Fintype V] [DecidableEq E] in
lemma withEnds_card_le (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (a b : V) : (withEnds ends a b).card ≤ 2 := by
  classical
  by_cases h : (withEnds ends a b).Nonempty
  · obtain ⟨e,he⟩ := h
    have hh : withEnds ends a b = Finset.univ.filter (fun f => ends f = ends e) := by
      unfold withEnds
      rw [(mem_withEnds ends a b e).mp he]
    rw [hh]; exact hpar e
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

noncomputable def edgePairOptions (R : Finset E) (a b c d : V) : Finset (Finset E) := by
  classical
  exact (withEnds ends a b).biUnion fun e =>
    (withEnds ends c d).image fun f => R ∪ {e,f}

omit [Fintype V] in
lemma mem_edgePairOptions (R : Finset E) (a b c d : V) (e f : E)
    (he : ends e = s(a,b)) (hf : ends f = s(c,d)) :
    R ∪ {e,f} ∈ edgePairOptions ends R a b c d := by
  classical
  exact Finset.mem_biUnion.mpr ⟨e,(mem_withEnds ends a b e).mpr he,
    Finset.mem_image.mpr ⟨f,(mem_withEnds ends c d f).mpr hf,rfl⟩⟩

omit [Fintype V] in
lemma edgePairOptions_card_le
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (R : Finset E) (a b c d : V) : (edgePairOptions ends R a b c d).card ≤ 4 := by
  classical
  calc
    _ ≤ ∑ e ∈ withEnds ends a b, ((withEnds ends c d).image (fun f => R ∪ {e,f})).card := Finset.card_biUnion_le
    _ ≤ ∑ e ∈ withEnds ends a b, 2 := Finset.sum_le_sum (fun _ _ =>
      Finset.card_image_le.trans (withEnds_card_le ends hpar c d))
    _ ≤ 4 := by simp only [Finset.sum_const,smul_eq_mul]; have := withEnds_card_le ends hpar a b; omega

noncomputable def switchOptions (A : Finset E) (I : Finset E) : Finset (Finset E) := by
  classical
  exact if h : I.card = 2 then
    let p := pairRep I h
    let u := edgeEndpoints ends p.1
    let v := edgeEndpoints ends p.2
    edgePairOptions ends (A\I) u.1 v.1 u.2 v.2 ∪
      edgePairOptions ends (A\I) u.1 v.2 u.2 v.1
  else ∅

omit [Fintype V] in
lemma switchOptions_card_le
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A I : Finset E) : (switchOptions ends A I).card ≤ 8 := by
  classical
  unfold switchOptions
  split_ifs with h
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (edgePairOptions_card_le ends hpar _ _ _ _ _) (edgePairOptions_card_le ends hpar _ _ _ _ _))
  · simp

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [Fintype V] in
lemma mem_pairOptions_of_endpoints (R : Finset E) (p q f g : E) (a b c d : V)
    (hp : ends p = s(a,b)) (hq : ends q = s(c,d))
    (hf : ends f = s(b,c)) (hg : ends g = s(d,a)) :
    R ∪ {f,g} ∈
      edgePairOptions ends R (edgeEndpoints ends p).1 (edgeEndpoints ends q).1
        (edgeEndpoints ends p).2 (edgeEndpoints ends q).2 ∪
      edgePairOptions ends R (edgeEndpoints ends p).1 (edgeEndpoints ends q).2
        (edgeEndpoints ends p).2 (edgeEndpoints ends q).1 := by
  classical
  have hu := Sym2.eq_iff.mp ((edgeEndpoints_spec ends p).symm.trans hp)
  have hv := Sym2.eq_iff.mp ((edgeEndpoints_spec ends q).symm.trans hq)
  rcases hu with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases hv with ⟨h3,h4⟩ | ⟨h3,h4⟩
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_right
    rw [Finset.pair_comm f g]
    exact mem_edgePairOptions ends R a d b c g f (hg.trans (Sym2.eq_swap)) hf
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_left
    rw [Finset.pair_comm f g]
    exact mem_edgePairOptions ends R a d b c g f (hg.trans (Sym2.eq_swap)) hf
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_left
    exact mem_edgePairOptions ends R b c a d f g hf (hg.trans (Sym2.eq_swap))
  · rw [h1,h2,h3,h4]
    apply Finset.mem_union_right
    exact mem_edgePairOptions ends R b c a d f g hf (hg.trans (Sym2.eq_swap))

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma inc_eq_ends (e : E) (a b : V) (hab : a ≠ b)
    (h : ∀ x, x ∈ ends e ↔ x = a ∨ x = b) : ends e = s(a,b) := by
  exact (Sym2.mem_and_mem_iff hab).mp ⟨(h a).mpr (Or.inl rfl),(h b).mpr (Or.inr rfl)⟩

lemma switch_mem_options {A B : PM (fun e v => v ∈ ends e)} (h : TwoEdgeSwitch A B) :
    ∃ I ∈ A.val.powersetCard 2, B.val ∈ switchOptions ends A.val I := by
  classical
  obtain ⟨v,e,hv,he,h02,hsub,hB⟩ := h.normal_form
  let I : Finset E := {e 0,e 2}
  have hI : I.card = 2 := by simp [I,h02]
  refine ⟨I,Finset.mem_powersetCard.mpr ⟨hsub,hI⟩,?_⟩
  have hend (i : Fin 4) : ends (e i) = s(v i,v (i+1)) :=
    inc_eq_ends ends (e i) (v i) (v (i+1))
      (fun h => (by omega : i ≠ i+1) (hv h)) (he i)
  unfold switchOptions
  rw [dite_eq_left hI]
  dsimp only
  obtain ⟨hne,hr⟩ := pairRep_spec I hI
  have h1 : (pairRep I hI).1 = e 0 ∨ (pairRep I hI).1 = e 2 := by
    have : (pairRep I hI).1 ∈ I := by
      exact (congrArg (fun S : Finset E => (pairRep I hI).1 ∈ S) hr).mpr (by simp)
    simpa [I] using this
  have h2 : (pairRep I hI).2 = e 0 ∨ (pairRep I hI).2 = e 2 := by
    have : (pairRep I hI).2 ∈ I := by
      exact (congrArg (fun S : Finset E => (pairRep I hI).2 ∈ S) hr).mpr (by simp)
    simpa [I] using this
  rw [hB]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact False.elim (hne (h1.trans h2.symm))
  · rw [h1,h2]
    exact mem_pairOptions_of_endpoints ends (A.val\I) (e 0) (e 2) (e 1) (e 3)
      (v 0) (v 1) (v 2) (v 3) (hend 0) (hend 2) (hend 1) (hend 3)
  · rw [h1,h2,Finset.pair_comm (e 1) (e 3)]
    exact mem_pairOptions_of_endpoints ends (A.val\I) (e 2) (e 0) (e 3) (e 1)
      (v 2) (v 3) (v 0) (v 1) (hend 2) (hend 0) (hend 3) (hend 1)
  · exact False.elim (hne (h1.trans h2.symm))

lemma switchDestinations_card_bound
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A : PM (fun e v => v ∈ ends e)) :
    (switchDestinations A).card ≤ 8 * A.val.card.choose 2 := by
  classical
  have hsub : (switchDestinations A).image Subtype.val ⊆
      (A.val.powersetCard 2).biUnion (switchOptions ends A.val) := by
    intro B hB
    obtain ⟨C,hC,hCB⟩ := Finset.mem_image.mp hB
    rw [← hCB]
    obtain ⟨I,hI,hB⟩ := switch_mem_options ends ((Finset.mem_filter.mp hC).2)
    exact Finset.mem_biUnion.mpr ⟨I,hI,hB⟩
  calc
    _ = ((switchDestinations A).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ((A.val.powersetCard 2).biUnion (switchOptions ends A.val)).card := Finset.card_le_card hsub
    _ ≤ ∑ I ∈ A.val.powersetCard 2, (switchOptions ends A.val I).card := Finset.card_biUnion_le
    _ ≤ ∑ I ∈ A.val.powersetCard 2, 8 :=
      Finset.sum_le_sum fun I _ => switchOptions_card_le ends hpar A.val I
    _ = _ := by simp [Nat.mul_comm]

end

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

noncomputable def switchProposal (A B : PM (fun e v => v ∈ ends e)) : ℝ :=
  relationProposal TwoEdgeSwitch (8*(Fintype.card V/2).choose 2) A B

omit [DecidableEq V] in
lemma switchProposal_row (A : PM (fun e v => v ∈ ends e)) : (∑ B, switchProposal ends A B) = 1 :=
  relationProposal_row _ _ _

omit [DecidableEq V] in
lemma switchProposal_symmetric (A B : PM (fun e v => v ∈ ends e)) :
    switchProposal ends A B = switchProposal ends B A :=
  relationProposal_symmetric _ _ (fun _ _ => ⟨TwoEdgeSwitch.symm,TwoEdgeSwitch.symm⟩) A B

lemma switchProposal_nonneg (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) : 0 ≤ switchProposal ends A B := by
  classical
  apply relationProposal_nonneg
  intro C
  have hn : Fintype.card V/2 = C.val.card := by have := C.twice_card ends hloop; omega
  calc
    _ ≤ (switchDestinations C).card := Finset.card_le_card (by
      intro D hD; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_filter.mp hD).2).2⟩)
    _ ≤ 8*C.val.card.choose 2 := switchDestinations_card_bound ends hpar C
    _ = _ := by rw [hn]

lemma switchProposal_off (hloop : ∀ e, ¬(ends e).IsDiag)
    (A B : PM (fun e v => v ∈ ends e)) (h : A ≠ B) :
    switchProposal ends A B = if TwoEdgeSwitch A B then (8*(A.val.card.choose 2:ℝ))⁻¹ else 0 := by
  have hn : Fintype.card V/2 = A.val.card := by have := A.twice_card ends hloop; omega
  simp [switchProposal,relationProposal,relationOff,relationDestinations,h,hn]

theorem switchProposal_dirichlet (hloop : ∀ e, ¬(ends e).IsDiag)
    (w : E → ℝ) (f : Finset E → ℝ) :
    (∑ A : PM (fun e v => v ∈ ends e), ∑ B : PM (fun e v => v ∈ ends e),
      min (gibbs w A) (gibbs w B)*switchProposal ends A B*(f A.val-f B.val)^2) / 6 =
      switchDirichlet (inc := fun e v => v ∈ ends e) w f := by
  classical
  unfold switchDirichlet
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro A _
  rw [Finset.sum_div]
  unfold switchDestinations
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro B _
  by_cases h : A = B
  · subst B; simp
  · rw [switchProposal_off ends hloop A B h]
    by_cases hc : TwoEdgeSwitch A B
    · rw [ite_eq_left hc,ite_eq_left hc]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp [hc]

end MatchingFPRAS.Transport

end OAI
