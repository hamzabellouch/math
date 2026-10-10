import OAI.Combinatorics.Sidorenko.Exposure

namespace OAI

namespace SidorenkoCounterexample
open Module

section Span
variable {K V P : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype P] [DecidableEq P]

/-- The span of the spaces on the edges incident to a given vertex. -/
def localSpan (s : Finset (Finset P)) (H : Finset P → Submodule K V) (i : P) :
    Submodule K V := (s.filter fun e => i ∈ e).sup H

omit [FiniteDimensional K V] [Fintype P] in
private theorem localSpan_le (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (i : P) : localSpan s H i ≤ s.sup H :=
  Finset.sup_mono (Finset.filter_subset _ _)

omit [FiniteDimensional K V] [Fintype P] in
private theorem localSpan_insert (s : Finset (Finset P)) (e : Finset P)
    (H : Finset P → Submodule K V) (i : P) :
    localSpan (insert e s) H i = if i ∈ e then H e ⊔ localSpan s H i
      else localSpan s H i := by
  classical
  simp only [localSpan, Finset.filter_insert]
  split_ifs <;> simp

private theorem local_rank_insert (s : Finset (Finset P)) (e : Finset P)
    (H : Finset P → Submodule K V) :
    (∑ i, finrank K (localSpan (insert e s) H i)) +
      (∑ i ∈ e, finrank K (H e ⊓ localSpan s H i : Submodule K V)) =
    (∑ i, finrank K (localSpan s H i)) + e.card * finrank K (H e) := by
  classical
  have heq (i : P) : finrank K (localSpan (insert e s) H i) +
      (if i ∈ e then finrank K (H e ⊓ localSpan s H i : Submodule K V) else 0) =
      finrank K (localSpan s H i) + (if i ∈ e then finrank K (H e) else 0) := by
    by_cases hi : i ∈ e
    · rw [localSpan_insert, ite_eq_left hi, ite_eq_left hi, ite_eq_left hi]
      exact (Submodule.finrank_sup_add_finrank_inf_eq (H e) (localSpan s H i)).trans (Nat.add_comm _ _)
    · rw [localSpan_insert, ite_eq_right hi, ite_eq_right hi, ite_eq_right hi]
  have h := congrArg (fun f : P → ℕ => ∑ i, f i) (funext heq)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const,
    smul_eq_mul, Finset.univ_inter] using h

/-- The dimension bound, together with its equality rigidity. Equality
forces the entire edge-space family to be a direct sum. -/
theorem span_inequality_with_rigidity (s : Finset (Finset P))
    (H : Finset P → Submodule K V) (hs : ∀ e ∈ s, e.card = 2) :
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) ∧
    ((∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) →
      s.SupIndep H) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    constructor
    · simp
    · intro _
      exact Finset.supIndep_empty H
  | @insert e s he ih =>
    have hse : ∀ f ∈ s, f.card = 2 := fun f hf => hs f (Finset.mem_insert_of_mem hf)
    obtain ⟨hbound, hrigid⟩ := ih hse
    have hecard := hs e (Finset.mem_insert_self _ _)
    obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp hecard
    have hr := local_rank_insert s e H
    rw [hecard, heab] at hr
    simp only [Finset.sum_pair hab] at hr
    rw [← heab] at hr
    have hg := Submodule.finrank_sup_add_finrank_inf_eq (H e) (s.sup H)
    have hda := Submodule.finrank_mono
      (inf_le_inf_left (H e) (localSpan_le s H a))
    have hdb := Submodule.finrank_mono
      (inf_le_inf_left (H e) (localSpan_le s H b))
    rw [Finset.sup_insert]
    constructor
    · omega
    · intro heq
      have hold : (∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) := by omega
      have hA : finrank K (H e ⊓ localSpan s H a : Submodule K V) =
          finrank K (H e ⊓ s.sup H : Submodule K V) := by omega
      have hB : finrank K (H e ⊓ localSpan s H b : Submodule K V) =
          finrank K (H e ⊓ s.sup H : Submodule K V) := by omega
      have hind := hrigid hold
      have hfilters : Disjoint (s.filter fun f => a ∈ f) (s.filter fun f => b ∈ f) := by
        rw [Finset.disjoint_left]
        intro f hfa hfb
        obtain ⟨hf, haf⟩ := Finset.mem_filter.mp hfa
        have hbf := (Finset.mem_filter.mp hfb).2
        have hef : e ⊆ f := by
          rw [heab]
          intro x hx
          rcases Finset.mem_insert.mp hx with hxa | hxb
          · exact hxa ▸ haf
          · exact (Finset.mem_singleton.mp hxb) ▸ hbf
        have heqf : e = f := Finset.eq_of_subset_of_card_le hef (by rw [hse f hf, hecard])
        exact he (heqf.symm ▸ hf)
      have hdis : Disjoint (localSpan s H a) (localSpan s H b) :=
        hind.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _) hfilters
      have hAe := Submodule.eq_of_le_of_finrank_eq
        (inf_le_inf_left (H e) (localSpan_le s H a)) hA
      have hBe := Submodule.eq_of_le_of_finrank_eq
        (inf_le_inf_left (H e) (localSpan_le s H b)) hB
      have hnew : Disjoint (H e) (s.sup H) := by
        rw [disjoint_iff_inf_le]
        calc
          H e ⊓ s.sup H ≤ localSpan s H a ⊓ localSpan s H b := by
            exact le_inf (hAe ▸ inf_le_right) (hBe ▸ inf_le_right)
          _ ≤ ⊥ := hdis.le_bot
      exact hind.insert hnew

/-- Exact non-strict span inequality of the manuscript. -/
theorem span_inequality (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (hs : ∀ e ∈ s, e.card = 2) :
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) :=
  (span_inequality_with_rigidity s H hs).1

/-- Exact strict improvement for a nondirect family, including partial
intersections. Zero spaces do not affect `SupIndep`. -/
theorem strict_span_inequality (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (hs : ∀ e ∈ s, e.card = 2) (hn : ¬s.SupIndep H) :
    2 * finrank K (s.sup H : Submodule K V) + 1 ≤ ∑ i, finrank K (localSpan s H i) := by
  obtain ⟨hb, hr⟩ := span_inequality_with_rigidity s H hs
  have hne : (∑ i, finrank K (localSpan s H i)) ≠ 2 * finrank K (s.sup H : Submodule K V) :=
    fun h => hn (hr h)
  omega

end Span
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FiniteSpans
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
 theorem finrank_finset_sup_le (s : Finset I) (A : I → Submodule K E) :
    finrank K ↥(s.sup A) ≤ ∑ i∈s, finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    have := Submodule.finrank_sup_add_finrank_inf_eq (A i) (s.sup A)
    omega
 theorem finrank_finite_iSup_le [Fintype I] (A : I → Submodule K E) :
    finrank K ↥(⨆ i,A i) ≤ ∑ i, finrank K (A i) := by
  have hh := finrank_finset_sup_le Finset.univ A
  exact (le_of_eq (congrArg (fun S : Submodule K E=>finrank K S)
    (Finset.sup_univ_eq_iSup A).symm)).trans hh
 theorem finrank_finset_sup_direct (s : Finset I) (A : I → Submodule K E)
    (ha : iSupIndep A) : finrank K ↥(s.sup A) = ∑ i∈s, finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd : Disjoint (A i) (s.sup A) := by
      rw [Finset.sup_eq_iSup]
      exact ha.disjoint_biSup hi
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (A i) (s.sup A)
    rw [hd.eq_bot,finrank_bot,add_zero] at hh
    rw [Finset.sup_insert,Finset.sum_insert hi,hh,ih]
end FiniteSpans

def incidentPairs (i : Fin 13) : Finset (Fin 33) := Finset.univ.filter (fun e => i∈pairVertices e)
def pairRelated (e f : Fin 33) : Prop := ¬Disjoint (pairVertices e) (pairVertices f)
instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
 theorem pairRelated_symm (e f : Fin 33) : pairRelated e f → pairRelated f e := by
  unfold pairRelated; intro h hf; exact h hf.symm
 theorem incidentPairs_card : ∀ i, (incidentPairs i).card = (![4,6,4,6,5,4,5,5,5,6,5,6,5] : Fin 13 → ℕ) i := by decide
 theorem incidentPairs_card_le : ∀ i, (incidentPairs i).card≤6 := by decide
 theorem pair_shared_card : ∀ e f, (Finset.univ.filter (fun i => e∈incidentPairs i ∧ f∈incidentPairs i)).card =
    if e=f then 2 else if pairRelated e f then 1 else 0 := by decide
 theorem incident_pair_card (e : Fin 33) : (Finset.univ.filter (fun i => e∈incidentPairs i)).card=2 := by
  have he : Finset.univ.filter (fun i => e∈incidentPairs i)=pairVertices e := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,incidentPairs]
  rw [he,pairVertices_card]
 theorem sum_incident (f : Fin 33 → ℝ) :
    (∑ i : Fin 13, ∑ e∈incidentPairs i, f e)=2*∑ e,f e := by
  simp only [incidentPairs,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (e : Fin 33) : (∑ i : Fin 13, if i∈pairVertices e then f e else 0)=2*f e := by
    rw [←Finset.sum_filter,Finset.sum_const]
    have hc : (Finset.univ.filter (fun i=>i∈pairVertices e)).card=2 := by
      have he : Finset.univ.filter (fun i=>i∈pairVertices e)=pairVertices e := by ext i; simp
      rw [he,pairVertices_card]
    rw [hc]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [hh]
  rw [Finset.mul_sum]
noncomputable def localPairDim (h : Fin 33 → ℕ) (i : Fin 13) : ℕ := ∑ e∈incidentPairs i,h e
 theorem localPairDim_le (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : localPairDim h i≤2*(incidentPairs i).card := by
  unfold localPairDim
  calc _ ≤ ∑ _e∈incidentPairs i, 2 := Finset.sum_le_sum (fun e _=>hh e)
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; omega
 theorem localPairDim_le_twelve (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : localPairDim h i≤12 := by
  have := localPairDim_le h hh i
  have := incidentPairs_card_le i
  omega
section GraphSpans
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
noncomputable def incidentSpan (A : Fin 33 → Submodule K E) (i : Fin 13) : Submodule K E :=
  (incidentPairs i).sup A
 theorem incidentSpan_le {A : Fin 33 → Submodule K E} {i : Fin 13} {L : Submodule K E}
    (h : ∀ e, i∈pairVertices e → A e≤L) : incidentSpan A i≤L := by
  apply Finset.sup_le
  intro e he
  exact h e (Finset.mem_filter.mp he).2
variable [FiniteDimensional K E]
 theorem incidentSpan_finrank_le (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e)) (i : Fin 13) :
    finrank K (incidentSpan (fun e=>(A e).val) i)≤localPairDim h i := by
  unfold incidentSpan localPairDim
  calc _ ≤ ∑ e∈incidentPairs i, finrank K (A e).val := finrank_finset_sup_le _ _
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)
 theorem incidentSpan_finrank_direct (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e))
    (ha : iSupIndep (fun e=>(A e).val)) (i : Fin 13) :
    finrank K (incidentSpan (fun e=>(A e).val) i)=localPairDim h i := by
  unfold incidentSpan localPairDim
  calc _ = ∑ e∈incidentPairs i, finrank K (A e).val := finrank_finset_sup_direct _ _ ha
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)
noncomputable def extendPairSpace (A : Fin 33 → Submodule K E) : Finset (Fin 13) → Submodule K E :=
  Function.extend pairVertices A (fun _=>⊥)
omit [FiniteDimensional K E] in
 theorem extendPairSpace_apply (A : Fin 33 → Submodule K E) (e : Fin 33) :
    extendPairSpace A (pairVertices e)=A e := pairVertices_injective.extend_apply _ _ _
omit [FiniteDimensional K E] in
 theorem extend_global_span (A : Fin 33 → Submodule K E) :
    (Finset.univ.image pairVertices).sup (extendPairSpace A)=⨆ e,A e := by
  rw [Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply,Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos]
omit [FiniteDimensional K E] in
 theorem extend_local_span (A : Fin 33 → Submodule K E) (i : Fin 13) :
    localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i=incidentSpan A i := by
  unfold localSpan incidentSpan incidentPairs
  rw [Finset.filter_image,Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply]
 theorem indexed_strict_span (A : Fin 33 → Submodule K E) (ha : ¬iSupIndep A) :
    2*finrank K ↥(⨆ e,A e)+1≤∑ i,finrank K (incidentSpan A i) := by
  have hn : ¬(Finset.univ.image pairVertices).SupIndep (extendPairSpace A) := by
    intro hs
    have hi := hs.independent
    have hj := hi.comp (f := fun e : Fin 33 => (⟨pairVertices e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩ : ↥(Finset.univ.image pairVertices))) (by
      intro e f hef
      exact pairVertices_injective (congrArg Subtype.val hef))
    apply ha
    simpa only [Function.comp_def,extendPairSpace_apply] using hj
  have hb := strict_span_inequality (Finset.univ.image pairVertices) (extendPairSpace A)
    (by intro e he; obtain ⟨f,_,rfl⟩:=Finset.mem_image.mp he; exact pairVertices_card f) hn
  rw [extend_global_span] at hb
  have hs : (∑ i : Fin 13,finrank K (localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i))=∑ i,finrank K (incidentSpan A i) :=
    Finset.sum_congr rfl (fun i _ => congrArg (fun S : Submodule K E => finrank K S) (extend_local_span A i))
  rw [hs] at hb
  exact hb
end GraphSpans
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem pairRelated_self (e : Fin 33) : pairRelated e e := by
  intro he
  have hb := disjoint_self.mp he
  have hc := pairVertices_card e
  rw [hb] at hc
  simp at hc
 theorem related_label_count (h : Fin 33 → ℕ) :
    (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)=
      (∑ e, ∑ f, if pairRelated e f then (h e:ℝ)*h f else 0)-∑ e,(h e:ℝ) := by
  classical
  rw [nat_card_subtype_sum,Nat.cast_sum,Fintype.sum_prod_type]
  have he (a b : Σ e, Fin (h e)) :
      (if a≠b ∧ pairRelated a.1 b.1 then (1:ℝ) else 0)=
        (if pairRelated a.1 b.1 then (1:ℝ) else 0)-(if a=b then 1 else 0) := by
    by_cases hab : a=b
    · subst b; simp [pairRelated_self]
    · by_cases hr : pairRelated a.1 b.1 <;> simp [hab,hr]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [he,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  congr 1
  simp_rw [Fintype.sum_sigma]
  simp [Finset.sum_const,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  by_cases hr : pairRelated e f <;> simp [hr]

 theorem sum_local_products (f g : Fin 33 → ℝ) :
    (∑ i : Fin 13, (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e))=
      ∑ e,∑ a, ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ a∈incidentPairs i)).card:ℝ)*f e*g a := by
  classical
  have hf (i : Fin 13) : (∑ e∈incidentPairs i,∑ a∈incidentPairs i,f e*g a)=
      ∑ e : Fin 33,∑ a : Fin 33, if e∈incidentPairs i ∧ a∈incidentPairs i then f e*g a else 0 := by
    symm
    simp only [ite_and]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_ite_mem]
    simp only [Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hp (i : Fin 13) : (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e)=
      ∑ e∈incidentPairs i,∑ a∈incidentPairs i,f e*g a := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hp,hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_filter,Finset.sum_const]
  simp only [nsmul_eq_mul,mul_assoc]

 theorem sum_local_squares (h : Fin 33 → ℕ) :
    (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
      (∑ e,(h e:ℝ)^2)+(∑ e,∑ f,if pairRelated e f then (h e:ℝ)*h f else 0) := by
  classical
  have he : (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
      ∑ i : Fin 13,(∑ e∈incidentPairs i,(h e:ℝ))*(∑ e∈incidentPairs i,(h e:ℝ)) := by
    simp only [localPairDim,Nat.cast_sum,pow_two]
  rw [he,sum_local_products]
  have hp (e f : Fin 33) :
      ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ f∈incidentPairs i)).card:ℝ)*(h e:ℝ)*h f=
      (if e=f then (h e:ℝ)^2 else 0)+(if pairRelated e f then (h e:ℝ)*h f else 0) := by
    rw [pair_shared_card]
    by_cases hef : e=f
    · subst f; simp only [ite_true,pairRelated_self,Nat.cast_ofNat,pow_two]; ring
    · by_cases hr : pairRelated e f <;> simp [hef,hr]
  simp_rw [hp,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

 theorem sum_localPairDim (h : Fin 33 → ℕ) : (∑ i,(localPairDim h i:ℝ))=2*∑ e,(h e:ℝ) := by
  simpa only [localPairDim,Nat.cast_sum] using sum_incident (fun e=>(h e:ℝ))

 theorem residual_direct_exponent (D : ℕ) (h : Fin 33 → ℕ) :
    2*(D:ℝ)*(∑ e,(h e:ℝ))-
      (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)/2-
      (∑ e,(h e:ℝ)^2)+(∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
      -∑ e,triangular (h e) := by
  rw [related_label_count]
  have hl : (∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
      -(D:ℝ)*(∑ i,(localPairDim h i:ℝ))+((∑ i,(localPairDim h i:ℝ)^2)-(∑ i,(localPairDim h i:ℝ)))/2 := by
    simp only [mul_sub,mul_one,sub_div,←pow_two]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_div,Finset.mul_sum]
  rw [hl,sum_localPairDim,sum_local_squares]
  have ht : (∑ e,triangular (h e))=((∑ e,(h e:ℝ)^2)+(∑ e,(h e:ℝ)))/2 := by
    unfold triangular
    simp only [mul_add,mul_one,←pow_two]
    rw [←Finset.sum_div,Finset.sum_add_distrib]
  rw [ht]
  ring
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem degree_choose_sum : (∑ i : Fin 13,(2*(incidentPairs i).card).choose 2)=618 := by decide
 theorem local_choose_sum_bound (ki : Fin 13 → ℕ) (hk : ∀ i,ki i≤2*(incidentPairs i).card) :
    (∑ i : Fin 13, (ki i:ℝ)*(ki i-1)/2)≤618 := by
  have hb : (∑ i : Fin 13,(ki i).choose 2)≤618 := by
    rw [←degree_choose_sum]
    exact Finset.sum_le_sum (fun i _=>Nat.choose_le_choose 2 (hk i))
  have hc : (∑ i : Fin 13, ((ki i).choose 2:ℝ))≤618 := by exact_mod_cast hb
  simpa only [Nat.cast_choose_two] using hc
 theorem residual_nondirect_exponent (D k : ℕ) (h : Fin 33 → ℕ) (ki : Fin 13 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hk : ∀ i,ki i≤2*(incidentPairs i).card)
    (hs : 2*k+1≤∑ i,ki i) :
    (k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+
      (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))≤-(D:ℝ)+1575 := by
  have hsq (e : Fin 33) : (h e:ℝ)^2=2*(h e:ℝ) := by rcases hh e with he|he <;> rw [he] <;> norm_num
  have hle (e : Fin 33) : (h e:ℝ)≤2 := by rcases hh e with he|he <;> rw [he] <;> norm_num
  have hb : (∑ e,(h e:ℝ))≤66 := by
    calc _ ≤ ∑ _e : Fin 33,(2:ℝ) := Finset.sum_le_sum (fun e _=>hle e)
         _ = _ := by norm_num
  have hn : 0≤∑ e,(h e:ℝ) := Finset.sum_nonneg (fun _ _=>Nat.cast_nonneg _)
  have hs' : 2*(k:ℝ)+1≤∑ i,(ki i:ℝ) := by exact_mod_cast hs
  have hc := local_choose_sum_bound ki hk
  have hh' : (∑ e,(h e:ℝ)*(k-h e))=(k:ℝ)*(∑ e,(h e:ℝ))-2*(∑ e,(h e:ℝ)) := by
    simp_rw [mul_sub,←pow_two,hsq]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum]
    ring
  have hg : (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))=
      -(D:ℝ)*(∑ i,(ki i:ℝ))+(∑ i : Fin 13,(ki i:ℝ)*(ki i-1)/2) := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [hh',hg]
  have hd := mul_nonneg (Nat.cast_nonneg D) (sub_nonneg.mpr hs')
  have hm := mul_nonneg hn (sub_nonneg.mpr hb)
  nlinarith [sq_nonneg ((k:ℝ)-(∑ e,(h e:ℝ))/2)]
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Containment
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def pairSpaces (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) : Submodule K E :=
  (pairVertices e).inf (fun i=>(L i).val)
 theorem pairSpaces_le (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) (i : Fin 13)
    (hi : i∈pairVertices e) : pairSpaces ω L e≤(L i).val := Finset.inf_le hi
 theorem incidentPairSpaces_le (L : Fin 13 → SymplecticLagrangian ω) (i : Fin 13) :
    incidentSpan (pairSpaces ω L) i≤(L i).val :=
  incidentSpan_le (fun e he=>pairSpaces_le ω L e i he)
 theorem pairSpaces_orthogonal (L : Fin 13 → SymplecticLagrangian ω) (e f : Fin 33)
    (hr : pairRelated e f) {x y : E} (hx : x∈pairSpaces ω L e) (hy : y∈pairSpaces ω L f) : ω x y=0 := by
  classical
  obtain ⟨i,he,hf⟩ := Finset.not_disjoint_iff.mp hr
  have hxi := pairSpaces_le ω L e i he hx
  have hyi := pairSpaces_le ω L f i hf hy
  have hyO : y∈ω.orthogonal (L i).val := (L i).property.symm ▸ hyi
  exact hyO x hxi
abbrev PairDimProfile (h : Fin 33 → ℕ) :=
  {L : Fin 13 → SymplecticLagrangian ω // ∀ e,finrank K (pairSpaces ω L e)=h e}
abbrev DirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // iSupIndep (pairSpaces ω L.val)}
abbrev FamilyContainment (A : Fin 33 → Submodule K E) :=
  (i : Fin 13) → {L : SymplecticLagrangian ω // incidentSpan A i≤L.val}
noncomputable def directPairProfileCoding (h : Fin 33 → ℕ) (L : DirectPairProfile ω h) :
    Σ A : DirectFamily ω h pairRelated, FamilyContainment ω (fun e=>(A.val e).val) :=
  ⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property,
    fun e f hr _ hx _ hy=>pairSpaces_orthogonal ω L.val.val e f hr hx hy⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
 theorem directPairProfileCoding_injective (h : Fin 33 → ℕ) :
    Function.Injective (directPairProfileCoding ω h) := by
  let recover : (Σ A : DirectFamily ω h pairRelated, FamilyContainment ω (fun e=>(A.val e).val)) →
      (Fin 13 → SymplecticLagrangian ω) := fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))
noncomputable def containmentExponent (D : ℕ) (ki : Fin 13 → ℕ) : ℝ :=
  ∑ i, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2)
variable [Fintype K] [Finite E]
 theorem familyContainment_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (A : Fin 33 → Submodule K E) (ki : Fin 13 → ℕ)
    (hk : ∀ i,finrank K (incidentSpan A i)=ki i) :
    (Nat.card (FamilyContainment ω A):ℝ) ≤ (lagrangianConstant D)^13*
      (Nat.card (SymplecticLagrangian ω):ℝ)^13*(Fintype.card K:ℝ)^(containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hp (i : Fin 13) : (Nat.card {L : SymplecticLagrangian ω // incidentSpan A i≤L.val}:ℝ) ≤
      lagrangianConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)*
        (Fintype.card K:ℝ)^(-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2) := by
    simpa only [hk i] using containingLagrangian_card_rpow ω h2 ha hω D hD (incidentSpan A i)
  have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _=>Nat.cast_nonneg (Nat.card {L : SymplecticLagrangian ω // incidentSpan A i≤L.val})) (fun i _=>hp i)
  rw [FamilyContainment,Nat.card_pi,Nat.cast_prod]
  calc _ ≤ _ := hh
       _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
          mul_pow,←Real.rpow_sum_of_pos hq]
        rfl
 theorem directPairProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hn : (∑ e,h e)≤2*D) :
    (Nat.card (DirectPairProfile ω h):ℝ) ≤
      2^(∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(∑ e,triangular (h e))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : DirectFamily ω h pairRelated, (Nat.card (FamilyContainment ω (fun e=>(A.val e).val)):ℝ) ≤
      (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D (localPairDim h)) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ (incidentSpan_finrank_direct h A.val A.property.1)
  have hi : (Nat.card (DirectPairProfile ω h):ℝ)≤
      Nat.card (Σ A : DirectFamily ω h pairRelated,FamilyContainment ω (fun e=>(A.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directPairProfileCoding_injective ω h)
  have hn' : (∑ e,h e)≤finrank K E := hD ▸ hn
  have hf := directFamily_card_bound ω hω h pairRelated pairRelated_symm hn'
  rw [←hD,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum] at hf
  have hc : 0 ≤ (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D (localPairDim h)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (lagrangianConstant_pos D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by
        have he := residual_direct_exponent D h
        change _+containmentExponent D (localPairDim h)=_ at he
        rw [←he,Real.rpow_add hq]
        ring
end Containment
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Nondirect
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
abbrev LocalFamilyStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {A : FamilySpanStratum (K:=K) (E:=E) h k // ∀ i,finrank K (incidentSpan (fun e=>(A.val e).val) i)=ki i}
abbrev PairSpanStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {L : PairDimProfile ω h // finrank K ↥(⨆ e,pairSpaces ω L.val e)=k ∧
    ∀ i,finrank K (incidentSpan (pairSpaces ω L.val) i)=ki i}
noncomputable def pairSpanStratumCoding (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (L : PairSpanStratum ω h k ki) :
    Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki, FamilyContainment ω (fun e=>(A.val.val e).val) :=
  ⟨⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property.1⟩,L.property.2⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
omit [Fintype K] [Finite E] in
 theorem pairSpanStratumCoding_injective (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :
    Function.Injective (pairSpanStratumCoding ω h k ki) := by
  let recover : (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      FamilyContainment ω (fun e=>(A.val.val e).val)) → (Fin 13 → SymplecticLagrangian ω) :=
    fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))
 theorem localFamilyStratum_card_bound (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (hk : k≤finrank K E) (hh : ∀ e,h e≤k) :
    (Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki):ℝ)≤
      2^(k+∑ e,h e)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ e,h e*(k-h e)) := by
  have hi : Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki)≤
      Nat.card (FamilySpanStratum (K:=K) (E:=E) h k) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (Nat.cast_le.mpr hi).trans (familySpan_card_upper h k hk hh)
 theorem familySpan_exponent_cast (h : Fin 33 → ℕ) (k n : ℕ) (hk : k≤n) (hh : ∀ e,h e≤k) :
    ((k*(n-k)+∑ e,h e*(k-h e):ℕ):ℝ)=
      (k:ℝ)*(n-k)+∑ e,(h e:ℝ)*(k-h e) := by
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hk,Nat.cast_sum,Nat.cast_sub (hh _)]
 theorem pairSpanStratum_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (hk : k≤2*D) (hh : ∀ e,h e≤k) :
    (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      2^(k+∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^((k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      (Nat.card (FamilyContainment ω (fun e=>(A.val.val e).val)):ℝ) ≤
      (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D ki) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ A.property
  have hi : (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      Nat.card (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,FamilyContainment ω (fun e=>(A.val.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairSpanStratumCoding_injective ω h k ki)
  have hn : k≤finrank K E := hD ▸ hk
  have hf := localFamilyStratum_card_bound h k ki hn hh
  rw [←Real.rpow_natCast (Fintype.card K:ℝ),familySpan_exponent_cast h k _ hn hh,←hD,
    Nat.cast_mul,Nat.cast_ofNat] at hf
  have hc : 0 ≤ (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D ki) :=
    mul_nonneg (mul_nonneg (pow_nonneg (lagrangianConstant_pos D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by simp only [Real.rpow_add hq];ring
 theorem residual_h_sum_le (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) : (∑ e,h e)≤66 := by
  calc _ ≤ ∑ _e : Fin 33,2 := Finset.sum_le_sum (fun e _=>by rcases hh e with he|he <;> omega)
       _ = _ := by decide
omit [Fintype K] in
 theorem pairProfile_global_dim_le (h : Fin 33 → ℕ) (L : PairDimProfile ω h) :
    finrank K ↥(⨆ e,pairSpaces ω L.val e)≤∑ e,h e := by
  have hh := finrank_finite_iSup_le (pairSpaces ω L.val)
  simpa only [L.property] using hh
omit [Fintype K] in
 theorem pairProfile_local_dim_le (h : Fin 33 → ℕ) (L : PairDimProfile ω h) (i : Fin 13) :
    finrank K (incidentSpan (pairSpaces ω L.val) i)≤localPairDim h i :=
  incidentSpan_finrank_le h (fun e=>⟨_,L.property e⟩) i
abbrev ResidualDimensionBox := Fin 67 × (Fin 13 → Fin 13)
noncomputable def pairProfileDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : PairDimProfile ω h) : ResidualDimensionBox :=
  (⟨finrank K ↥(⨆ e,pairSpaces ω L.val e),by
    have := (pairProfile_global_dim_le ω h L).trans (residual_h_sum_le h hh); omega⟩,
   fun i=>⟨finrank K (incidentSpan (pairSpaces ω L.val) i),by
    have := (pairProfile_local_dim_le ω h L i).trans (localPairDim_le_twelve h (fun e=>by rcases hh e with he|he <;> omega) i)
    omega⟩)
abbrev NonDirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // ¬iSupIndep (pairSpaces ω L.val)}
noncomputable def nondirectDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : NonDirectPairProfile ω h) : ResidualDimensionBox := pairProfileDimension ω h hh L.val
noncomputable def nondirectFiberInjection (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) (L : {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}) :
    PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val) := by
  refine ⟨L.val.val,?_,?_⟩
  · exact congrArg (fun b : ResidualDimensionBox=>b.1.val) L.property
  · intro i
    exact congrArg (fun b : ResidualDimensionBox=>(b.2 i).val) L.property
omit [Fintype K] in
 theorem nondirectFiberInjection_injective (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) : Function.Injective (nondirectFiberInjection ω h hh b) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun X : PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)=>X.val) hxy
 theorem pairStratum_residual_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) (hk : b.1.val≤2*D) (he : ∀ e,h e≤b.1.val)
    (hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card) (hs : 2*b.1.val+1≤∑ i,(b.2 i).val) :
    (Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)):ℝ)≤
      2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have hf := pairSpanStratum_card_bound ω h2 ha hω D hD h b.1.val (fun i=>(b.2 i).val) hk he
  have hq : 1≤(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hfexp := Real.rpow_le_rpow_of_exponent_le hq
    (residual_nondirect_exponent D b.1.val h (fun i=>(b.2 i).val) hh hki hs)
  have hbpow : (2:ℝ)^(b.1.val+∑ e,h e)≤2^132 := by
    apply pow_le_pow_right₀ (by norm_num)
    have := b.1.isLt
    have := residual_h_sum_le h hh
    omega
  have hC := pow_nonneg (lagrangianConstant_pos D).le 13
  have hL : 0≤(Nat.card (SymplecticLagrangian ω):ℝ)^13 := pow_nonneg (Nat.cast_nonneg _) _
  have hP : (0:ℝ)≤2^132 := pow_nonneg (by norm_num) _
  refine hf.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbpow hC) hL)
    hfexp (Real.rpow_nonneg (le_trans (by norm_num) hq) _) (mul_nonneg (mul_nonneg hP hC) hL)
 theorem nondirectFiber_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) :
    (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
      2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  classical
  by_cases hex : Nonempty {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}
  · obtain ⟨L⟩ := hex
    let A := pairSpaces ω L.val.val.val
    have hb := (nondirectFiberInjection ω h hh b L).property
    change finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)=b.1.val ∧
      (∀ i,finrank K (incidentSpan (pairSpaces ω L.val.val.val) i)=(b.2 i).val) at hb
    have hk : b.1.val≤2*D := by
      rw [hD,←hb.1]
      exact Submodule.finrank_le _
    have he : ∀ e,h e≤b.1.val := by
      intro e
      rw [←L.val.val.property e,←hb.1]
      exact Submodule.finrank_mono (le_iSup (pairSpaces ω L.val.val.val) e)
    have hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card := by
      intro i
      rw [←hb.2 i]
      exact (pairProfile_local_dim_le ω h L.val.val i).trans
        (localPairDim_le h (fun e=>by rcases hh e with he|he <;> omega) i)
    have hs : 2*b.1.val+1≤∑ i,(b.2 i).val := by
      have hs := indexed_strict_span A L.val.property
      change 2*finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)+1≤
        ∑ i,finrank K (incidentSpan (pairSpaces ω L.val.val.val) i) at hs
      simpa only [hb.1,hb.2] using hs
    have hi : (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
        Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)) := by
      exact_mod_cast Nat.card_le_card_of_injective _ (nondirectFiberInjection_injective ω h hh b)
    exact hi.trans (pairStratum_residual_bound ω h2 ha hω D hD h hh b hk he hki hs)
  · have : IsEmpty {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b} := not_nonempty_iff.mp hex
    rw [Nat.card_of_isEmpty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (lagrangianConstant_pos D).le _)) (pow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
 theorem nondirectPairProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (Nat.card (NonDirectPairProfile ω h):ℝ)≤
      (67*13^13)*2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv (nondirectDimension ω h hh))
  rw [←he]
  have hb := real_card_sigma_le _ (nondirectFiber_card_bound ω h2 ha hω D hD h hh)
  convert hb using 1
  simp only [ResidualDimensionBox,Nat.card_prod,Nat.card_fin,Nat.card_fun,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring
end Nondirect
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev FullTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) :=
  Σ u : CommonParameters D r c, BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)
noncomputable def fullTailConstant (D r c : ℕ) (s : Fin 3 → ℕ)
    (x : FullTailChoice D r c s) : ℝ :=
  (orbitMassConstant D*(lagrangianConstant D)^2)*(lagrangianConstant D*2^c)*
    ((2^x.1.val.val*lagrangianConstant (D-x.1.val.val))*2^(3*(D-c)))*
    reducedPlantedConstant (r-x.1.val.val) (s 0) (s 1) (s 2) x.2.val
 theorem fullTailConstant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (x : FullTailChoice D r c s) :
    0 ≤ fullTailConstant D r c s x := by
  have h₀ := (orbitMassConstant_pos D).le
  have h₁ := (lagrangianConstant_pos D).le
  have h₂ := (lagrangianConstant_pos (D-x.1.val.val)).le
  unfold fullTailConstant reducedPlantedConstant
  positivity
noncomputable def fullTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) : ℝ :=
  ∑ x : FullTailChoice D r c s,
    fullTailConstant D r c s x * q^(tailGain D true (plantedTailTuple D r c s x.1 x.2))
 theorem fullTailMajorant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 0≤q) :
    0 ≤ fullTailMajorant D r c s q := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (fullTailConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hq _)
 theorem fullTailMajorant_eq (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ)
    (hD : D=2*r) (hc : c≤D) (hq : 0<q) :
    fullTailMajorant D r c s q =
      (orbitMassConstant D*(lagrangianConstant D)^2)*
      q^(((D:ℝ)+1)*c+(∑ i,triangular (s i))+3*triangular r-4*triangular D)*
      ((lagrangianConstant D*2^c)*q^(isotropicExponent D c)*
        ∑ u : CommonParameters D r c,
          ((2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)))*
          q^((u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
            3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ))*
          reducedPlantedSum (D-c) (r-u.val.val) (s 0) (s 1) (s 2) q) := by
  classical
  unfold fullTailMajorant
  rw [Fintype.sum_sigma]
  simp_rw [←fullPlantedExponent_eq D c r hD hc s,fullPlantedExponent,Real.rpow_add hq,
    Real.rpow_sub hq,reducedPlantedSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro θ _
  unfold fullTailConstant
  simp only [Real.rpow_add hq,Real.rpow_sub hq,Real.rpow_natCast]
  ring
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem tripleFaceDensity_tail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
    (hq : 4*lagrangianConstant D≤(Fintype.card K:ℝ)) (A L M N : SymplecticLagrangian ω) :
    let c := finrank K ↥((L.val⊓M.val)⊓N.val)
    let s : Fin 3 → ℕ := ![finrank K ↥(L.val⊓M.val)-c,finrank K ↥(L.val⊓N.val)-c,
      finrank K ↥(M.val⊓N.val)-c]
    tripleFaceDensity ω r A L M N ≤ fullTailMajorant D r c s (Fintype.card K) := by
  dsimp only
  have hc : finrank K ↥((L.val⊓M.val)⊓N.val)≤D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [fullTailMajorant_eq _ _ _ _ _ hr hc hq0]
  have hh := tripleFaceDensity_full_bound ω h2 ha hω D hD hq r (by omega) A L M N
  dsimp only at hh
  refine hh.trans_eq ?_
  simp only [tripleDefect,commonPlantedTerm,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,triangular_nat]
end Actual
end SidorenkoCounterexample

end OAI
