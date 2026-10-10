import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Law

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped BigOperators Classical
open FiniteEntropy
variable {α ι : Type*} [Fintype α] [Fintype ι]

noncomputable def completionEquiv (I : Finset ι) (v : I → α) :
    {s : ι → α // ∀ i : I,s i.val = v i} ≃ ({i : ι // i ∉ I} → α) where
  toFun s i := s.val i.val
  invFun w := ⟨fun i => if h : i ∈ I then v ⟨i,h⟩ else w ⟨i,h⟩,by
    intro i
    simp only [i.property, dite_true]⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ I
    · simp only [hi,dite_true]
      exact (s.property ⟨i,hi⟩).symm
    · simp only [hi,dite_false]
  right_inv w := by
    funext i
    simp only [i.property,dite_false]

lemma completion_count (I : Finset ι) (v : I → α) :
    (Finset.univ.filter fun s : ι → α => ∀ i : I,s i.val = v i).card =
      Fintype.card α ^ (Fintype.card ι-I.card) := by
  classical
  have he := Fintype.card_congr (completionEquiv I v)
  rw [Fintype.card_fun,Fintype.card_subtype_compl,Fintype.card_coe] at he
  simpa only [Fintype.card_subtype] using he

variable {N l : ℕ}

noncomputable def matching (I : {I : Finset (Fin N) // I.card=l})
    (f : Fin l → α) : Finset (Fin N → α) :=
  Finset.univ.filter fun s => ∀ j,s (I.val.orderEmbOfFin I.property j) = f j

lemma matching_count (I : {I : Finset (Fin N) // I.card=l}) (f : Fin l → α) :
    (matching I f).card = Fintype.card α ^ (N-l) := by
  let e := I.val.orderIsoOfFin I.property
  have he : matching I f = Finset.univ.filter fun s : Fin N → α =>
      ∀ i : I.val,s i.val = f (e.symm i) := by
    ext s
    simp only [matching,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hs i
      have h := hs (e.symm i)
      have hi : I.val.orderEmbOfFin I.property (e.symm i) = i.val :=
        congrArg Subtype.val (e.apply_symm_apply i)
      rwa [hi] at h
    · intro hs j
      have h := hs (e j)
      change s (I.val.orderEmbOfFin I.property j) = f (e.symm (e j)) at h
      simpa only [e.symm_apply_apply] using h
  rw [he]
  convert (completion_count I.val (fun i => f (e.symm i))) using 1
  · congr
    exact Subsingleton.elim _ _
  · simp only [Fintype.card_fin,I.property]

noncomputable def occurrences (f : Fin l → α) : Finset (Fin N → α) :=
  Finset.univ.biUnion fun I : {I : Finset (Fin N) // I.card=l} => matching I f

lemma position_set_count : Fintype.card {I : Finset (Fin N) // I.card=l} = N.choose l := by
  classical
  have he : (Finset.univ.filter fun I : Finset (Fin N) => I.card=l) =
      Finset.univ.powersetCard l := by ext I; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem occurrence_count (f : Fin l → α) :
    (occurrences (N := N) f).card ≤ N.choose l * Fintype.card α^(N-l) := by
  calc
    _ ≤ ∑ I : {I : Finset (Fin N) // I.card=l},(matching I f).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [matching_count,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,position_set_count,Nat.cast_id]

theorem selected_atom [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) (f : Fin l → α) :
    second p f ≤ 2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l := by
  classical
  let E := occurrences (N := N) f ∪ occurrences (N := N) (rev f)
  have hm : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass : second p f ≤ ∑ s∈E,first p s := by
    change (∑ s,p (s,f)) ≤ _
    calc
      _ ≤ ∑ s,if s∈E then first p s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s ∈ E
        · simp only [hs,ite_true]
          exact le_first p s f
        · simp only [hs,ite_false]
          apply le_of_not_gt
          intro hp
          exact hs (Finset.mem_union.mpr (hselect s f hp))
      _ = _ := by rw [←Finset.sum_filter,Finset.filter_univ_mem]
  have hc : E.card ≤ 2*(N.choose l*Fintype.card α^(N-l)) := by
    exact (Finset.card_union_le _ _).trans ((add_le_add (occurrence_count f)
      (occurrence_count (rev f))).trans_eq (by ring))
  have hc' : (E.card:ℝ) ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l)) := by
    exact_mod_cast hc
  calc
    second p f ≤ ∑ s∈E,first p s := hmass
    _ ≤ ∑ _s∈E,C/(Fintype.card α:ℝ)^N := Finset.sum_le_sum fun s _ => hstream s
    _ = (E.card:ℝ)*(C/(Fintype.card α:ℝ)^N) := by simp
    _ ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l))*(C/(Fintype.card α:ℝ)^N) :=
      mul_le_mul_of_nonneg_right hc' (div_nonneg hC (pow_nonneg hm.le _))
    _ = _ := by
      have he : (Fintype.card α:ℝ)^N = (Fintype.card α:ℝ)^(N-l)*(Fintype.card α:ℝ)^l := by
        rw [←pow_add,Nat.sub_add_cancel hl]
      rw [he]
      field_simp

theorem selected_entropy [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) :
    -Real.log (2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l) ≤ entropy (second p) :=
  atom_bound_entropy (second p) _ (selected_atom hl p C hC hstream rev hselect)

end SharpRamseyFive.SelectedTuple

end OAI
