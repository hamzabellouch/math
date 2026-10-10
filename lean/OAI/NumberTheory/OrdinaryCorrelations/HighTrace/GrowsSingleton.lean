import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FixedIsTagged
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BitWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open Finset Classical
variable {h ℓ : ℕ}

lemma grows_singleton (w : ClosedLine h ℓ) (v : ℤ) (e : Fin ℓ) :
    Grows w v {e} ↔ e ∈ w.treeSteps ∧ w.offset e.castSucc = v := by
  constructor
  · intro hg
    refine ⟨hg.1 (mem_singleton_self _),?_⟩
    rcases hg.2 e (mem_singleton_self _) with hr | ⟨j,hj,hje,hjv⟩
    · exact hr
    · have hj' : j=e := mem_singleton.mp hj
      subst j
      exact False.elim (lt_irrefl _ hje)
  · rintro ⟨he,hev⟩
    refine ⟨singleton_subset_iff.mpr he,?_⟩
    intro j hj
    have hj' : j=e := mem_singleton.mp hj
    subst j
    exact Or.inl hev

lemma singleton_mem_shapes (w : ClosedLine h ℓ) (v : ℤ) (e : Fin ℓ) :
    {e} ∈ (shapes w v).erase ∅ ↔ e ∈ w.treeSteps ∧ w.offset e.castSucc = v := by
  simp only [mem_erase,singleton_ne_empty,ne_eq,not_false_eq_true,true_and,
    mem_shapes,grows_singleton]

theorem sum_singleton_corrections (w : ClosedLine h ℓ) (f : Fin ℓ → ℝ) :
    (∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅,
      ∑ e ∈ w.treeSteps, if E = {e} then f e else 0) = ∑ e ∈ w.treeSteps, f e := by
  calc
    _ = ∑ e ∈ w.treeSteps, ∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅,
        if E = {e} then f e else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro e he
      simp only [sum_ite_eq',singleton_mem_shapes,he,true_and]
      have hv : w.offset e.castSucc ∈ treeVertices w := mem_image.mpr ⟨_,mem_univ _,rfl⟩
      simp [hv]

lemma good_singleton_raw {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index) (hp : ¬S.IsCore p)
    (e : Fin ℓ) (he : w.Good e) : subtreeUnionWeight w p {e} = theta := by
  have hne := w.endpoints_ne hh e
  simp only [subtreeUnionWeight,card_singleton,pow_one,edgeVertices,image_singleton,
    singleton_union,prod_pair hne,
    he.2.1,he.2.2.1,pow_one,beta_eq_center p hp]
  simp [amplitude,hp,theta,pow_two]

lemma modified_raw_correction {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index) (hp : ¬S.IsCore p)
    (E : Finset (Fin ℓ)) (hE : E ⊆ w.treeSteps) :
    modifiedWeight w p E = subtreeUnionWeight w p E +
      ∑ e ∈ w.treeSteps, if E = {e} then (if w.Good e then -theta/2 else theta) else 0 := by
  by_cases hs : ∃ e, E = {e}
  · obtain ⟨e,rfl⟩ := hs
    have hem : e ∈ w.treeSteps := hE (mem_singleton_self _)
    have hsum : (∑ j ∈ w.treeSteps,
        if ({e} : Finset (Fin ℓ)) = {j} then (if w.Good j then -theta/2 else theta) else 0) =
        (if w.Good e then -theta/2 else theta) := by
      simp only [singleton_inj]
      simp [hem]
    rw [hsum]
    by_cases hg : w.Good e
    · have hex : ∃ j, ({e} : Finset (Fin ℓ)) = {j} ∧ w.Good j := ⟨e,rfl,hg⟩
      rw [modifiedWeight,ite_eq_right hp,ite_eq_left hex,ite_eq_left hg,good_singleton_raw w hh p hp e hg]
      ring
    · have hn : ¬∃ j, ({e} : Finset (Fin ℓ)) = {j} ∧ w.Good j := by
        rintro ⟨j,hj,hgj⟩
        have hej : e=j := singleton_inj.mp hj
        exact hg (hej ▸ hgj)
      have hex : ∃ j, ({e} : Finset (Fin ℓ)) = {j} ∧ ¬w.Good j := ⟨e,rfl,hg⟩
      rw [modifiedWeight,ite_eq_right hp,ite_eq_right hn,ite_eq_left hex,ite_eq_right hg]
  · have hn₁ : ¬∃ e, E={e} ∧ w.Good e := by rintro ⟨e,he,_⟩; exact hs ⟨e,he⟩
    have hn₂ : ¬∃ e, E={e} ∧ ¬w.Good e := by rintro ⟨e,he,_⟩; exact hs ⟨e,he⟩
    rw [modifiedWeight,ite_eq_right hp,ite_eq_right hn₁,ite_eq_right hn₂]
    have hz : (∑ e ∈ w.treeSteps,
        if E={e} then (if w.Good e then -theta/2 else theta) else 0) = 0 := by
      apply sum_eq_zero
      intro e he
      exact ite_eq_right (fun h => hs ⟨e,h⟩)
    rw [hz,add_zero]

def goodEdges (w : ClosedLine h ℓ) : Finset (Fin ℓ) := w.treeSteps.filter w.Good

def badEdges (w : ClosedLine h ℓ) : Finset (Fin ℓ) := w.treeSteps.filter (fun e => ¬w.Good e)

lemma correction_sum (w : ClosedLine h ℓ) :
    (∑ e ∈ w.treeSteps, if w.Good e then -theta/2 else theta) =
      -theta/2 * (goodEdges w).card + theta * (badEdges w).card := by
  rw [sum_ite]
  simp only [sum_const,nsmul_eq_mul,goodEdges,badEdges]
  ring

theorem modified_center_subtree_sum {S : OrdinaryCorrelations.GraphKernel.PrimeSystem}
    (w : ClosedLine h ℓ) (hh : 0 < h) (p : S.Index) (hp : ¬S.IsCore p) :
    (∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅, modifiedWeight w p E) -
      bandDefect w betaZ ≤ -theta/2 * (goodEdges w).card + theta * (badEdges w).card := by
  have hraw := numerical_subtree_sum_le w 1 betaZ (by norm_num) (by norm_num [betaZ])
    (by norm_num [betaZ])
  have heq : (∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅, modifiedWeight w p E) =
      (∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅, subtreeUnionWeight w p E) +
      ∑ e ∈ w.treeSteps, if w.Good e then -theta/2 else theta := by
    rw [← sum_singleton_corrections w (fun e => if w.Good e then -theta/2 else theta),← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro E hE
    exact modified_raw_correction w hh p hp E (((mem_shapes ..).mp (mem_erase.mp hE).2).1)
  rw [heq,correction_sum]
  have hr : (∑ v ∈ treeVertices w, ∑ E ∈ (shapes w v).erase ∅,
      subtreeUnionWeight w p E) ≤ bandDefect w betaZ := by
    simpa only [subtreeUnionWeight,amplitude,hp,ite_false,beta_eq_center p hp] using hraw
  linarith

end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
