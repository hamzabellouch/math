import OAI.Combinatorics.HadwigerCounterexample.SpanDeficits

namespace OAI

/-! # Greedy Exposures -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Module Finset
open scoped BigOperators
variable {p : Shape} {N : ℕ} {I : Type} [DecidableEq I]

def price (f : I → Ambient p N) (S : Cov p N) (W : Finset I) :=
  W.sup (fun i => tax p S (matter p (f i)))

private theorem tax_comp (a b c : Cov p N) :
    tax p a (b⊔c)=tax p a b + tax p (a⊔b) c := by
  have h1 := tax_before (p:=p) a (b⊔c)
  have h2 := tax_before (p:=p) a b
  have h3 := tax_before (p:=p) (a⊔b) c
  rw [sup_assoc] at h3
  omega

omit [DecidableEq I] in
private theorem price_drop (f : I → Ambient p N) (S T : Cov p N) (W R : Finset I)
    (h : S ≤ T) (g : R⊆ W) :
    price f T R ≤ price f S W := by
  refine Finset.sup_le fun i hi => (tax_antitone p S T (matter p (f i)) h).trans ?_
  exact (@Finset.le_sup _ _ _ _ W (fun i => tax p S (matter p (f i))) i (g hi))

private theorem union_arrange (f : I→Ambient p N) (W R : Finset I) :
    arrange p f (W∪R)= arrange p f W⊔arrange p f R := Finset.sup_union

private theorem grow (p : Shape) {N} (f : I→Ambient p N) (S : Cov p N) (W : Finset I)
    (r : ℕ) (h : r≤W.card) :
    ∃ E R : Finset I, W=E∪R ∧ Disjoint E R ∧ E.card=r ∧
      r*price f (S⊔ arrange p f E) R ≤ tax p S (arrange p f E) := by
  classical
  induction r generalizing W S with
  | zero => exact ⟨∅,W,by simp⟩
  | succ r ih =>
    obtain ⟨x,hx,hP⟩ := Finset.exists_mem_eq_sup W
      (Finset.card_pos.mp (show 0<W.card by omega)) (fun i => tax p S (matter p (f i)))
    let U := W.erase x
    let X := matter p (f x)
    have hU : U.card+1=W.card := Finset.card_erase_add_one hx
    obtain ⟨E,R,hE,hd,hT,hK⟩ := ih (S⊔X) U (by omega)
    have hx' : x∉E := fun H => Finset.notMem_erase _ _ (hE.symm ▸ Finset.mem_union_left R H)
    have hx'' : x∉R := fun H => Finset.notMem_erase _ _ (hE.symm ▸ Finset.mem_union_right E H)
    refine ⟨insert x E,R,?_,?_,?_,?_⟩
    · rw [Finset.insert_union,← hE,Finset.insert_erase hx]
    · rw [Finset.disjoint_insert_left]
      exact ⟨hx'',hd⟩
    · rw [Finset.card_insert_of_notMem hx',hT]
    · have hg : arrange p f (insert x E)=X⊔arrange p f E := Finset.sup_insert
      rw [hg,tax_comp (p:=p),←sup_assoc,Nat.add_mul,Nat.one_mul]
      have hi := price_drop f S (S⊔X⊔arrange p f E) W R
        (le_trans le_sup_left le_sup_left)
        (Finset.Subset.trans (show R⊆U from hE.symm ▸ Finset.subset_union_right)
          (Finset.erase_subset ..))
      have h1 : price f S W=tax p S X := hP
      rw [h1] at hi
      refine (Nat.add_le_add hK hi).trans_eq (Nat.add_comm ..)

/-- Dyadic selection if potential is strictly too low to sustain
all bad tail deficit ratios -/
private theorem greedy_expose (f : I→Ambient p N) (S : Cov p N) (W : Finset I)
    (b m : ℕ) (hW : W.card=2^m*b)
    (hg : 4*(W.card*price f S W+tax p S (arrange p f W)) < W.card*m) :
    ∃ E R : Finset I, W=E∪R ∧ Disjoint E R ∧ b≤R.card ∧
      let s' := S⊔arrange p f E
      4*(R.card*price f s' R) ≤ 4*tax p s' (arrange p f R)+R.card := by
  classical
  induction m generalizing W S with
  | zero => omega
  | succ m ih =>
    by_cases he : 4*(W.card*price f S W)≤ 4*tax p S (arrange p f W)+W.card
    · have h1 : b ≤ W.card := by rw [hW]; exact Nat.le_mul_of_pos_left b (by positivity)
      exact ⟨∅,W,by simpa [arrange,h1] using he⟩
    let k := 2^m*b
    have h1 : W.card=2*k := by rw [hW,pow_succ]; unfold k; ring
    obtain ⟨E,R,hE,hD,hT,hB⟩ := grow p f S W k (by omega)
    have hk : R.card=k := by rw [hE,Finset.card_union_of_disjoint hD] at h1; omega
    let X := S⊔arrange p f E
    have hX :
        tax p S (arrange p f W)=tax p S (arrange p f E)+tax p X (arrange p f R) := by
      rw [hE,union_arrange,tax_comp (p:=p)]
    have hh : 4*(R.card*price f X R+ tax p X (arrange p f R))<R.card*m := by
      have hcalc (a a' t b t' k m : ℕ)
          (hh : 4*(2*k*a+t)<2*k*(m+1)) (ht : t=b+t') (h : k*a'≤b)
          (ha : 4*t+2*k<4*(2*k*a)) :
          4*(k*a'+t')< k*m := by nlinarith
      rw [h1] at he hg
      rw [hk]
      exact hcalc _ _ _ _ _ _ _ hg hX hB (lt_of_not_ge he)
    obtain ⟨F,T,hF,hT,hb,h'⟩ := ih X R hk hh
    have hu : Disjoint E (F∪T) := by rwa [← hF]
    refine ⟨E∪F,T,by rw [hE,hF,Finset.union_assoc],
      by simp only [Finset.disjoint_union_left]; exact
        ⟨Disjoint.mono_right (show T⊆ F∪T from Finset.subset_union_right) hu,hT⟩,hb,?_⟩
    rw [union_arrange, ←sup_assoc]; exact h'

private theorem sum_charge_sign (f : I → Ambient p N) (W : Finset I) (i : Bool) :
    cdSign p (arrange p f W) i ≤ ∑ j∈W,epoch p (f j) := by
  classical
  induction W using Finset.induction with
  | empty =>
    have h : cdSign p (N:=N) ⊥ i=0 := Finset.sum_eq_zero fun e _ => finrank_bot ..
    rw [arrange,Finset.sup_empty,Finset.sum_empty,h]
  | insert x W hx hi =>
    rw [show arrange p f (insert x W)=matter p (f x)⊔arrange p f W from Finset.sup_insert,
      Finset.sum_insert hx]
    calc cdSign p _ i ≤ cdSign p (matter p (f x)) i+cdSign p (arrange p f W) i := by
                          unfold cdSign
                          rw [← Finset.sum_add_distrib]
                          exact Finset.sum_le_sum fun i _ =>
                            Submodule.finrank_add_le_finrank_add_finrank ..
         _ ≤ _ := by rw [matter_dim]; exact add_le_add (le_refl _) hi

theorem arrange_bound (f : I→Ambient p N) (W : Finset I) (k : ℕ) (h : ∀ i ∈ W,epoch p (f i) ≤ k)
    (i : Bool) :
    cdSign p (arrange p f W) i ≤ W.card*k :=
  (sum_charge_sign f W i).trans ((Finset.sum_le_sum fun j hj => h j hj).trans_eq (by simp))

theorem sparse_covered (f : I→ Ambient p N) (W : Finset I)
    (m b r : ℕ) (hW : W.card=2^m*(2*b))
    (hb : 1 ≤ b) (hm : 16*r < m) (hf : ∀ i∈W,epoch p (f i) ≤ r)
    (h : 2 * epoch p (∑ i∈W,f i) ≤ b) :
    ∃ E T : Finset I,E⊆ W ∧ T⊆ W ∧ Disjoint E T ∧ T.card=b ∧
      ∀ i∈T,covered p (arrange p f E) (f i) := by
  classical
  have htax (C : Cov p N) : tax p ⊥ C = cdim p C := by rw [tax,cdim_bot,bot_sup_eq,Nat.sub_zero]
  have hx : price f ⊥ W ≤ 2*r := by
    refine Finset.sup_le fun i hi => ?_
    rw [htax,cdim_sign,matter_dim,matter_dim,two_mul]
    exact add_le_add (hf i hi) (hf i hi)
  have hh :
      4*(W.card*price f ⊥ W + tax p ⊥ (arrange p f W))<W.card*m := by
    have hk : tax p ⊥ (arrange p f W)≤2*(W.card*r) := by
      rw [htax,cdim_sign,two_mul]
      exact add_le_add (arrange_bound f W r hf true) (arrange_bound f W r hf false)
    have hg : 0 < W.card := by rw [hW]; positivity
    nlinarith
  obtain ⟨E,R,hE,hD,hR,hL⟩ := greedy_expose f ⊥ W (2*b) m hW hh
  simp only [bot_sup_eq] at hL
  let S := arrange p f E
  let P (i : I) := ¬ covered p S (f i)
  let J := R.filter P
  have hZ :
      epoch p (∑ i∈R,erased p S (f i)) ≤ epoch p (∑ i∈W,f i) := by
    have hh : ∑ i∈E,erased p S (f i) = 0 := Finset.sum_eq_zero fun i hi =>
      covered_part (S:=S) (show matter p (f i) ≤
        E.sup (fun j => matter p (f j)) from (@Finset.le_sup _ _ _ _ _ (fun j => matter p (f j)) _ hi))
    have h1 : (∑ i∈R, erased p S (f i))=erased p S (∑ i∈W,f i) := by
      rw [hE,Finset.sum_union hD,map_add,map_sum,map_sum,hh,zero_add]
    rw [h1]; exact epoch_erased ..
  have hu : J.card≤ ∑ i∈R,epoch p (erased p S (f i)) := by
    calc J.card = ∑ i∈R, (if P i then (1:ℕ) else 0) := by rw [←Finset.sum_filter]; simp [J]
         _ ≤ _ := Finset.sum_le_sum fun j _ => by
                   split
                   · rename_i hh
                     exact Nat.one_le_iff_ne_zero.mpr (fun h => hh ((epoch_eq_zero _).mp h))
                   exact Nat.zero_le _
  have hp : (∑ i∈R,tax p S (matter p (f i))) ≤ R.card*price f S R := by
    refine (Finset.sum_le_sum (g:=fun i => price f S R) fun i hi => ?_).trans_eq (by simp)
    exact (@Finset.le_sup _ _ _ _ _ (fun i => tax p S (matter p (f i))) i hi)
  have ht := (epoch_charge f S R).2
  have hb' : b≤ (R\ J).card := by
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset P _)]
    change b ≤ R.card-J.card
    have heq : J.card≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
    change 4*(R.card*price f S R) ≤ 4*tax p S (arrange p f R)+R.card at hL
    omega
  obtain ⟨T,hT,hb'⟩ := Finset.exists_subset_card_eq hb'
  have hz : T ⊆ R := hT.trans Finset.sdiff_subset
  refine ⟨E,T,hE.symm ▸ Finset.subset_union_left,hE.symm ▸ hz.trans Finset.subset_union_right,
    Disjoint.mono_right hz hD,hb',fun i hi => ?_⟩
  exact Classical.byContradiction fun h =>
    (Finset.mem_sdiff.mp (hT hi)).2 (Finset.mem_filter.mpr ⟨hz hi,h⟩)

end HadwigerCounterexample

end

end OAI
