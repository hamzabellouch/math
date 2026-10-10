import OAI.Computability.MatchingCount.OddCutUncross

namespace OAI

section

namespace BinaryMatching.OddMincut
open Finset UnitFlow UnitMincut TerminalMincut CutAlgebra OddCutParity OddCutUncross
variable {n : ℕ}

def outside (A : Finset (Fin n)) : Option (Fin n) :=
  (List.finRange n).find? (fun v => decide (v∉A))

lemma outside_some (A : Finset (Fin n)) (hA : Aᶜ.Nonempty) :
    ∃ r, outside A=some r ∧ r∉A := by
  obtain ⟨v,hv⟩ := hA
  have hv' : v∉A := mem_compl.mp hv
  cases he : outside A with
  | none =>
    have hh := List.find?_eq_none.mp he v (by simp)
    simp [hv'] at hh
  | some r =>
    have hh := List.find?_some (show (List.finRange n).find?
      (fun v => decide (v∉A))=some r from he)
    exact ⟨r,rfl,by simpa using hh⟩

def cheaper (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) : Finset (Fin n) :=
  if cutCapacity c S ≤ cutCapacity c T then S else T

lemma cheaper_le_left (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cutCapacity c (cheaper c S T) ≤ cutCapacity c S := by
  unfold cheaper; split_ifs <;> omega

lemma cheaper_le_right (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cutCapacity c (cheaper c S T) ≤ cutCapacity c T := by
  unfold cheaper; split_ifs <;> omega

lemma cheaper_odd (c : Fin n → Fin n → ℕ) (U S T : Finset (Fin n))
    (hS : OddSide U S) (hT : OddSide U T) : OddSide U (cheaper c S T) := by
  unfold cheaper; split_ifs <;> assumption

def recurse : ℕ → (Fin n → Fin n → ℕ) → Finset (Fin n) → Finset (Fin n)
  | 0,_,_ => ∅
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then A else
      match outside A, outside Aᶜ with
      | some r, some q =>
        cheaper c
          (lift (contractMap A r) (recurse k (push c (contractMap A r)) (A∩U)))
          (lift (contractMap Aᶜ q) (recurse k (push c (contractMap Aᶜ q)) (Aᶜ∩U)))
      | _,_ => ∅

lemma recurse_correct (fuel : ℕ) (c : Fin n → Fin n → ℕ)
    (hc : ∀ i j, c i j=c j i) (U : Finset (Fin n)) (he : Even U.card)
    (hU : 2≤U.card) (hbound : U.card≤fuel) :
    OddSide U (recurse fuel c U) ∧
      ∀ S, OddSide U S → cutCapacity c (recurse fuel c U) ≤ cutCapacity c S := by
  induction fuel generalizing c U with
  | zero => omega
  | succ k ih =>
    let A := terminalCut c U
    obtain ⟨hsep,hmin⟩ := terminalCut_correct c U hU
    change Separates U A at hsep
    change ∀ T, Separates U T → cutCapacity c A ≤ cutCapacity c T at hmin
    by_cases hodd : OddSide U A
    · have heq : recurse (k+1) c U=A := by
        rw [recurse]
        change (if OddSide U A then A else _)=A
        exact ite_eq_left hodd
      rw [heq]
      exact ⟨hodd,fun S hS => hmin S (odd_separates U S he hS)⟩
    · have heA : Even (A∩U).card := by
        simp only [OddSide,Nat.odd_iff] at hodd
        rw [Nat.even_iff]; omega
      have heB := even_other U A he heA
      obtain ⟨hposA,hposB⟩ := separate_cards U A hsep
      have hpart := terminal_partition U A
      have htwoA : 2≤(A∩U).card := by rw [Nat.even_iff] at heA; omega
      have htwoB : 2≤(Aᶜ∩U).card := by rw [Nat.even_iff] at heB; omega
      have hboundA : (A∩U).card≤k := by omega
      have hboundB : (Aᶜ∩U).card≤k := by omega
      have hnonA : A.Nonempty := by
        obtain ⟨v,hv⟩ := card_pos.mp hposA
        exact ⟨v,(mem_inter.mp hv).1⟩
      have hnonB : Aᶜ.Nonempty := by
        obtain ⟨v,hv⟩ := card_pos.mp hposB
        exact ⟨v,(mem_inter.mp hv).1⟩
      obtain ⟨r,hr,hrA⟩ := outside_some A hnonB
      obtain ⟨q,hq,hqB⟩ := outside_some Aᶜ (by simpa using hnonA)
      let f := contractMap A r
      let g := contractMap Aᶜ q
      let X := recurse k (push c f) (A∩U)
      let Y := recurse k (push c g) (Aᶜ∩U)
      obtain ⟨hX,minX⟩ := ih (push c f) (push_symm c hc f) (A∩U) heA htwoA hboundA
      obtain ⟨hY,minY⟩ := ih (push c g) (push_symm c hc g) (Aᶜ∩U) heB htwoB hboundB
      change OddSide (A∩U) X at hX
      change OddSide (Aᶜ∩U) Y at hY
      have hLX : OddSide U (lift f X) := (odd_lift_iff U A X r heB).2 hX
      have hLY : OddSide U (lift g Y) :=
        (odd_lift_iff U Aᶜ Y q (by simpa using heA)).2 hY
      have heq : recurse (k+1) c U=cheaper c (lift f X) (lift g Y) := by
        rw [recurse]
        change (if OddSide U A then A else _) = _
        rw [ite_eq_right hodd,hr,hq]
      rw [heq]
      refine ⟨cheaper_odd c U _ _ hLX hLY,?_⟩
      intro S hS
      by_cases hSA : OddSide (A∩U) S
      · obtain ⟨T,hTA,hT,hcap⟩ := uncross_on_side c hc U A S hsep heA hmin hSA
        have hchild := (odd_subset_iff U A T hTA).2 hT
        have hminT := minX T hchild
        change cutCapacity (push c f) X ≤ cutCapacity (push c f) T at hminT
        rw [cut_push] at hminT
        rw [show f=contractMap A r from rfl,cut_contract_subset c A T r hrA hTA] at hminT
        exact (cheaper_le_left c _ _).trans (hminT.trans hcap)
      · have hSB := split_odd U S A hS hSA
        have hminB : ∀ T, Separates U T → cutCapacity c Aᶜ ≤ cutCapacity c T := by
          simpa only [cut_compl c hc] using hmin
        obtain ⟨T,hTB,hT,hcap⟩ := uncross_on_side c hc U Aᶜ S
          (separates_compl U A hsep) heB hminB hSB
        have hchild := (odd_subset_iff U Aᶜ T hTB).2 hT
        have hminT := minY T hchild
        change cutCapacity (push c g) Y ≤ cutCapacity (push c g) T at hminT
        rw [cut_push] at hminT
        rw [show g=contractMap Aᶜ q from rfl,cut_contract_subset c Aᶜ T q hqB hTB] at hminT
        exact (cheaper_le_right c _ _).trans (hminT.trans hcap)

def oddCut (c : Fin n → Fin n → ℕ) (U : Finset (Fin n)) : Finset (Fin n) :=
  recurse U.card c U

 theorem oddCut_correct (c : Fin n → Fin n → ℕ) (hc : ∀ i j, c i j=c j i)
    (U : Finset (Fin n)) (he : Even U.card) (hU : 2≤U.card) :
    OddSide U (oddCut c U) ∧
      ∀ S, OddSide U S → cutCapacity c (oddCut c U) ≤ cutCapacity c S :=
  recurse_correct U.card c hc U he hU le_rfl

end BinaryMatching.OddMincut
end

end OAI
