import OAI.Computability.MatchingCount.RecursiveEval

namespace OAI

section

namespace BinaryMatching.DenseOracle
open Finset UnitFlow CutAlgebra OddCutParity
variable {n : ℕ}

def total (c : Fin n → Fin n → ℕ) : ℕ := ∑ i, ∑ j, c i j

lemma entry_le_total (c : Fin n → Fin n → ℕ) (i j : Fin n) : c i j≤total c :=
  (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j)).trans
    (single_le_sum (fun x _ => Nat.zero_le (∑ y, c x y)) (mem_univ i))

lemma source_le_total (c : Fin n → Fin n → ℕ) (a : Fin n) :
    UnitMincut.sourceCapacity c a≤total c := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ a)

lemma push_total_le (c : Fin n → Fin n → ℕ) (f : Fin n → Fin n) :
    total (push c f)≤total c := by
  calc
    _ ≤ ∑ i,∑ j,∑ u,∑ v,if f u=i ∧ f v=j then c u v else 0 := by
      apply sum_le_sum; intro i hi
      apply sum_le_sum; intro j hj
      unfold push
      split_ifs
      · exact Nat.zero_le _
      · rfl
    _ = ∑ u,∑ v,∑ i,∑ j,if f u=i ∧ f v=j then c u v else 0 := sum_four_swap _
    _ = total c := by simp [total,ite_and,Finset.sum_ite_irrel,eq_comm]

lemma contract_total_le (c : Matrix n ℕ) (f : Fin n → Fin n) :
    total (view (contract c f))≤total (view c) := by
  rw [contract_view]
  exact push_total_le _ _

lemma feasible_abs_bound (c : Fin n → Fin n → ℕ) (a z : Fin n) (b : UnitFlow.Matrix (Fin n))
    (hb : Feasible c a z b) (i j : Fin n) : (b i j).natAbs≤total c := by
  have hu : b i j≤(total c:ℤ) := (hb.capacity i j).trans (by exact_mod_cast entry_le_total c i j)
  have hl : b j i≤(total c:ℤ) := (hb.capacity j i).trans (by exact_mod_cast entry_le_total c j i)
  rw [hb.antisymm j i] at hl
  have hh : |b i j|≤(total c:ℤ) := abs_le.mpr ⟨by omega,hu⟩
  rw [←Int.natCast_natAbs] at hh
  exact_mod_cast hh

lemma flow_abs_bound (c : Matrix n ℕ) (a z : Fin n) (k : ℕ) (i j : Fin n) :
    (view (iterate c a z k) i j).natAbs≤total (view c) := by
  rw [iterate_view]
  exact feasible_abs_bound _ _ _ _ (UnitMincut.iterate_feasible _ _ _ _) _ _

lemma path_length_bound (c : Matrix n ℕ) (b : Matrix n ℤ) (a : Fin n) (k : ℕ)
    (v : Fin n) (p : List (Fin n)) (hp : (search c b a k)[v]=some p) : p.length≤n := by
  have hs := congrFun (search_view c b a k) v
  change (search c b a k)[v]=_ at hs
  rw [hs] at hp
  have hh := (ResidualSearch.good_search (UnitMincut.residual (view c) (view b)) a k).simple v p hp
  simpa only [Fintype.card_fin] using hh.length_le_card

def calls : ℕ → Matrix n ℕ → Finset (Fin n) → ℕ
  | 0,_,_ => 1
  | k+1,c,U =>
    let A := terminalCut c U
    if OddSide U A then 1 else
      match OddMincut.outside A, OddMincut.outside Aᶜ with
      | some r,some q =>
        1+calls k (contract c (contractMap A r)) (A∩U)+
          calls k (contract c (contractMap Aᶜ q)) (Aᶜ∩U)
      | _,_ => 1

lemma calls_bound (fuel : ℕ) (c : Matrix n ℕ) (U : Finset (Fin n))
    (he : Even U.card) (hU : 2≤U.card) (hbound : U.card≤fuel) :
    calls fuel c U≤U.card-1 := by
  induction fuel generalizing c U with
  | zero => omega
  | succ k ih =>
    let A := terminalCut c U
    obtain ⟨hsep,_⟩ := TerminalMincut.terminalCut_correct (view c) U hU
    rw [←terminalCut_eq] at hsep
    change TerminalMincut.Separates U A at hsep
    by_cases hodd : OddSide U A
    · have hcall : calls (k+1) c U=1 := by
        rw [calls]
        change (if OddSide U A then 1 else _)=1
        exact ite_eq_left hodd
      rw [hcall]; omega
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
      rw [calls]
      change (if OddSide U A then 1 else _ )≤_
      rw [ite_eq_right hodd]
      split
      · rename_i r q hr hq
        have h₁ := ih (contract c (contractMap A r)) (A∩U) heA htwoA hboundA
        have h₂ := ih (contract c (contractMap Aᶜ q)) (Aᶜ∩U) heB htwoB hboundB
        change 1+calls k (contract c (contractMap A r)) (A∩U)+
          calls k (contract c (contractMap Aᶜ q)) (Aᶜ∩U)≤U.card-1
        omega
      · omega

lemma initial_total_bound (G : Input) (j : ℕ) :
    total (Algorithm.capacities (Algorithm.iterate G j).numerators)≤G.n^2*Algorithm.D₀ G := by
  have hh (i k : Fin G.n) : Algorithm.capacities (Algorithm.iterate G j).numerators i k≤Algorithm.D₀ G := by
    unfold Algorithm.capacities
    split_ifs with hik hki
    · have hb := (Algorithm.iterate_box G j ⟨(i,k),hik⟩).2
      exact Int.toNat_le.mpr (by simpa only [Algorithm.entry] using hb)
    · have hb := (Algorithm.iterate_box G j ⟨(k,i),hki⟩).2
      exact Int.toNat_le.mpr (by simpa only [Algorithm.entry] using hb)
    · exact Nat.zero_le _
  calc
    _ ≤ ∑ _i : Fin G.n,∑ _k : Fin G.n,Algorithm.D₀ G :=
      sum_le_sum fun i _ => sum_le_sum fun k _ => hh i k
    _ = _ := by simp; ring

end BinaryMatching.DenseOracle
end

end OAI
