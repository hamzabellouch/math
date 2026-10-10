import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellCatalogProgram
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeCandidates

namespace OAI

/-! # Polynomial enumeration of exchanges of a binary profile

The program scans at most the square of the list length. It retains only
an absent receiving coordinate and a present donating coordinate, so every
retained natural-number update is again a binary profile.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

def binaryExchangeTest (z : List ℕ×(ℕ×ℕ)) : Bool :=
  decide (z.1.getD z.2.1 0=0 ∧ z.1.getD z.2.2 0=1)

def binaryExchangeTestRealizer : Realizer binaryExchangeTest := by
  let V : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.1) := first
  let I : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.2.1) := composition second first
  let J : Realizer (fun z : List ℕ×(ℕ×ℕ) => z.2.2) := composition second second
  let absent := composition (pair (composition (pair V I) (getDFast 0)) (constant 0)) natEqual
  let present := composition (pair (composition (pair V J) (getDFast 0)) (constant 1)) natEqual
  exact (choose absent present (constant false)).congr (by
    intro z
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,binaryExchangeTest,decide_eq_true_eq]
    split_ifs <;> simp_all)

theorem polynomial_binaryExchangeTest : PolynomialTime binaryExchangeTestRealizer := by
  unfold binaryExchangeTestRealizer
  apply polynomial_congr
  apply polynomial_choose
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast 0))
      (polynomial_constant 0)) polynomial_natEqual
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0))
      (polynomial_constant 1)) polynomial_natEqual
  · exact polynomial_constant false

def binaryExchangeIndices (xs : List ℕ) : List (ℕ×ℕ) :=
  (cellPairs (xs,xs)).filter (fun ij => binaryExchangeTest (xs,ij))

def binaryExchangeIndicesRealizer : Realizer binaryExchangeIndices :=
  composition (pair identity (composition (pair identity identity) cellPairsRealizer))
    (filterWith binaryExchangeTestRealizer)

theorem polynomial_binaryExchangeIndices : PolynomialTime binaryExchangeIndicesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_binaryExchangeTest)

theorem mem_binaryExchangeIndices (xs : List ℕ) (i j : ℕ) :
    (i,j)∈binaryExchangeIndices xs ↔
      i<xs.length ∧ j<xs.length ∧ xs.getD i 0=0 ∧ xs.getD j 0=1 := by
  simp only [binaryExchangeIndices,List.mem_filter,mem_cellPairs,binaryExchangeTest,
    decide_eq_true_eq]
  tauto

lemma cellPairs_nodup (xs ys : List ℕ) : (cellPairs (xs,ys)).Nodup := by
  apply List.Nodup.map_on _ List.nodup_range
  intro a _ b _ he
  have hq := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  dsimp only [pairAt] at hq hr
  calc
    a = a%ys.length+ys.length*(a/ys.length) := (Nat.mod_add_div a ys.length).symm
    _ = b%ys.length+ys.length*(b/ys.length) := by rw [hq,hr]
    _ = b := Nat.mod_add_div b ys.length

theorem binaryExchangeIndices_nodup (xs : List ℕ) : (binaryExchangeIndices xs).Nodup :=
  (cellPairs_nodup xs xs).filter _

def binaryExchanges (xs : List ℕ) : List (List ℕ) :=
  (binaryExchangeIndices xs).map (fun ij => listExchange (xs,ij))

def binaryExchangesRealizer : Realizer binaryExchanges :=
  composition (pair identity binaryExchangeIndicesRealizer) (mapWith listExchangeRealizer)

theorem polynomial_binaryExchanges : PolynomialTime binaryExchangesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_binaryExchangeIndices)
    (polynomial_mapWith polynomial_listExchange)

noncomputable def setProfile {n : ℕ} (S : Set (Fin n)) : Fin n → ℕ :=
  fun i => if i∈S then 1 else 0

lemma setProfile_injective {n : ℕ} : Function.Injective (setProfile (n := n)) := by
  intro S T he
  ext i
  have hi := congrFun he i
  by_cases hs : i∈S <;> by_cases ht : i∈T <;> simp_all [setProfile]

/-- On an absent/present coordinate pair, the natural update is exactly
set removal followed by set insertion. -/
theorem exchange_setProfile {n : ℕ} (S : Set (Fin n)) (i j : Fin n)
    (hi : i∉S) (hj : j∈S) :
    IntegerWeightedTransport.exchangeTarget (setProfile S) i j=
      setProfile (insert i (S\{j})) := by
  have hij : i≠j := fun he => hi (he ▸ hj)
  funext a
  by_cases hai : a=i
  · subst a
    simp [IntegerWeightedTransport.exchangeTarget,setProfile,hi,hij]
  · by_cases haj : a=j
    · subst a
      simp [IntegerWeightedTransport.exchangeTarget,setProfile,hj,hai]
    · by_cases ha : a∈S <;>
        simp [IntegerWeightedTransport.exchangeTarget,setProfile,hai,haj,ha]

/-- Every program output is a genuine binary exchange, and all such
exchanges are listed. No enumeration of the set of states is involved. -/
theorem mem_binaryExchanges_setProfile {n : ℕ} (S : Set (Fin n)) (ys : List ℕ) :
    ys∈binaryExchanges (List.ofFn (setProfile S)) ↔
      ∃ i j : Fin n,i∉S ∧ j∈S ∧ ys=List.ofFn (setProfile (insert i (S\{j}))) := by
  simp only [binaryExchanges,List.mem_map]
  constructor
  · rintro ⟨⟨i,j⟩,hij,rfl⟩
    have h := (mem_binaryExchangeIndices _ i j).mp hij
    have hi : i<n := by simpa only [List.length_ofFn] using h.1
    have hj : j<n := by simpa only [List.length_ofFn] using h.2.1
    let a : Fin n := ⟨i,hi⟩
    let b : Fin n := ⟨j,hj⟩
    have hget (k : Fin n) : (List.ofFn (setProfile S)).getD k.val 0=setProfile S k := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
      simp only [Option.getD_some,List.getElem_ofFn]
    have ha : a∉S := by
      have hh := h.2.2.1
      rw [hget a] at hh
      intro ha
      simp [setProfile,ha] at hh
    have hb : b∈S := by
      have hh := h.2.2.2
      rw [hget b] at hh
      by_contra hn
      simp [setProfile,hn] at hh
    refine ⟨a,b,ha,hb,?_⟩
    exact (listExchange_ofFn (setProfile S) a b).trans
      (congrArg List.ofFn (exchange_setProfile S a b ha hb))
  · rintro ⟨i,j,hi,hj,rfl⟩
    refine ⟨(i.val,j.val),?_,?_⟩
    · apply (mem_binaryExchangeIndices _ _ _).mpr
      refine ⟨by simp,by simp,?_,?_⟩ <;>
        simp [List.getD_eq_getElem?_getD,setProfile,hi,hj]
    · exact ((listExchange_ofFn (setProfile S) i j).trans
        (congrArg List.ofFn (exchange_setProfile S i j hi hj)))

lemma getD_setProfile {n : ℕ} (S : Set (Fin n)) (i : Fin n) :
    (List.ofFn (setProfile S)).getD i.val 0=setProfile S i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some,List.getElem_ofFn]

lemma binaryIndex_specs {n : ℕ} (S : Set (Fin n)) (ij : ℕ×ℕ)
    (h : ij∈binaryExchangeIndices (List.ofFn (setProfile S))) :
    ∃ i j : Fin n,ij=(i.val,j.val) ∧ i∉S ∧ j∈S := by
  have hh := (mem_binaryExchangeIndices _ ij.1 ij.2).mp h
  have hi : ij.1<n := by simpa only [List.length_ofFn] using hh.1
  have hj : ij.2<n := by simpa only [List.length_ofFn] using hh.2.1
  let i : Fin n := ⟨ij.1,hi⟩
  let j : Fin n := ⟨ij.2,hj⟩
  refine ⟨i,j,rfl,?_,?_⟩
  · intro hm
    have he := hh.2.2.1
    rw [getD_setProfile S i] at he
    simp [setProfile,hm] at he
  · by_contra hm
    have he := hh.2.2.2
    rw [getD_setProfile S j] at he
    simp [setProfile,hm] at he

/-- Distinct eligible coordinate pairs give distinct binary profiles. -/
theorem binaryExchanges_nodup {n : ℕ} (S : Set (Fin n)) :
    (binaryExchanges (List.ofFn (setProfile S))).Nodup := by
  apply (binaryExchangeIndices_nodup _).map_on
  intro a ha b hb he
  obtain ⟨i,j,rfl,hi,hj⟩ := binaryIndex_specs S a ha
  obtain ⟨u,v,rfl,hu,hv⟩ := binaryIndex_specs S b hb
  rw [listExchange_ofFn,listExchange_ofFn,exchange_setProfile S i j hi hj,
    exchange_setProfile S u v hu hv] at he
  have hs := setProfile_injective (List.ofFn_injective he)
  change CommonBasesFPRAS.exchangedSet S (⟨j,hj⟩,⟨i,hi⟩)=
    CommonBasesFPRAS.exchangedSet S (⟨v,hv⟩,⟨u,hu⟩) at hs
  have hp := CommonBasesFPRAS.exchangedSet_injective S hs
  have h1 : i=u := congrArg (fun a : CommonBasesFPRAS.ExchangeChoice S => a.2.val) hp
  have h2 : j=v := congrArg (fun a : CommonBasesFPRAS.ExchangeChoice S => a.1.val) hp
  subst u
  subst v
  rfl

end ContingencyTables.ProfilePrograms

end OAI
