import OAI.NumberTheory.TotientAsymptotic.SurvivingCollision

namespace OAI

/-! Canonical basic witnesses for distinct good tuples and their first differing prime. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def chosenRemainder (x : ℝ) (H : ℕ) (ζ : PrefixDatum (R x H)) : RemainderDatum (L x H) :=
  if h : IsPrefixDatum x H ζ then Classical.choose ((isPrefixDatum_iff x H ζ).mp h)
  else ⟨fun _ => 1,1⟩

lemma chosenRemainder_spec {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hζ : IsPrefixDatum x H ζ) :
    IsBasicRemainder x H (chosenRemainder x H ζ) ∧
      prefixOfRemainder x H (chosenRemainder x H ζ)=ζ := by
  unfold chosenRemainder
  rw [dite_eq_left hζ]
  exact Classical.choose_spec ((isPrefixDatum_iff x H ζ).mp hζ)

lemma chosenRemainder_tuple {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hτ : IsBasicTuple x H t τ) : witnessTuple τ.head (chosenRemainder x H τ.tail)=τ := by
  have he := (chosenRemainder_spec hτ.2.2.1).2
  cases τ
  simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he

lemma chosenRemainder_good {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hτ : IsGoodTuple x H t τ) : GoodWitnessConditions τ.head (chosenRemainder x H τ.tail) :=
  hτ.2 _ (chosenRemainder_spec hτ.1.2.2.1).1 (chosenRemainder_spec hτ.1.2.2.1).2

lemma wholeWitnessPrime_tuple {x : ℝ} {H : ℕ} {p : ℕ}
    {η : RemainderDatum (L x H)} (j : Fin (R x H+1)) :
    wholeWitnessPrime p η j.val=tuplePrimes (witnessTuple p η) j := by
  refine Fin.cases ?_ (fun r => ?_) j
  · simp [wholeWitnessPrime,tuplePrimes,witnessTuple]
  · simp [wholeWitnessPrime,tuplePrimes,witnessTuple,prefixOfRemainder]

lemma chosen_collision_first {x t : ℝ} {H : ℕ} {τ σ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) (hσ : IsBasicTuple x H t σ)
    (hv : tupleValue τ=tupleValue σ) (hne : τ ≠ σ) :
    ∃ i ≤ R x H,
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) i ≠
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) i ∧
      ∀ j < i, wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j =
        wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j := by
  obtain ⟨i,hi,hcommon⟩ := basic_collision_first_difference hPH hτ hv hne
  have heτ (j : Fin (R x H+1)) :
      wholeWitnessPrime τ.head (chosenRemainder x H τ.tail) j.val=tuplePrimes τ j := by
    rw [wholeWitnessPrime_tuple,chosenRemainder_tuple hτ]
  have heσ (j : Fin (R x H+1)) :
      wholeWitnessPrime σ.head (chosenRemainder x H σ.tail) j.val=tuplePrimes σ j := by
    rw [wholeWitnessPrime_tuple,chosenRemainder_tuple hσ]
  refine ⟨i.val,by have := i.isLt; omega,?_,?_⟩
  · simpa only [heτ,heσ] using hi
  · intro j hj
    let j' : Fin (R x H+1) := ⟨j,by have := i.isLt; omega⟩
    exact (heτ j').trans ((hcommon j' hj).trans (heσ j').symm)

def goodCollisionPairs (x : ℝ) (H : ℕ) (t : ℝ) :
    Finset (TotientTuple (R x H) × TotientTuple (R x H)) :=
  ((goodTupleFinset x H t) ×ˢ (goodTupleFinset x H t)).filter
    (fun q => q.1 ≠ q.2 ∧ tupleValue q.1=tupleValue q.2)

/-- All the qualitative comparison data are extracted from the actual
finite collision set, with the universal good-witness condition preserved. -/
theorem good_collision_surviving_identity {x t : ℝ} {H : ℕ}
    (hPH : P H < H) (hP : 1 ≤ P H) (hHm : H ≤ m x)
    (hind : ∀ i ≤ R x H, i+collisionCutoff (m x-i) < L x H)
    {τ σ : TotientTuple (R x H)} (hq : (τ,σ) ∈ goodCollisionPairs x H t) :
    ∃ i ≤ R x H,
      0 < (collisionSurvivors τ.head σ.head (chosenRemainder x H τ.tail)
        (chosenRemainder x H σ.tail) i (collisionLastIndex x i)).card ∧
      (collisionSurvivors τ.head σ.head (chosenRemainder x H τ.tail)
        (chosenRemainder x H σ.tail) i (collisionLastIndex x i)).card ≤
        collisionCutoff (m x-i)+1 ∧
      (collisionResidual (chosenRemainder x H τ.tail) i)*
        shiftedProduct (survivingPair τ.head σ.head (chosenRemainder x H τ.tail)
          (chosenRemainder x H σ.tail) i (collisionLastIndex x i)).left =
      (collisionResidual (chosenRemainder x H σ.tail) i)*
        shiftedProduct (survivingPair τ.head σ.head (chosenRemainder x H τ.tail)
          (chosenRemainder x H σ.tail) i (collisionLastIndex x i)).right := by
  obtain ⟨hpairs,hne,hv⟩ := Finset.mem_filter.mp hq
  obtain ⟨hτ,hσ⟩ := Finset.mem_product.mp hpairs
  have ht := (mem_goodTupleFinset hPH.le).mp hτ
  have hs := (mem_goodTupleFinset hPH.le).mp hσ
  obtain ⟨i,hi,hfirst,hcommon⟩ := chosen_collision_first hPH.le ht.1 hs.1 hv hne
  let η := chosenRemainder x H τ.tail
  let ξ := chosenRemainder x H σ.tail
  have hη := (chosenRemainder_spec ht.1.2.2.1).1
  have hξ := (chosenRemainder_spec hs.1.2.2.1).1
  have hik : i ≤ collisionLastIndex x i := Nat.le_add_right _ _
  have hk : collisionLastIndex x i < L x H := hind i hi
  refine ⟨i,hi,(survivingIndex_first hik hfirst).choose,?_,?_⟩
  · have hsub : collisionSurvivors τ.head σ.head η ξ i (collisionLastIndex x i) ⊆
        Finset.Icc i (collisionLastIndex x i) := Finset.filter_subset _ _
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hh
    have hn : collisionLastIndex x i+1-i=collisionCutoff (m x-i)+1 := by
      unfold collisionLastIndex
      omega
    simpa only [hn] using hh
  · have he := surviving_collision_identity hη hξ ht.1.1 (by unfold L; omega)
      (by unfold R L; omega) hk hik
      (by simpa only [chosenRemainder_tuple ht.1,chosenRemainder_tuple hs.1] using hv)
      hfirst hcommon
    exact he

end TotientAsymptotic

end

end OAI
