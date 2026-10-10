import OAI.NumberTheory.TotientAsymptotic.BasicExceptionCount
import OAI.NumberTheory.TotientAsymptotic.PrefixPreimage

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def exceptionalTotients (x : ℝ) (H : ℕ) : Finset ℕ :=
  totientValues x ∩ basicExceptionValues x H

def nonuniqueValues (x : ℝ) (H : ℕ) : Finset ℕ :=
  FiniteMap.badValues (goodTupleFinset x H x) (badTupleFinset x H x)
    (totientValues x) (exceptionalTotients x H) tupleValue

def discardedTuples (x : ℝ) (H : ℕ) : Finset (TotientTuple (R x H)) :=
  FiniteMap.badPreimages (tupleFinset x H x) (goodTupleFinset x H x)
    (badTupleFinset x H x) (totientValues x) (exceptionalTotients x H) tupleValue

lemma unique_prefix_finite_comparison : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ((nonuniqueValues x H).card : ℝ) ≤ (basicExceptionValues x H).card+
      (badTupleFinset x H x).card+((goodCollisionPairs x H x).card : ℝ)/2 ∧
    ((discardedTuples x H).card : ℝ) ≤ (basicExceptionValues x H).card+
      2*(badTupleFinset x H x).card+(goodCollisionPairs x H x).card ∧
    Set.BijOn (fun τ : TotientTuple (R x H) => tupleValue τ) (↑(tupleFinset x H x \ discardedTuples x H))
      (↑(totientValues x \ nonuniqueValues x H)) := by
  filter_upwards [basic_tuple_isTotient,eventually_ge_atTop 2,
    P_tendsto.eventually (eventually_ge_atTop 1)] with H hreal hH hP
  filter_upwards [hreal,uncovered_values_subset (P_lt_self hH) hP] with x hx hcover
  have hPH := (P_lt_self hH).le
  have hmap : ∀ τ ∈ tupleFinset x H x, tupleValue τ ∈ totientValues x := by
    intro τ hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    exact basic_tuple_mem_values hPH hb (hx x τ hb)
  have hg : goodTupleFinset x H x ⊆ tupleFinset x H x := Finset.filter_subset _ _
  have hpart : tupleFinset x H x=goodTupleFinset x H x ∪ badTupleFinset x H x :=
    (Finset.union_sdiff_of_subset hg).symm
  have hdis : Disjoint (goodTupleFinset x H x) (badTupleFinset x H x) :=
    Finset.disjoint_left.mpr (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₂).2 h₁)
  have hcov : totientValues x \ exceptionalTotients x H ⊆ (tupleFinset x H x).image tupleValue := by
    intro v hv
    obtain ⟨hv,he⟩ := Finset.mem_sdiff.mp hv
    by_contra hn
    have hexc := hcover x le_rfl (Finset.mem_sdiff.mpr ⟨hv,hn⟩)
    exact he (Finset.mem_inter.mpr ⟨hv,hexc⟩)
  have hc := FiniteMap.counting (tupleFinset x H x) (goodTupleFinset x H x)
    (badTupleFinset x H x) (totientValues x) (exceptionalTotients x H) tupleValue
    hpart hdis hmap Finset.inter_subset_left hcov
  rw [good_collision_count_eq (fun τ hτ => hmap τ (hg hτ))] at hc
  have he : ((exceptionalTotients x H).card : ℝ) ≤ (basicExceptionValues x H).card := by
    exact_mod_cast Finset.card_le_card (show exceptionalTotients x H ⊆ basicExceptionValues x H from Finset.inter_subset_right)
  exact ⟨hc.2.2.1.trans (by linarith),hc.2.2.2.1.trans (by linarith),hc.2.2.2.2⟩

/-- All inverse images of an ordinary value have the same displayed prime
prefix. This uses all-preimage extraction, not merely existence of a witness. -/
lemma common_prefix_inverse_fiber {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop,
    ∀ τ ∈ tupleFinset x H x \ discardedTuples x H,
    (Set.InjOn (fun σ : TotientTuple (R x H) => tupleValue σ) (↑(tupleFinset x H x \ discardedTuples x H))) →
    tupleValue τ ∈ totientValues x \ nonuniqueValues x H →
    ∀ n : ℕ, 0 < n → n.totient=tupleValue τ →
      ∃ w : ℕ, 0 < w ∧ w.totient=τ.tail.d ∧ n=tuplePrimeProduct τ*w := by
  filter_upwards [all_preimages_tuple_value hPH hP,all_preimages_basic hPH hP,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hval hbasic hm
  intro τ hτ hinj hv n hn hnv
  have hE : tupleValue τ ∉ basicExceptionValues x H := by
    intro he
    apply (Finset.mem_sdiff.mp hv).2
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1,he⟩
  have hσ := hval _ (Finset.mem_sdiff.mp hv).1 hE n hn hnv
  have hσout : witnessTuple (fordPrime n 0) (fordRemainder x H n) ∈
      tupleFinset x H x \ discardedTuples x H := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hσ.1,?_⟩
    intro h
    have hb := (Finset.mem_filter.mp h).2
    rw [hσ.2] at hb
    exact (Finset.mem_sdiff.mp hv).2 hb
  have heq := hinj hσout hτ hσ.2
  obtain ⟨hbt,hfact⟩ := hbasic _ (Finset.mem_sdiff.mp hv).1 hE n hn hnv
  have hη : IsBasicRemainder x H (fordRemainder x H n) := by
    have hsout : tupleValue τ ∉ preimageExceptionValues x (extractedStructureCondition x (P H)) := by
      intro h
      exact hE (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hs := (outside_preimageExceptions_iff (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1).mp hsout n hn hnv
    have ha : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
      apply le_of_not_gt
      intro h
      exact hE (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1,n,hn,hnv,hs,hbt.2.1,h⟩)))
    exact fordRemainder_basic (by unfold L; omega) hs ha
  refine ⟨remainderTail x H (fordRemainder x H n),suffixPreimage_pos (i := R x H) hη,?_,?_⟩
  · have hh := congrArg (fun σ : TotientTuple (R x H) => σ.tail.d) heq
    exact hh
  · calc
      n = wholePreimage (fordPrime n 0) (fordRemainder x H n) := hfact.symm
      _ = _ := by rw [wholePreimage_prefix_split _ _ (by unfold R L; omega),heq]

end TotientAsymptotic

end

end OAI
