import OAI.NumberTheory.TotientAsymptotic.CollisionHeadSize
import OAI.NumberTheory.TotientAsymptotic.GoodDiscard
import OAI.NumberTheory.TotientAsymptotic.FiniteMap

namespace OAI

/-! Actual arithmetic realization of tuples and the finite-map comparison. -/

noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable

namespace TotientAsymptotic

def wholePreimage {x : ℝ} {H : ℕ} (p : ℕ) (η : RemainderDatum (L x H)) : ℕ :=
  p * suffixPreimage η 0

lemma basic_head_coprime (H : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ p : ℕ, p.Prime → x^(9/10 : ℝ) ≤ p →
    ∀ η : RemainderDatum (L x H), IsBasicRemainder x H η →
      p.Coprime (suffixPreimage η 0) := by
  filter_upwards [basic_remainder_subpower H (show (0 : ℝ)<1/10 by norm_num),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro p hp hpl η hη
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hle := Nat.le_of_dvd (suffixPreimage_pos hη (i := 0)) hd
  have hsmall := (hx η hη).trans_lt
    (Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num : (1/10 : ℝ)<9/10))
  exact (not_lt_of_ge (show (p : ℝ) ≤ suffixPreimage η 0 by exact_mod_cast hle))
    (hsmall.trans_le hpl)

lemma wholePreimage_totient {x : ℝ} {H p : ℕ}
    {η : RemainderDatum (L x H)} (hp : p.Prime) (hη : IsBasicRemainder x H η)
    (hL : L x H < m x) (hR : R x H < L x H)
    (hcop : p.Coprime (suffixPreimage η 0)) :
    (wholePreimage p η).totient = tupleValue (witnessTuple p η) := by
  rw [wholePreimage, Nat.totient_mul hcop, Nat.totient_prime hp,
    witness_tuple_value_at_cut hη hL hR (Nat.zero_lt_of_lt hR)]
  simp only [Finset.Icc_self, Finset.prod_singleton, wholeWitnessPrime, ite_true]
  ring

lemma basic_tuple_isTotient : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ t : ℝ, ∀ τ : TotientTuple (R x H), IsBasicTuple x H t τ → IsTotient (tupleValue τ) := by
  filter_upwards [eventually_tail_cut_separated] with H hH
  obtain ⟨hPH,hP⟩ := hH
  filter_upwards [basic_head_coprime H,m_tendsto.eventually (eventually_ge_atTop H)] with x hx hm
  intro t τ hτ
  obtain ⟨η,hη,he⟩ := (isPrefixDatum_iff x H τ.tail).mp hτ.2.2.1
  have hw : witnessTuple τ.head η=τ := by
    cases τ
    simpa only [witnessTuple,TotientTuple.mk.injEq,true_and] using he
  have hL : L x H < m x := by unfold L; omega
  have hR : R x H < L x H := by unfold R L; omega
  refine ⟨wholePreimage τ.head η,Nat.mul_pos hτ.1.pos (suffixPreimage_pos hη),?_⟩
  rw [wholePreimage_totient hτ.1 hη hL hR (hx τ.head hτ.1 hτ.2.1 η hη),hw]

def totientValues (t : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊t⌋₊).filter IsTotient

def uncoveredValues (x : ℝ) (H : ℕ) (t : ℝ) : Finset ℕ :=
  totientValues t \ (tupleFinset x H t).image tupleValue

lemma card_totientValues (t : ℝ) : ((totientValues t).card : ℝ)=V t := rfl

lemma basic_tuple_mem_values {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) (hval : IsTotient (tupleValue τ)) :
    tupleValue τ ∈ totientValues t := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨basic_tuple_value_pos hPH hτ,Nat.le_floor hτ.2.2.2⟩,hval⟩

lemma good_collision_count_eq {x t : ℝ} {H : ℕ}
    (hmap : ∀ τ ∈ goodTupleFinset x H t, tupleValue τ ∈ totientValues t) :
    FiniteMap.collisionCount (goodTupleFinset x H t) (totientValues t) tupleValue =
      (goodCollisionPairs x H t).card := by
  classical
  rw [FiniteMap.collisionCount_eq_ordered_pairs _ _ _ hmap]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_offDiag,goodCollisionPairs,Finset.mem_product]
  tauto

/-- Both errors are for concrete finite sets: actual bad tuples and actual
uncovered totient values. The coverage error will be bounded by extraction. -/
theorem tuple_value_comparison : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ t : ℝ,
    -((uncoveredValues x H t).card : ℝ) ≤ ((tupleFinset x H t).card : ℝ)-V t ∧
    ((tupleFinset x H t).card : ℝ)-V t ≤
      (badTupleFinset x H t).card+((goodCollisionPairs x H t).card : ℝ)/2 := by
  filter_upwards [basic_tuple_isTotient,eventually_ge_atTop 2] with H hreal hH
  filter_upwards [hreal] with x hx
  intro t
  have hPH := (P_lt_self hH).le
  have hmap : ∀ τ ∈ tupleFinset x H t, tupleValue τ ∈ totientValues t := by
    intro τ hτ
    have hb := (mem_tupleFinset hPH).mp hτ
    exact basic_tuple_mem_values hPH hb (hx t τ hb)
  have hg : goodTupleFinset x H t ⊆ tupleFinset x H t := Finset.filter_subset _ _
  have hpart : tupleFinset x H t=goodTupleFinset x H t ∪ badTupleFinset x H t := by
    exact (Finset.union_sdiff_of_subset hg).symm
  have hdis : Disjoint (goodTupleFinset x H t) (badTupleFinset x H t) :=
    Finset.disjoint_left.mpr (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₂).2 h₁)
  have hc := FiniteMap.counting (tupleFinset x H t) (goodTupleFinset x H t)
    (badTupleFinset x H t) (totientValues t) (uncoveredValues x H t) tupleValue
    hpart hdis hmap (Finset.sdiff_subset) (by
      intro v hv
      by_contra hn
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,hn⟩))
  rw [good_collision_count_eq (fun τ hτ => hmap τ (hg hτ))] at hc
  exact ⟨hc.1,hc.2.1⟩

end TotientAsymptotic

end

end OAI
