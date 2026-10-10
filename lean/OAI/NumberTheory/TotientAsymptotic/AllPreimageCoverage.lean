import OAI.NumberTheory.TotientAsymptotic.ValueCoverage

namespace OAI

/-! Uniform arithmetic extraction for every preimage outside explicit exceptional values. -/

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def basicExceptionValues (x : ℝ) (H : ℕ) : Finset ℕ :=
  (preimageExceptionValues x (extractedStructureCondition x (P H)) ∪ smallValues x) ∪
    (largeOmegaValues x ∪ cofactorExceptionValues x H)

lemma all_preimages_basic {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop, ∀ v ∈ totientValues x, v ∉ basicExceptionValues x H →
    ∀ n : ℕ, 0 < n → n.totient = v →
      IsBasicTuple x H x (witnessTuple (fordPrime n 0) (fordRemainder x H n)) ∧
      wholePreimage (fordPrime n 0) (fordRemainder x H n) = n := by
  filter_upwards [basic_head_coprime H,extracted_head_large,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_ge_atTop (0 : ℝ)] with x hcop hhead hm hx0
  intro v hv hout n hn hnv
  have houts : v ∉ preimageExceptionValues x (extractedStructureCondition x (P H)) ∧
      v ∉ smallValues x ∧ v ∉ largeOmegaValues x ∧ v ∉ cofactorExceptionValues x H := by
    simpa only [basicExceptionValues,Finset.mem_union,not_or,and_assoc] using hout
  obtain ⟨hvr,hvφ⟩ := Finset.mem_filter.mp hv
  have hs := (outside_preimageExceptions_iff hvr).mp houts.1 n hn hnv
  have hvpos := (Finset.mem_Icc.mp hvr).1
  have hlow : x^(19/20 : ℝ) ≤ (v : ℝ) := by
    apply le_of_not_gt
    intro h
    exact houts.2.1 (Finset.mem_Icc.mpr ⟨hvpos,Nat.le_floor h.le⟩)
  have hΩ : (v.primeFactorsList.length : ℝ) ≤ 20*B x := by
    apply le_of_not_gt
    intro h
    exact houts.2.2.1 (Finset.mem_filter.mpr ⟨hvr,h⟩)
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H < m x := by unfold L; omega
  have hRL : R x H < L x H := by unfold R L; omega
  have hp := hhead H n hL hn hs (hnv.symm ▸ hlow) (hnv.symm ▸ hΩ)
  have hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
    apply le_of_not_gt
    intro h
    exact houts.2.2.2 (Finset.mem_filter.mpr ⟨hv,n,hn,hnv,hs,hp,h⟩)
  have hη := fordRemainder_basic hL hs hsize
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hs.2.1)
  have hprime := fordPrime_prime (show 0 < n.primeFactorsList.length by omega)
  have hfact := fordRemainder_factorization hn hindex
  refine ⟨⟨hprime,hp,(isPrefixDatum_iff x H _).mpr ⟨_,hη,rfl⟩,?_⟩,hfact⟩
  rw [← wholePreimage_totient hprime hη hLm hRL (hcop _ hprime hp _ hη),hfact,hnv]
  exact (Nat.le_floor_iff hx0).mp (Finset.mem_Icc.mp hvr).2

/-- Every preimage of an ordinary value induces a tuple with that exact value. -/
lemma all_preimages_tuple_value {H : ℕ} (hPH : P H < H) (hP : 1 ≤ P H) :
    ∀ᶠ x : ℝ in atTop, ∀ v ∈ totientValues x, v ∉ basicExceptionValues x H →
    ∀ n : ℕ, 0 < n → n.totient = v →
      witnessTuple (fordPrime n 0) (fordRemainder x H n) ∈ tupleFinset x H x ∧
      tupleValue (witnessTuple (fordPrime n 0) (fordRemainder x H n)) = v := by
  filter_upwards [all_preimages_basic hPH hP,basic_head_coprime H,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hb hc hm
  intro v hv he n hn hnv
  obtain ⟨ht,hfact⟩ := hb v hv he n hn hnv
  have hη : IsBasicRemainder x H (fordRemainder x H n) := by
    have hout : v ∉ cofactorExceptionValues x H := by
      intro h
      exact he (Finset.mem_union_right _ (Finset.mem_union_right _ h))
    have hvr := (Finset.mem_filter.mp hv).1
    have hstout : v ∉ preimageExceptionValues x (extractedStructureCondition x (P H)) := by
      intro h
      exact he (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hs := (outside_preimageExceptions_iff hvr).mp hstout n hn hnv
    have hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) := by
      apply le_of_not_gt
      intro h
      exact hout (Finset.mem_filter.mpr ⟨hv,n,hn,hnv,hs,ht.2.1,h⟩)
    exact fordRemainder_basic (by unfold L; omega) hs hsize
  refine ⟨(mem_tupleFinset hPH.le).mpr ht,?_⟩
  rw [← wholePreimage_totient (p := fordPrime n 0) ht.1 hη (by unfold L; omega)
    (by unfold R L; omega) (hc _ ht.1 ht.2.1 _ hη),hfact,hnv]

end TotientAsymptotic

end

end OAI
