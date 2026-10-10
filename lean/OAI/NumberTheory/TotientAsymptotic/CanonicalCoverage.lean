import OAI.NumberTheory.TotientAsymptotic.FordHead
import OAI.NumberTheory.TotientAsymptotic.ValueOmega

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

/-- The exact coverage statement once the three explicit exceptional
conditions (structure, largest prime, cofactor) have been excluded. -/
lemma canonical_tuple_coverage {x t : ℝ} {H n : ℕ} (hPH : P H < H) (hP : 1 ≤ P H)
    (hm : H ≤ m x) (hn : 0<n)
    (hstruct : extractedStructureCondition x (P H) n)
    (hhead : x^(9/10 : ℝ) ≤ fordPrime n 0)
    (hsize : Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)))
    (hval : (n.totient : ℝ) ≤ t)
    (hcop : (fordPrime n 0).Coprime (suffixPreimage (fordRemainder x H n) 0)) :
    n.totient ∈ (tupleFinset x H t).image tupleValue := by
  have hL : 0<L x H := by unfold L; omega
  have hLm : L x H< m x := by unfold L; omega
  have hRL : R x H<L x H := by unfold R L; omega
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hstruct.2.1)
  have hp := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  let η := fordRemainder x H n
  let p := fordPrime n 0
  have hη : IsBasicRemainder x H η := fordRemainder_basic hL hstruct hsize
  have he : tupleValue (witnessTuple p η)=n.totient := by
    rw [← wholePreimage_totient hp hη hLm hRL hcop,fordRemainder_factorization hn hindex]
  have ht : IsBasicTuple x H t (witnessTuple p η) :=
    ⟨hp,hhead,(isPrefixDatum_iff x H _).mpr ⟨η,hη,rfl⟩,he.symm ▸ hval⟩
  exact Finset.mem_image.mpr ⟨witnessTuple p η,(mem_tupleFinset hPH.le).mpr ht,he⟩

/-- The coprimality premise is automatically available uniformly for actual
basic remainders once the head lower bound and cofactor cutoff hold. -/
theorem canonical_tuple_coverage_eventually {H : ℕ} (hPH : P H < H) (hP : 1≤P H) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ, 0<n →
      extractedStructureCondition x (P H) n → x^(9/10 : ℝ) ≤ fordPrime n 0 →
      Real.log (fordCofactor n (L x H+1) : ℝ) ≤ Real.exp (2*bandScale x (L x H)) →
      (n.totient : ℝ) ≤ t → n.totient ∈ (tupleFinset x H t).image tupleValue := by
  filter_upwards [basic_head_coprime H,m_tendsto.eventually (eventually_ge_atTop H)] with x hc hm
  intro t n hn hs hp ha hv
  have hL : 0<L x H := by unfold L; omega
  have hindex := fordPrime_index_of_doubleLog_pos (lt_trans (by norm_num) hs.2.1)
  have hprime := fordPrime_prime (show 0<n.primeFactorsList.length by omega)
  exact canonical_tuple_coverage hPH hP hm hn hs hp ha hv
    (hc _ hprime hp _ (fordRemainder_basic hL hs ha))

end TotientAsymptotic

end

end OAI
