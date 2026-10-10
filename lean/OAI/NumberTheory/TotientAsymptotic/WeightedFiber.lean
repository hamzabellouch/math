import OAI.NumberTheory.TotientAsymptotic.CandidateComparison
import OAI.NumberTheory.TotientAsymptotic.WeightedPrimeWindow
import OAI.NumberTheory.TotientAsymptotic.WeightPerturbation

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter
namespace TotientAsymptotic

def prefixCandidateFactor {r : ℕ} (ζ : PrefixDatum r) : ℕ :=
  ell ζ.d*∏ i, ζ.primes i

lemma tupleLeastCandidate_eq_head {r p : ℕ} (ζ : PrefixDatum r) :
    tupleLeastCandidate (TotientTuple.mk p ζ)=p*prefixCandidateFactor ζ := by
  simp only [tupleLeastCandidate,tuplePrimeProduct,tuplePrimes,Fin.prod_univ_succ,
    Fin.cons_zero,Fin.cons_succ,prefixCandidateFactor]
  ring

def candidatePrimeSet (x : ℝ) (H k : ℕ) (ζ : PrefixDatum (R x H)) : Finset ℕ :=
  (shiftedPrimeSet x x (prefixDenominator ζ)).filter (fun p : ℕ =>
    (k : ℝ)*x < (p*prefixCandidateFactor ζ : ℕ) ∧
      (p*prefixCandidateFactor ζ : ℕ) ≤ (k+1 : ℝ)*x)

lemma candidate_fiber_card {x : ℝ} {H k : ℕ} (hPH : P H ≤ H) (hx : 0 ≤ x)
    {ζ : PrefixDatum (R x H)} (hζ : IsPrefixDatum x H ζ) :
    ((candidateTuples x H k).filter (fun τ => τ.tail=ζ)).card=(candidatePrimeSet x H k ζ).card := by
  apply Finset.card_bij (fun τ _ => τ.head)
  · intro τ hτ
    obtain ⟨hτ,htail⟩ := Finset.mem_filter.mp hτ
    obtain ⟨hb,hw⟩ := Finset.mem_filter.mp hτ
    have hb := (mem_tupleFinset hPH).mp hb
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_shiftedPrimeSet hx (basic_prefix_denominator_pos hPH hζ)).mpr
      refine ⟨hb.1,hb.2.1,?_⟩
      have hv := hb.2.2.2
      change ((tupleValue (TotientTuple.mk τ.head τ.tail) : ℕ) : ℝ) ≤ x at hv
      rw [tupleValue_eq_head,htail] at hv
      exact hv
    · have he : τ=TotientTuple.mk τ.head ζ := by cases τ; simp_all
      rw [he] at hw
      simpa only [candidateInWindow,tupleLeastCandidate_eq_head] using hw
  · intro τ hτ σ hσ he
    have ht := (Finset.mem_filter.mp hτ).2
    have hs := (Finset.mem_filter.mp hσ).2
    cases τ
    cases σ
    simp_all
  · intro p hp
    obtain ⟨hp,hw⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hlo,hval⟩ := (mem_shiftedPrimeSet hx (basic_prefix_denominator_pos hPH hζ)).mp hp
    refine ⟨⟨p,ζ⟩,Finset.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_tupleFinset hPH).mpr
      refine ⟨hp,hlo,hζ,?_⟩
      simpa only [tupleValue_eq_head,prefixDenominator] using hval
    · simpa only [candidateInWindow,tupleLeastCandidate_eq_head] using hw

lemma candidate_count_eq_prime_fibers {x : ℝ} {H k : ℕ} (hPH : P H ≤ H) (hx : 0 ≤ x) :
    ((candidateTuples x H k).card : ℝ)=
      ∑ ζ ∈ prefixDataFinset x H, ((candidatePrimeSet x H k ζ).card : ℝ) := by
  have hmap : ∀ τ ∈ candidateTuples x H k, τ.tail ∈ prefixDataFinset x H := by
    intro τ hτ
    exact mem_prefixDataFinset.mpr ((mem_tupleFinset hPH).mp (Finset.mem_filter.mp hτ).1).2.2.1
  have he := Finset.sum_card_fiberwise_eq_card_filter (candidateTuples x H k) (prefixDataFinset x H) TotientTuple.tail
  rw [Finset.filter_eq_self.mpr hmap] at he
  rw [← he,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ζ hζ
  rw [candidate_fiber_card hPH hx (mem_prefixDataFinset.mp hζ)]

end TotientAsymptotic

end

end OAI
