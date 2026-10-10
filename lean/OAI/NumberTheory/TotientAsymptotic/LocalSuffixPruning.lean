import OAI.NumberTheory.TotientAsymptotic.LocalResidualExceptionData
import OAI.NumberTheory.TotientAsymptotic.LocalSuffixAggregation

namespace OAI

/-! Assemble the proved exceptional classes before the surviving Ford
comparison count.  The remaining premise is a finite reciprocal estimate
for the explicitly defined regular witness class. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_suffix_count_of_regular_mass {c : ℝ} (hc : 0 < c)
    (d q : ℕ) (hd : 0 < d) (hqpos : 0 < q) (hq : q.totient=d) (L : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∀ (i : Fin (m x-H)) (F : ℕ → ℕ),
        let R := localBadSuffixValues x c d L H i
        Set.InjOn F (R : Set ℕ) →
        (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
          largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
        (∑ r ∈ localWitnessRegular R F (m x-i.val),(r.totient:ℝ)⁻¹) ≤ rho^(m x-i.val)) →
      (∑ i : Fin (m x-H),((tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card:ℝ)) ≤
        (x/(d*Real.log x))*(C*G x (m x-H))*polynomialGeometricTail 0 rho H := by
  obtain ⟨C,hC,hcount⟩ := local_suffix_count_aggregation_mul hc d hd L 3 (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,local_bad_suffix_exception_data hc d q hd hqpos hq L]
    with H hcount hexcept
  filter_upwards [hcount,hexcept] with x hcount hexcept
  intro hregular
  apply hcount
  intro i
  obtain ⟨F,hinj,hF,hnormal,hsquare⟩ := hexcept i
  have hr := hregular i F hinj hF
  have hp := local_residual_mass_partition (localBadSuffixValues x c d L H i) F (m x-i.val)
  linarith only [hp,hr,hnormal,hsquare]

end TotientAsymptotic

end

end OAI
