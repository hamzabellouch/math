import OAI.NumberTheory.TotientAsymptotic.LocalRegularReciprocalMass
import OAI.NumberTheory.TotientAsymptotic.LocalFullCandidateCount

namespace OAI

/-! Apply the dyadic integration bridge to the actual suffix value sets. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_suffix_regular_of_layer_counts {c : ℝ} (hc : 0<c)
    (d : ℕ) (hd : 0<d) (L : ℕ) :
    ∃ A : ℝ,0<A ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∀ (i : Fin (m x-H)) (F : ℕ → ℕ),
        let R := localBadSuffixValues x c d L H i
        Set.InjOn F (R : Set ℕ) →
        (∀ r∈R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r∣F r ∧
          largestPrimeFactor (F r)≠largestPrimeFactor r) →
        let Q := localWitnessRegular R F (m x-i.val)
        ∀ k∈Finset.Icc 1 (discardExponent (localPrimeHeight A L (m x-i.val))),
          (Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).Nonempty →
          ((Q.filter (fun r => Nat.clog 2 (d*r.totient)=k)).card:ℝ) ≤
            (2:ℝ)^k/Real.log ((2:ℝ)^k)*(B ((2:ℝ)^k))^(-4:ℝ)) →
      LocalSuffixRegularBound x c d L H := by
  obtain ⟨A,hA,hvalues⟩ := local_bad_suffix_value_bounds hc d hd
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hA' : 0<A+Real.log d+2 := by
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp
    (local_residual_mass_of_fourth_power_count (half_pos hc) hA' d L)
  refine ⟨A+Real.log d+2,hA',?_⟩
  filter_upwards [hvalues L,eventually_ge_atTop H₀] with H hvalues hH
  filter_upwards [hvalues] with x hvalues
  intro hcounts i F
  dsimp only
  intro hinj hF
  have hhi : H₀ ≤ m x-i.val := by have := i.isLt; omega
  apply hH₀ _ hhi (localWitnessRegular (localBadSuffixValues x c d L H i) F (m x-i.val))
  · intro r hr
    have hrR := (Finset.mem_sdiff.mp hr).1
    obtain ⟨hu,p,hp,hpv,hgeo⟩ := hvalues i r hrR
    exact ⟨p,hp,hpv,hgeo,hu⟩
  · exact hcounts i F hinj hF

end TotientAsymptotic

end

end OAI
