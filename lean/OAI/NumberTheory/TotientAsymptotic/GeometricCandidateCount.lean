import OAI.NumberTheory.TotientAsymptotic.GeometricSuffixMass
import OAI.NumberTheory.TotientAsymptotic.CandidateUpperCount
import OAI.NumberTheory.TotientAsymptotic.LocalPrimeGrid
import OAI.NumberTheory.TotientAsymptotic.TailProductBounds

namespace OAI

/-! Count original heads before summing any bad residual suffixes. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_suffix_candidate_count {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ,0 < C ∧ ∀ L : ℕ,∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ n : ℕ,∀ _hn : n ≤ m x-H,
      ∀ (Q : Finset (Fin (m x-H) → ℕ))
        (T : Finset (Fin (m x-H-n) → ℕ)),
        Q ⊆ gridPrimeTuples (localPrimeGrid x c L (m x-H)) →
        (∀ p ∈ T,(∀ i,(p i).Prime) ∧ StrictAnti p) →
        (∀ p ∈ Q,primeFinal p n ∈ T) →
      ((tailHeadPairs x d Q).card:ℝ) ≤
        (x/(d*Real.log x))*(C*G x (m x-H))*
          (∑ r ∈ T.image (fun p => ∏ i,p i),(r.totient:ℝ)⁻¹) := by
  obtain ⟨C,hC,hmass⟩ := geometric_suffix_mass (half_pos hc)
  refine ⟨C,hC,?_⟩
  intro L
  filter_upwards [hmass,head_limited_prime_coordinates hc] with H hH hcoords
  filter_upwards [hH,hcoords,tail_head_pair_upper,capped_prime_tail_denominator hd,
    m_tendsto.eventually (eventually_ge_atTop H),eventually_gt_atTop (1:ℝ)]
    with x hmass hcoords hcount hdenom hm hx
  intro n hn Q T hQ hT hsuffix
  have hdata (p) (hp : p∈Q) : (∀ i,(p i).Prime) ∧
      primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
      (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) := by
    have hp' := hQ hp
    obtain ⟨b,hb,hp'⟩ := Finset.mem_biUnion.mp hp'
    exact hcoords _ (Nat.sub_add_cancel hm) p
      (Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hp'⟩)
  have hhead := hcount d hd _ Q (by
    intro p hp
    have hh := hdata p hp
    exact ⟨hh.1,prime_coordinates_strictAnti hh.1 hh.2.1.1.2.1,
      hdenom _ (Nat.sub_le _ _) p hh.1 hh.2.2⟩)
  have hs := hmass _ n (Nat.sub_add_cancel hm) hn Q T
    (fun p hp => ⟨(hdata p hp).1,(hdata p hp).2.1⟩) hT hsuffix
  apply hhead.trans
  have hfac : 0 ≤ x/(d*Real.log x) := by
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    exact (div_pos (zero_lt_one.trans hx) (mul_pos hdR (Real.log_pos hx))).le
  convert mul_le_mul_of_nonneg_left hs hfac using 1
  ring

end TotientAsymptotic

end

end OAI
