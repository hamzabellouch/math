import OAI.NumberTheory.TotientAsymptotic.AmbientResidualExceptions
import OAI.NumberTheory.TotientAsymptotic.LocalResidualExceptionData

namespace OAI

/-! Direct exceptional counts for the original-head branch of the actual family. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_normal_candidate_normality_and_value {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ localNormalCandidates x c d L H,
      ((d*b.totient:ℕ):ℝ) ≤ x ∧
      ∀ p : ℕ,p.Prime → p ∣ b → IsNormalPrime (localNormalityScale (m x)) p := by
  filter_upwards [local_normal_candidate_list_data hc d hd L,
    raw_candidate_prime_data hc d hd] with H hlist hraw
  filter_upwards [hlist,hraw,eventually_ge_atTop (0:ℝ)] with x hlist hraw hx
  obtain ⟨p,hp⟩ := hlist
  intro b hb
  have hbr := local_regular_candidates_subset (local_normal_candidates_subset hb)
  obtain ⟨t,q,he,ht,_ho,_hr,_hcap,hinterval,_hq,hqp,_hlog⟩ := hraw b hbr
  refine ⟨?_,?_⟩
  · rw [he]
    exact candidate_totient_bound hx hd ht hinterval hqp
  · intro r hr hdiv
    have hh := hp b hb
    have hnorm : ∀ i : ℕ, 0 ≤ i → i < m x-H+1 →
        IsNormalPrime (localNormalityScale (m x)) (p b i) := by
      intro i hi hiN
      simpa only [Nat.zero_sub,Nat.sub_zero] using hh.2.2.2.2 0 i hi hiN
    have hdiv' : r ∣ pptSuffixProduct (p b) (m x-H+1) 0 := by
      rw [←hh.1]
      exact hdiv
    exact normal_prime_divisor_suffix hh.2.1 hnorm r hr hdiv' 

theorem local_original_exception_data {c : ℝ} (hc : 0 < c)
    (d q : ℕ) (hd : 0 < d) (hqpos : 0 < q) (hq : q.totient=d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      let R := localOriginalBad x c d L H
      ∃ F : ℕ → ℕ,Set.InjOn F (R : Set ℕ) ∧
        (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
          largestPrimeFactor (F r) ≠ largestPrimeFactor r) ∧
        ((localWitnessNonnormal R F (m x)).card:ℝ) ≤ x/Real.log x*rho^(m x) ∧
        ((localWitnessSquare R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ) := by
  classical
  filter_upwards [local_normal_candidate_normality_and_value hc d hd L] with H hH
  filter_upwards [hH,ambient_nonnormal_witness_count d q hd,ambient_square_witness_count,
    (localNormalityScale_tendsto.comp m_tendsto).eventually
      (ppt_seed_prime_factors_eventually_normal hqpos)] with x hx hn hs hseed
  let R := localOriginalBad x c d L H
  have hR (r) (hr : r∈R) : r∈localNormalCandidates x c d L H :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1
  obtain ⟨F,hinj,hF,hbranch⟩ := local_bad_residual_witness hd hqpos hq R
    (fun _ hr => (Finset.mem_filter.mp hr).2)
  refine ⟨F,hinj,hF,?_,?_⟩
  · apply hn R (localWitnessNonnormal R F (m x)) F (Finset.filter_subset _ _)
      (fun r hr => (hx r (hR r hr)).2) hseed hbranch
      (fun _ hr => (Finset.mem_filter.mp hr).2)
    intro r hr
    have hrR := (Finset.mem_filter.mp hr).1
    exact ⟨(hF r hrR).1,(hF r hrR).2.1,(hx r (hR r hrR)).1⟩
  · apply hs (localWitnessSquare R F (m x)) F (hinj.mono (Finset.filter_subset _ _))
    · intro r hr
      have hrR := (Finset.mem_filter.mp hr).1
      refine ⟨(hF r hrR).1,?_⟩
      rw [(hF r hrR).2.1]
      exact (hx r (hR r hrR)).1
    · exact fun _ hr => (Finset.mem_filter.mp hr).2

end TotientAsymptotic

end

end OAI
