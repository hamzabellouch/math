import OAI.NumberTheory.TotientAsymptotic.LocalCandidateLists
import OAI.NumberTheory.TotientAsymptotic.PPTPrefixGrouping

namespace OAI

/-! Actual failed candidates admit normal, ordered, maximal-prefix residuals. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localBadCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  (localNormalCandidates x c d L H).filter (fun b => ¬FullFiber d b)

lemma normal_prime_divisor_suffix {N J : ℕ} {p : ℕ → ℕ} {S : ℝ}
    (hprime : ∀ i < N,(p i).Prime)
    (hnormal : ∀ i,J ≤ i → i < N → IsNormalPrime S (p i)) :
    ∀ q : ℕ,q.Prime → q ∣ pptSuffixProduct p N J → IsNormalPrime S q := by
  intro q hq hdiv
  obtain ⟨i,hi,hqi⟩ := (hq.prime.dvd_finsetProd_iff p).mp hdiv
  have hi' := Finset.mem_Ico.mp hi
  have he : q=p i := (Nat.prime_dvd_prime_iff_eq hq (hprime i hi'.2)).mp hqi
  exact he ▸ hnormal i hi'.1 hi'.2

/-- The decomposition is made on the actual failed finite family, retaining
normality at the chosen residual scale for every prime of every residual. -/
theorem local_bad_candidate_prefix_data {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∃ (p : ℕ → ℕ → ℕ) (j : ℕ → ℕ),∀ b ∈ localBadCandidates x c d L H,
        b=pptSuffixProduct (p b) (m x-H+1) 0 ∧
        (∀ i < m x-H+1,(p b i).Prime) ∧
        (∀ i k : ℕ,i < k → k < m x-H+1 → p b k < p b i) ∧
        j b < m x-H+1 ∧ 0 < pptPrefixProduct (p b) (j b) ∧
        b=pptPrefixProduct (p b) (j b)*pptSuffixProduct (p b) (m x-H+1) (j b) ∧
        PPTBadResidual d (pptSuffixProduct (p b) (m x-H+1) (j b)) ∧
        ∀ q : ℕ,q.Prime → q ∣ pptSuffixProduct (p b) (m x-H+1) (j b) →
          IsNormalPrime (localNormalityScale (m x-(j b-1))) q := by
  filter_upwards [local_normal_candidate_list_data hc d hd L] with H hH
  filter_upwards [hH] with x hx
  obtain ⟨p,hp⟩ := hx
  let S := localBadCandidates x c d L H
  have hdata (b) (hb : b ∈ S) := hp b (Finset.mem_filter.mp hb).1
  obtain ⟨j,hj⟩ := ppt_maximal_prefix_grouping hd S p
    (fun b hb => (hdata b hb).1)
    (fun b hb => (hdata b hb).2.1)
    (fun b hb => (hdata b hb).2.2.1)
    (fun b hb => (hdata b hb).2.2.2.1)
    (fun _ hb => (Finset.mem_filter.mp hb).2)
  refine ⟨p,j,?_⟩
  intro b hb
  have hd := hdata b hb
  have hj' := hj b hb
  refine ⟨hd.1,hd.2.1,hd.2.2.1,hj'.1,hj'.2.1,hj'.2.2.1,hj'.2.2.2,?_⟩
  apply normal_prime_divisor_suffix hd.2.1
  intro i hi hN
  exact hd.2.2.2.2 (j b) i hi hN

end TotientAsymptotic

end

end OAI
