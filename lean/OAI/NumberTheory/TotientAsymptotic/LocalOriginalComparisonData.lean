import OAI.NumberTheory.TotientAsymptotic.LocalOriginalExceptions
import OAI.NumberTheory.TotientAsymptotic.CandidateProperties
import OAI.NumberTheory.TotientAsymptotic.CandidateRoughness

namespace OAI

/-! The original-head branch retains a geometric tail, a dominant head,
and normality for the same ordered representation. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_original_comparison_data {c : ℝ} (hc : 0<c)
    (d : ℕ) (hd : 0<d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ b∈localNormalCandidates x c d L H,
        ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
          b=q*(∏ i,p i) ∧ (∀ i,(p i).Prime) ∧ StrictAnti p ∧
          primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
          q.Prime ∧ (∀ i,p i<q) ∧
          ((∏ i,p i:ℕ):ℝ)≤x^(1/10:ℝ) ∧ x^(9/10:ℝ)<(q:ℝ) ∧
          IsNormalPrime (localNormalityScale (m x)) q ∧
          (∀ i,IsNormalPrime (localNormalityScale (m x)) (p i)) ∧
          3 ≤ q ∧ (∀ i,3 ≤ p i) ∧
          (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) := by
  filter_upwards [raw_candidate_prime_data hc d hd,
    local_normal_candidate_normality_and_value hc d hd L,
    raw_candidate_rough hc d hd] with H hdata hnormal hrough
  filter_upwards [hdata,hnormal,hrough,
    capped_tail_subpower (by norm_num : (0:ℝ)<1/10),
    subpower_head_lower (by norm_num : (0:ℝ)<1/10)]
    with x hdata hnormal hrough htailbound hheadbound
  intro b hb
  have hbraw := local_regular_candidates_subset (local_normal_candidates_subset hb)
  obtain ⟨p,q,he,hp,ho,hgeom,hcap,hinterval,hq,hqp,hlog⟩ := hdata b hbraw
  have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hp i).pos)))
  have htail := htailbound _ (Nat.sub_le _ _) p hp hcap
  have hhead := hheadbound _ hD hlog q hinterval
  have hqdiv : q∣b := by rw [he]; exact dvd_mul_right _ _
  have hpdiv (i) : p i∣b := by
    rw [he]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) _
  have hn := (hnormal b hb).2
  refine ⟨p,q,he,hp,ho,hgeom,hq,hqp,htail,?_,hn q hq hqdiv,
    (fun i => hn (p i) (hp i) (hpdiv i)),?_,?_,hcap⟩
  · convert hhead using 1
    norm_num
  · have hh := hrough b hbraw q hq hqdiv
    omega
  · intro i
    have hh := hrough b hbraw (p i) (hp i) (hpdiv i)
    omega

end TotientAsymptotic

end

end OAI
