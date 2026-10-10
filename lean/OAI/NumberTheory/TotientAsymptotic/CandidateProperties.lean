import OAI.NumberTheory.TotientAsymptotic.CandidateAbundance
import OAI.NumberTheory.TotientAsymptotic.FiniteCandidateRatio
import OAI.NumberTheory.TotientAsymptotic.SubpowerCandidate

namespace OAI

/-! Arithmetic and size properties of the actual counted candidates. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem raw_candidate_prime_data {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
        b=q*(∏ i,p i) ∧ (∀ i,(p i).Prime) ∧ StrictAnti p ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
        (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) ∧
        q ∈ primeInterval (x/(2*((d*(∏ i,p i).totient:ℕ):ℝ)))
          (x/((d*(∏ i,p i).totient:ℕ):ℝ)) ∧
        q.Prime ∧ (∀ i,p i < q) ∧
        Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) := by
  filter_upwards [head_limited_prime_coordinates hc] with H hH
  filter_upwards [hH,capped_prime_tail_denominator hd,head_interval_above_tail,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hcoords hdenom hhead hm
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hzQ,hzq⟩ := Finset.mem_sigma.mp hz
  have hn : m x-H+H=m x := Nat.sub_add_cancel hm
  obtain ⟨hpr,hr,hcap⟩ := hcoords (m x-H) hn z.1 hzQ
  have hD : (1:ℝ) ≤ ((d*(∏ i,z.1 i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hpr i).pos)))
  have hlog := hdenom (m x-H) (Nat.sub_le _ _) z.1 hpr hcap
  obtain ⟨hq,hqp⟩ := hhead _ hD hlog _ z.1 hpr hcap z.2 hzq
  exact ⟨z.1,z.2,rfl,hpr,prime_coordinates_strictAnti hpr hr.1.2.1,
    hr,hcap,hzq,hq,hqp,hlog⟩

theorem raw_candidate_ratio_bound {c : ℝ} (hc : 0 < c) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      (b:ℝ)/b.totient ≤ Real.exp (1+2*((1-rho)⁻¹/(c/2))) := by
  filter_upwards [raw_candidate_prime_data hc d hd] with H hH
  filter_upwards [hH] with x hx
  intro b hb
  obtain ⟨p,q,rfl,hp,ho,hr,_,_,hq,hqp,_⟩ := hx b hb
  exact finite_candidate_ratio_bound (Nat.sub_le _ _) (half_pos hc) p hp ho
    hr.2.1 hq hqp

theorem raw_candidate_size_data {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (d : ℕ) (hd : 0 < d) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,∀ b ∈ rawCandidates x c d H,
      ∃ (p : Fin (m x-H) → ℕ) (q : ℕ),
        b=q*(∏ i,p i) ∧ (∀ i,(p i).Prime) ∧ StrictAnti p ∧
        primePrefixCoord p ∈ relaxedGeometricFamily (m x) (m x-H) (B x) (c/2) ∧
        q.Prime ∧ (∀ i,p i < q) ∧
        ((∏ i,p i:ℕ):ℝ) ≤ x^ε ∧ x^(1-ε) < (q:ℝ) := by
  filter_upwards [raw_candidate_prime_data hc d hd] with H hH
  filter_upwards [hH,capped_tail_subpower hε,subpower_head_lower hε]
    with x hx htail hhead
  intro b hb
  obtain ⟨p,q,rfl,hp,ho,hr,hcap,hinterval,hq,hqp,hlog⟩ := hx b hb
  have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
      (Finset.prod_pos (fun i _ => (hp i).pos)))
  exact ⟨p,q,rfl,hp,ho,hr,hq,hqp,
    htail _ (Nat.sub_le _ _) p hp hcap,hhead _ hD hlog q hinterval⟩

end TotientAsymptotic

end

end OAI
