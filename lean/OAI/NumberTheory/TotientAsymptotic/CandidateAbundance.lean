import OAI.NumberTheory.TotientAsymptotic.CandidateArithmetic
import OAI.NumberTheory.TotientAsymptotic.CandidateHeadSeparation

namespace OAI

/-! A positive counting-scale family of actual prime-product candidates. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def rawCandidates (x c : ℝ) (d H : ℕ) : Finset ℕ :=
  candidateIntegers x d (gridPrimeTuples (headLimitedPrimeGrid x c (m x-H)))

theorem raw_candidate_abundance : ∃ c : ℝ,0 < c ∧ ∀ d : ℕ,0 < d →
    ∀ᶠ H : ℕ in atTop,∃ η : ℝ,0 < η ∧ ∀ᶠ x : ℝ in atTop,
      η*(x/Real.log x*G x (m x)) ≤ ((rawCandidates x c d H).card:ℝ) ∧
      ∀ b ∈ rawCandidates x c d H,0 < b ∧ ((d*b.totient:ℕ):ℝ) ≤ x := by
  obtain ⟨c,hc,hmass⟩ := head_limited_prime_mass_lower
  refine ⟨c,hc,?_⟩
  intro d hd
  filter_upwards [hmass,head_limited_prime_coordinates hc] with H hH hcoord
  obtain ⟨δ,hδ,hδmass⟩ := hH
  refine ⟨δ/(4*d),by positivity,?_⟩
  filter_upwards [hδmass,hcoord,tail_head_pair_count,capped_prime_tail_denominator hd,
    head_interval_above_tail,m_tendsto.eventually (eventually_ge_atTop (H+2)),
    eventually_gt_atTop (1:ℝ)] with x hx hcoords hcount hdenom hhead hm hx1
  let n := m x-H
  let Q := gridPrimeTuples (headLimitedPrimeGrid x c n)
  have hnH : n+H=m x := by dsimp [n]; omega
  have hn : n ≤ m x := by dsimp [n]; omega
  have hN : (n-2)+2+H=m x := by dsimp [n]; omega
  have hQ (p) (hp : p ∈ Q) :
      (∀ i,(p i).Prime) ∧ StrictAnti p ∧
      Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) := by
    obtain ⟨hpr,hr,hcap⟩ := hcoords n hnH p hp
    exact ⟨hpr,prime_coordinates_strictAnti hpr hr.1.2.1,hdenom n hn p hpr hcap⟩
  have hheads (z) (hz : z ∈ tailHeadPairs x d Q) :
      z.2.Prime ∧ ∀ i,z.1 i < z.2 := by
    obtain ⟨hzQ,hzq⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hpr,_,hcap⟩ := hcoords n hnH z.1 hzQ
    have hD : (1:ℝ) ≤ ((d*(∏ i,z.1 i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
        (Finset.prod_pos (fun i _ => (hpr i).pos)))
    exact hhead _ hD (hQ z.1 hzQ).2.2 n z.1 hpr hcap z.2 hzq
  have hcard := candidateIntegers_card (fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1⟩) hheads
  have hpairs := hcount d hd n Q hQ
  rw [←hcard] at hpairs
  have hmass : δ*G x (m x) ≤ ∑ p ∈ Q,reciprocalShiftWeight p := by
    have hh := hx (n-2) hN
    have he : n-2+2=n := by dsimp [n]; omega
    rw [he] at hh
    exact hh
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hfac : 0 ≤ x/(4*d*Real.log x) := by
    have hd' : (0:ℝ) < d := by exact_mod_cast hd
    exact (div_pos (zero_lt_one.trans hx1) (by positivity)).le
  refine ⟨?_,?_⟩
  · calc
      _ = (x/(4*d*Real.log x))*(δ*G x (m x)) := by ring
      _ ≤ (x/(4*d*Real.log x))*(∑ p ∈ Q,reciprocalShiftWeight p) :=
        mul_le_mul_of_nonneg_left hmass hfac
      _ ≤ _ := hpairs
  · intro b hb
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hzQ,hzq⟩ := Finset.mem_sigma.mp hz
    have hpr := (hQ z.1 hzQ).1
    have hh := hheads z hz
    refine ⟨Nat.mul_pos hh.1.pos (Finset.prod_pos (fun i _ => (hpr i).pos)),?_⟩
    exact candidate_totient_bound (zero_lt_one.trans hx1).le hd hpr hzq hh.2

end TotientAsymptotic

end

end OAI
