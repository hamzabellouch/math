import OAI.NumberTheory.TotientAsymptotic.LocalRegularPrimeMass
import OAI.NumberTheory.TotientAsymptotic.CandidateProperties

namespace OAI

/-! Actual prime-product candidates retaining all local normality conditions. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma local_grid_tuples_subset {x c : ℝ} {L n : ℕ} :
    gridPrimeTuples (localPrimeGrid x c L n) ⊆
      gridPrimeTuples (headLimitedPrimeGrid x c n) := by
  intro p hp
  obtain ⟨b,hb,hp⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨b,localPrimeGrid_subset hb,hp⟩

lemma local_regular_tuples_subset {x c : ℝ} {L H : ℕ} :
    localRegularPrimeTuples x c L H ⊆
      gridPrimeTuples (headLimitedPrimeGrid x c (m x-H)) := by
  intro p hp
  exact local_grid_tuples_subset (Finset.mem_sdiff.mp hp).1

def localRegularCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  candidateIntegers x d (localRegularPrimeTuples x c L H)

lemma local_regular_candidates_subset {x c : ℝ} {d L H : ℕ} :
    localRegularCandidates x c d L H ⊆ rawCandidates x c d H := by
  intro b hb
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hp,hq⟩ := Finset.mem_sigma.mp hz
  exact Finset.mem_image.mpr ⟨z,Finset.mem_sigma.mpr
    ⟨local_regular_tuples_subset hp,hq⟩,rfl⟩

theorem local_regular_candidate_abundance :
    ∃ c δ : ℝ,∃ L : ℕ,0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ d : ℕ,0 < d → ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (δ/(4*d))*(x/Real.log x*G x (m x-H)) ≤
        ((localRegularCandidates x c d L H).card:ℝ) := by
  obtain ⟨c,δ,L,hc,hδ,hL,hmass⟩ := local_regular_prime_mass
  refine ⟨c,δ,L,hc,hδ,hL,?_⟩
  intro d hd
  filter_upwards [hmass,head_limited_prime_coordinates hc] with H hmass hcoord
  filter_upwards [hmass,hcoord,tail_head_pair_count,capped_prime_tail_denominator hd,
    head_interval_above_tail,m_tendsto.eventually (eventually_ge_atTop H),
    eventually_gt_atTop (1:ℝ)] with x hmass hcoords hcount hdenom hhead hm hx1
  let n := m x-H
  let Q := localRegularPrimeTuples x c L H
  have hnH : n+H=m x := Nat.sub_add_cancel hm
  have hQ (p) (hp : p ∈ Q) :
      (∀ i,(p i).Prime) ∧ StrictAnti p ∧
      Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) := by
    obtain ⟨hpr,hr,hcap⟩ := hcoords n hnH p (local_regular_tuples_subset hp)
    exact ⟨hpr,prime_coordinates_strictAnti hpr hr.1.2.1,
      hdenom n (Nat.sub_le _ _) p hpr hcap⟩
  have hheads (z) (hz : z ∈ tailHeadPairs x d Q) :
      z.2.Prime ∧ ∀ i,z.1 i < z.2 := by
    obtain ⟨hzQ,hzq⟩ := Finset.mem_sigma.mp hz
    obtain ⟨hpr,_,hcap⟩ := hcoords n hnH z.1 (local_regular_tuples_subset hzQ)
    have hD : (1:ℝ) ≤ ((d*(∏ i,z.1 i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
        (Finset.prod_pos (fun i _ => (hpr i).pos)))
    exact hhead _ hD (hQ z.1 hzQ).2.2 n z.1 hpr hcap z.2 hzq
  have hcard := candidateIntegers_card
    (fun p hp => ⟨(hQ p hp).1,(hQ p hp).2.1⟩) hheads
  have hpairs := hcount d hd n Q hQ
  rw [←hcard] at hpairs
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hfac : 0 ≤ x/(4*d*Real.log x) :=
    (div_pos (zero_lt_one.trans hx1) (by positivity)).le
  calc
    _ = (x/(4*d*Real.log x))*(δ*G x n) := by dsimp [n]; ring
    _ ≤ (x/(4*d*Real.log x))*(∑ p ∈ Q,reciprocalShiftWeight p) :=
      mul_le_mul_of_nonneg_left hmass hfac
    _ ≤ _ := hpairs

end TotientAsymptotic

end

end OAI
