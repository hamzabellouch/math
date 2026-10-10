import OAI.NumberTheory.TotientAsymptotic.LocalBadCandidates
import OAI.NumberTheory.TotientAsymptotic.PrimeSuffixMass
import OAI.NumberTheory.TotientAsymptotic.CandidateHeadSeparation

namespace OAI

/-! A failed candidate either fails at its original head or has a bad
suffix of its tail.  The latter event is independent of the original head. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

lemma candidatePrimeAt_suffix {n i : ℕ} (p : Fin n → ℕ) (q : ℕ) :
    pptSuffixProduct (candidatePrimeAt p q) (n+1) (i+1) =
      ∏ j,primeFinal p i j := by
  unfold pptSuffixProduct
  rw [Finset.prod_Ico_eq_prod_range]
  have he : n+1-(i+1)=n-i := by omega
  rw [he,Finset.prod_range]
  apply Finset.prod_congr rfl
  intro j _
  have hj : i+j.val<n := by have := j.isLt; omega
  have hid : i+1+j.val=i+j.val+1 := by omega
  rw [hid,candidatePrimeAt_succ p q (i+j.val) hj]
  rfl

theorem candidate_bad_suffix {d n : ℕ} (hd : 0 < d)
    (p : Fin n → ℕ) (q : ℕ) (hp : ∀ i,(p i).Prime) (ho : StrictAnti p)
    (hq : q.Prime) (hqp : ∀ i,p i<q)
    (hrough : ∀ r : ℕ,r.Prime → r ∣ q*(∏ i,p i) → d+1<r)
    (hbad : ¬FullFiber d (q*(∏ i,p i))) :
    PPTBadResidual d (q*(∏ i,p i)) ∨
      ∃ i : Fin n,PPTBadResidual d (∏ j,primeFinal p i.val j) := by
  classical
  let b := q*(∏ i,p i)
  let r := candidatePrimeAt p q
  have hr := candidatePrimeAt_prime p hp hq
  have hrep : b=pptSuffixProduct r (n+1) 0 := (candidatePrimeAt_product p q).symm
  obtain ⟨J,hJ⟩ := ppt_maximal_prefix_grouping hd {b} (fun _ => r)
    (by intro v hv; simpa only [Finset.mem_singleton.mp hv] using hrep)
    (fun _ _ => hr) (fun _ _ => candidatePrimeAt_order p ho hqp)
    (by
      intro v hv i hi
      apply hrough _ (hr i hi)
      change r i ∣ b
      rw [hrep]
      exact Finset.dvd_prod_of_mem r (Finset.mem_Ico.mpr ⟨Nat.zero_le _,hi⟩))
    (by intro v hv; simpa only [Finset.mem_singleton.mp hv] using hbad)
  have hh := hJ b (Finset.mem_singleton_self b)
  by_cases hzero : J b=0
  · left
    have hh' := hh.2.2.2
    rw [hzero,←hrep] at hh'
    exact hh'
  · right
    have hi : J b-1<n := by omega
    refine ⟨⟨J b-1,hi⟩,?_⟩
    have hh' := hh.2.2.2
    have he : J b=J b-1+1 := by omega
    rw [he] at hh'
    simpa only [r,candidatePrimeAt_suffix] using hh'

def localOriginalBad (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  (localBadCandidates x c d L H).filter (PPTBadResidual d)

def localBadSuffixTuples (x c : ℝ) (d L H : ℕ) (i : Fin (m x-H)) :
    Finset (Fin (m x-H) → ℕ) :=
  (localRegularPrimeTuples x c L H).filter
    (fun p => PPTBadResidual d (∏ j,primeFinal p i.val j))

theorem local_bad_candidate_count_cover {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ((localBadCandidates x c d L H).card:ℝ) ≤
        (localOriginalBad x c d L H).card+
          ∑ i : Fin (m x-H),((tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card:ℝ) := by
  classical
  filter_upwards [head_limited_prime_coordinates hc,raw_candidate_rough hc d hd]
    with H hcoords hrough
  filter_upwards [hcoords,hrough,capped_prime_tail_denominator hd,head_interval_above_tail,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hcoords hrough hdenom hhead hm
  let S := localBadCandidates x c d L H
  let T (i : Fin (m x-H)) :=
    (tailHeadPairs x d (localBadSuffixTuples x c d L H i)).image
      (fun z => z.2*(∏ j,z.1 j))
  have hcover : S ⊆ localOriginalBad x c d L H ∪ Finset.univ.biUnion T := by
    intro b hb
    have hb' := Finset.mem_filter.mp hb
    obtain ⟨p,q,hbval,hp,hinterval,_,_⟩ := local_normal_candidate_representation hb'.1
    have hpgrid := local_regular_tuples_subset hp
    have hpc := hcoords _ (Nat.sub_add_cancel hm) p hpgrid
    have hprime := hpc.1
    have horder := prime_coordinates_strictAnti hprime hpc.2.1.1.2.1
    have hD : (1:ℝ) ≤ ((d*(∏ i,p i).totient:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_pos hd (Nat.totient_pos.mpr
        (Finset.prod_pos (fun i _ => (hprime i).pos)))
    have hlog := hdenom _ (Nat.sub_le _ _) p hprime hpc.2.2
    obtain ⟨hq,hqp⟩ := hhead _ hD hlog _ p hprime hpc.2.2 q hinterval
    have hbraw := local_regular_candidates_subset (local_normal_candidates_subset hb'.1)
    have hroughb : ∀ r : ℕ,r.Prime → r ∣ q*(∏ i,p i) → d+1<r := by
      intro r hr hdiv
      exact hrough b hbraw r hr (by simpa only [hbval] using hdiv)
    have hbad : ¬FullFiber d (q*(∏ i,p i)) := hbval ▸ hb'.2
    rcases candidate_bad_suffix hd p q hprime horder hq hqp hroughb hbad with hfirst | ⟨i,hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb,hbval.symm ▸ hfirst⟩)
    · apply Finset.mem_union_right _
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ?_⟩
      exact ⟨⟨p,q⟩,Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hp,hi⟩,hinterval⟩,hbval.symm⟩
  have hnat : S.card ≤ (localOriginalBad x c d L H).card+
      ∑ i : Fin (m x-H),(tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card := by
    apply (Finset.card_le_card hcover).trans
    apply (Finset.card_union_le _ _).trans
    apply Nat.add_le_add_left
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum (fun i _ => Finset.card_image_le)
  exact_mod_cast hnat

end TotientAsymptotic

end

end OAI
