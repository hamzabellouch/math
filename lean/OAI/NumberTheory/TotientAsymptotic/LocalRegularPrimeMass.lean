import OAI.NumberTheory.TotientAsymptotic.LocalNormalityDiscard

namespace OAI

/-! A positive prime mass satisfying every needed indexed normality condition. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localRegularPrimeTuples (x c : ℝ) (L H : ℕ) : Finset (Fin (m x-H) → ℕ) :=
  gridPrimeTuples (localPrimeGrid x c L (m x-H)) \ localNormalityFailures x c L H

lemma local_regular_normality {x c : ℝ} {L H : ℕ}
    {p : Fin (m x-H) → ℕ} (hp : p ∈ localRegularPrimeTuples x c L H) :
    ∀ i j : Fin (m x-H),i ≤ j → IsNormalPrime (localNormalityScale (m x-i.val)) (p j) := by
  obtain ⟨hp,hnot⟩ := Finset.mem_sdiff.mp hp
  intro i j hij
  by_contra hn
  apply hnot
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,Finset.mem_biUnion.mpr ?_⟩
  exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,Finset.mem_filter.mpr ⟨hp,hn⟩⟩

theorem local_regular_prime_mass : ∃ c δ : ℝ,∃ L : ℕ,
    0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      δ*G x (m x-H) ≤ ∑ p ∈ localRegularPrimeTuples x c L H,reciprocalShiftWeight p := by
  classical
  obtain ⟨c,δ,L,hc,hδ,hL,hmass⟩ := local_prime_mass_lower_base
  have ht := polynomialGeometricTail_tendsto 0 rho
  refine ⟨c,δ/2,L,hc,half_pos hδ,hL,?_⟩
  filter_upwards [hmass,local_normality_discard hc L,
    ht.eventually (eventually_lt_nhds (half_pos hδ))] with H hH hbad htail
  filter_upwards [hH,hbad,m_tendsto.eventually (eventually_ge_atTop (H+2)),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hb hm hB
  let N := m x-H
  let Q := gridPrimeTuples (localPrimeGrid x c L N)
  let F := localNormalityFailures x c L H
  have hN : N-2+2+H=m x := by dsimp [N]; omega
  have hmass : δ*G x N ≤ ∑ p ∈ Q,reciprocalShiftWeight p := by
    have hh := hx (N-2) hN
    have he : N-2+2=N := by dsimp [N]; omega
    change δ*G x (N-2+2) ≤ gridPrimeMass (localPrimeGrid x c L (N-2+2)) at hh
    rw [he] at hh
    exact hh
  have hcover : Q ⊆ Q \ F ∪ F := by
    intro p hp
    by_cases hf : p ∈ F
    · exact Finset.mem_union_right _ hf
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp,hf⟩)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hcover
    (fun p _ _ => reciprocalShiftWeight_nonneg p)
  have hdisj : Disjoint (Q \ F) F := Finset.disjoint_left.mpr
    (fun _ hp hf => (Finset.mem_sdiff.mp hp).2 hf)
  rw [Finset.sum_union hdisj] at hsum
  have hbad' : (∑ p ∈ F,reciprocalShiftWeight p) ≤ (δ/2)*G x N :=
    hb.trans (mul_le_mul_of_nonneg_right htail.le (G_pos hB _).le)
  change (δ/2)*G x N ≤ ∑ p ∈ Q \ F,reciprocalShiftWeight p
  nlinarith only [hmass,hsum,hbad']

end TotientAsymptotic

end

end OAI
