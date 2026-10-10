import OAI.Combinatorics.EditApproximation.Queries.QueryRepresentatives
import OAI.Combinatorics.EditApproximation.Queries.QueryScalarDispatch

namespace OAI

namespace EditApproximation

theorem queryEarlierRepresentatives_scale {n : ℕ} (N P F exponent : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) (br : ℕ × TargetInterval n)
    (hb : br ∈ queryEarlierRepresentatives N P F exponent a initial q) :
    br.1 ∈ dyadicScales N := by
  simp only [queryEarlierRepresentatives, List.mem_append] at hb
  rcases hb with (hlocal | hcell) | honline
  · exact (representativeList_conditions a initial
      (localRefinementRepresentatives_subset N P F a initial q br hlocal)).1
  · obtain ⟨key, hkey, hbr⟩ := List.mem_flatMap.mp hcell
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hbr
    exact localGroupQueryKeys_scale hkey
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp honline
    exact (List.mem_filter.mp hb).1

theorem BinaryFraction.queryEarlierRepresentativesWithWork_scale {n : ℕ}
    (N P F exponent : ℕ) (hP : 0 < P) (a : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (R : ℕ) (hR : ∀ r, (initial r).2 ≤ R) (br : ℕ × TargetInterval n)
    (hb : br ∈ (queryEarlierRepresentativesWithWork N P F exponent hP a initial q).1) :
    br.1 ∈ dyadicScales N := by
  rw [queryEarlierRepresentativesWithWork_value N P F exponent hP a initial q R hR] at hb
  exact queryEarlierRepresentatives_scale N P F exponent a.value (fun r => (initial r).1.value) q br hb

end EditApproximation

end OAI
