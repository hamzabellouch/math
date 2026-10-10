import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Ball
import OAI.Combinatorics.KMedianRecovery.Branching.PopulationMachine

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RationalMin
lemma fold_lower_real (qs : List ℚ) (a : ℚ) (u : ℝ) (ha : u≤(a:ℝ)) (hq : ∀ q∈qs,u≤(q:ℝ)) :
    u≤((qs.foldl min a : ℚ):ℝ) := by
  induction qs generalizing a with
  | nil=>exact ha
  | cons q qs ih=>
    rw [List.foldl_cons]
    apply ih
    · rw [Rat.cast_min]
      exact le_min ha (hq q (by simp))
    · intro r hr
      exact hq r (by simp [hr])
lemma minimum_lower_real (qs : List ℚ) (u : ℝ) (hne : qs≠[]) (hu : ∀ q∈qs,u≤(q:ℝ)) :
    u≤(minimum qs:ℝ) := by
  cases qs with
  | nil=>exact (hne rfl).elim
  | cons q qs=>
    apply fold_lower_real
    · exact hu q (by simp)
    · exact hu
end MetricKMedianRecovery.BitMachine.RationalMin
namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
def distanceList (D : Finset (Fin n)) (w : Fin n) : List ℚ := (D.sort (·≤·)).map (δ w)
include hδ
lemma filter_count_cast (D : Finset (Fin n)) (w p : Fin n) :
    ((distanceList δ D w).filter (fun q=>decide (q≤δ w p))).length=(Population.ball D w (dist w p)).card := by
  rw [distanceList,List.filter_map,List.length_map]
  simp only [Function.comp_def]
  rw [←List.toFinset_card_of_nodup ((D.sort_nodup (·≤·)).filter (fun v=>decide (δ w v≤δ w p)))]
  congr 1
  ext i
  simp only [List.toFinset_filter,Finset.sort_toFinset,Finset.mem_filter,decide_eq_true_eq,Population.ball]
  rw [←hδ w i,←hδ w p,Rat.cast_le]
lemma candidate_cast (D : Finset (Fin n)) (P : ℚ) (m : ℕ) (w p : Fin n) :
    (candidateQ P m (distanceList δ D w) (δ w p):ℝ)=Population.candidate D (P:ℝ) m w p := by
  simp only [candidateQ,Rat.cast_max,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,hδ,
    filter_count_cast δ hδ,Population.candidate]
omit hδ [PseudoMetricSpace (Fin n)] in
lemma distanceList_nonempty (D : Finset (Fin n)) (hD : D.Nonempty) (w : Fin n) : distanceList δ D w≠[] := by
  intro hh
  obtain ⟨p,hp⟩:=hD
  have hm : δ w p∈distanceList δ D w := List.mem_map.mpr ⟨p,(Finset.mem_sort (·≤·)).mpr hp,rfl⟩
  rw [hh] at hm
  exact List.not_mem_nil hm
lemma radiusQ_cast (D : Finset (Fin n)) (hD : D.Nonempty) (P : ℚ) (m : ℕ) (w : Fin n) :
    (radiusQ P m (distanceList δ D w):ℝ)=Population.radius D hD (P:ℝ) m w := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro p hp
    rw [←candidate_cast δ hδ D P m w p]
    exact_mod_cast RationalMin.minimum_le_mem ((distanceList δ D w).map (candidateQ P m (distanceList δ D w))) (candidateQ P m (distanceList δ D w) (δ w p))
      (List.mem_map.mpr ⟨δ w p,List.mem_map.mpr ⟨p,(Finset.mem_sort (·≤·)).mpr hp,rfl⟩,rfl⟩)
  · apply RationalMin.minimum_lower_real
    · exact fun h=>distanceList_nonempty δ D hD w (List.map_eq_nil_iff.mp h)
    · intro q hq
      obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hq
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hd
      rw [candidate_cast δ hδ]
      exact Finset.inf'_le _ ((Finset.mem_sort (·≤·)).mp hp)
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
