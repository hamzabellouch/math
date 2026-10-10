import Mathlib
import OAI.Probability.SKBarriers.Replicas.ProductMerge
import OAI.Probability.SKBarriers.Replicas.TripleSchedule

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleSchedule (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  tripleCommonSchedule c++tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))++tripleTailSchedule t

theorem tripleCommonSchedule_mem_mass {c : List (ℝ × ℝ)} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleCommonSchedule c) : ∃ q∈c,p.1=q.1/3 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨q,hq,rfl⟩

theorem tripleMiddleSchedule_mem_mass {δ : ℝ} {w : List (ℝ × (ℝ × ℝ))} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))) :
    ∃ q∈weightedUnderlying w,p.1=q.1 ∨ p.1=q.1/2 := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  simp only [mergedProductBranches,List.mem_merge,List.mem_map] at hs
  rcases hs with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
  · exact ⟨(q.1,q.2.1),List.mem_map.mpr ⟨q,hq,rfl⟩,Or.inl rfl⟩
  · exact ⟨q,hq,Or.inr rfl⟩

theorem tripleTailSchedule_mem_mass {t : List (ℝ × ℝ)} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈tripleTailSchedule t) : ∃ q∈t,p.1=q.1 := by
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  simp only [tripleTailBlock,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> exact ⟨q,hq,rfl⟩

theorem tripleTailSchedule_monotone (t : List (ℝ × ℝ))
    (ht : t.Pairwise (fun p q => p.1≤q.1)) :
    (tripleTailSchedule t).Pairwise (fun p q => p.1≤q.1) := by
  induction t with
  | nil => simp [tripleTailSchedule]
  | cons a t ih =>
    obtain ⟨ha,ht⟩ := List.pairwise_cons.mp ht
    change (tripleTailBlock a++tripleTailSchedule t).Pairwise _
    apply List.pairwise_append.mpr
    refine ⟨?_,ih ht,?_⟩
    · simp [tripleTailBlock]
    · intro p hp q hq
      obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
      have hpa : p.1=a.1 := by
        simp only [tripleTailBlock,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with rfl|rfl|rfl <;> rfl
      rw [hpa,hqb]
      exact ha b hb

theorem tripleSchedule_mass_bounds (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) (hm : ∀ p∈c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈tripleSchedule δ c w t,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  simp only [tripleSchedule,List.mem_append] at hp
  rcases hp with (hp|hp)|hp
  · obtain ⟨q,hq,hpq⟩ := tripleCommonSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleMiddleSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rcases hpq with hpq|hpq
    · simpa only [hpq] using H
    · rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleTailSchedule_mem_mass hp
    simpa only [hpq] using hm q (by simp [hq])

theorem tripleSchedule_monotone (δ : ℝ) (c : List (ℝ × ℝ)) (w : List (ℝ × (ℝ × ℝ)))
    (t : List (ℝ × ℝ)) (hm : ∀ p∈c++weightedUnderlying w++t,0≤p.1)
    (hs : (c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1)) :
    (tripleSchedule δ c w t).Pairwise (fun p q => p.1≤q.1) := by
  obtain ⟨hcw,ht,hct⟩ := List.pairwise_append.mp hs
  obtain ⟨hc,hw,hcw⟩ := List.pairwise_append.mp hcw
  have hmid : (tripleMiddleSchedule δ (mergedProductBranches w (weightedUnderlying w))).Pairwise
      (fun p q => p.1≤q.1) := by
    rw [tripleMiddleSchedule,List.pairwise_map]
    apply mergedProductBranches_monotone
    · simpa only [weightedUnderlying,List.pairwise_map] using hw
    · exact hw
  have hcom : (tripleCommonSchedule c).Pairwise (fun p q => p.1≤q.1) := by
    rw [tripleCommonSchedule,List.pairwise_map]
    exact hc.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  unfold tripleSchedule
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨hcom,hmid,?_⟩,tripleTailSchedule_monotone t ht,?_⟩
  · intro p hp q hq
    obtain ⟨a,ha,hpa⟩ := tripleCommonSchedule_mem_mass hp
    obtain ⟨b,hb,hqb⟩ := tripleMiddleSchedule_mem_mass hq
    have H := hcw a ha b hb
    have Ha := hm a (by simp [ha])
    rw [hpa]
    rcases hqb with hqb|hqb <;> rw [hqb] <;> linarith
  · intro p hp q hq
    obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
    rw [hqb]
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨a,ha,hpa⟩ := tripleCommonSchedule_mem_mass hp
      have H := hct a (List.mem_append_left _ ha) b hb
      have Ha := hm a (by simp [ha])
      rw [hpa]; linarith
    · obtain ⟨a,ha,hpa⟩ := tripleMiddleSchedule_mem_mass hp
      have H := hct a (List.mem_append_right _ ha) b hb
      have Ha := hm a (by simp [ha])
      rcases hpa with hpa|hpa <;> rw [hpa] <;> linarith

end SK.Analytic

end
end

end OAI
