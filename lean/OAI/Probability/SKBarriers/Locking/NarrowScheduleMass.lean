import Mathlib
import OAI.Probability.SKBarriers.Locking.NarrowRetainedExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem narrowCommonSchedule_mem_mass {δ : ℝ} {c : List (ℝ × (ℝ × ℝ))} {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈narrowCommonSchedule δ c) : ∃ q∈weightedUnderlying c,p.1=q.1/3 := by
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact ⟨(q.1,q.2.1),List.mem_map.mpr ⟨q,hq,rfl⟩,rfl⟩

theorem narrowMiddleSchedule_mem_mass {δ : ℝ} {v w : List (ℝ × (ℝ × ℝ))}
    (hv : weightedUnderlying v=weightedUnderlying w) {p : ℝ × (Fin 3 → ℝ)}
    (hp : p∈narrowMiddleSchedule δ (mergedProductBranches v w)) :
    ∃ q∈weightedUnderlying w,p.1=q.1 ∨ p.1=q.1/2 := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
  simp only [mergedProductBranches,List.mem_merge,List.mem_map] at hs
  rcases hs with ⟨q,hq,rfl⟩|⟨q,hq,rfl⟩
  · have hq' : (q.1,q.2.1)∈weightedUnderlying w := hv ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
    exact ⟨(q.1,q.2.1),hq',Or.inl rfl⟩
  · exact ⟨(q.1,q.2.1),List.mem_map.mpr ⟨q,hq,rfl⟩,Or.inr rfl⟩

theorem narrowSchedule_mass_bounds (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈narrowSchedule δ c v w t,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  simp only [narrowSchedule,List.mem_append] at hp
  rcases hp with (hp|hp)|hp
  · obtain ⟨q,hq,hpq⟩ := narrowCommonSchedule_mem_mass hp
    have H := hm q (by simp [hq])
    rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := narrowMiddleSchedule_mem_mass hv hp
    have H := hm q (by simp [hq])
    rcases hpq with hpq|hpq
    · simpa only [hpq] using H
    · rw [hpq]; constructor <;> linarith [H.1,H.2]
  · obtain ⟨q,hq,hpq⟩ := tripleTailSchedule_mem_mass hp
    simpa only [hpq] using hm q (by simp [hq])

theorem narrowSchedule_monotone (δ : ℝ) (c v w : List (ℝ × (ℝ × ℝ))) (t : List (ℝ × ℝ))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w++t,0≤p.1)
    (hs : (weightedUnderlying c++weightedUnderlying w++t).Pairwise (fun p q => p.1≤q.1)) :
    (narrowSchedule δ c v w t).Pairwise (fun p q => p.1≤q.1) := by
  obtain ⟨hcw,ht,hct⟩ := List.pairwise_append.mp hs
  obtain ⟨hc,hw,hcw⟩ := List.pairwise_append.mp hcw
  have hmid : (narrowMiddleSchedule δ (mergedProductBranches v w)).Pairwise (fun p q => p.1≤q.1) := by
    rw [narrowMiddleSchedule,List.pairwise_map]
    apply mergedProductBranches_monotone
    · have H : (weightedUnderlying v).Pairwise (fun p q => p.1≤q.1) := by rw [hv]; exact hw
      simpa only [weightedUnderlying,List.pairwise_map] using H
    · simpa only [weightedUnderlying,List.pairwise_map] using hw
  have hcom : (narrowCommonSchedule δ c).Pairwise (fun p q => p.1≤q.1) := by
    rw [narrowCommonSchedule,List.pairwise_map]
    rw [weightedUnderlying,List.pairwise_map] at hc
    exact hc.imp (fun h => div_le_div_of_nonneg_right h (by norm_num))
  unfold narrowSchedule
  apply List.pairwise_append.mpr
  refine ⟨List.pairwise_append.mpr ⟨hcom,hmid,?_⟩,tripleTailSchedule_monotone t ht,?_⟩
  · intro p hp q hq
    obtain ⟨a,ha,hpa⟩ := narrowCommonSchedule_mem_mass hp
    obtain ⟨b,hb,hqb⟩ := narrowMiddleSchedule_mem_mass hv hq
    have H := hcw a ha b hb
    have Ha := hm a (by simp [ha])
    rw [hpa]
    rcases hqb with hqb|hqb <;> rw [hqb] <;> linarith
  · intro p hp q hq
    obtain ⟨b,hb,hqb⟩ := tripleTailSchedule_mem_mass hq
    rw [hqb]
    rcases List.mem_append.mp hp with hp|hp
    · obtain ⟨a,ha,hpa⟩ := narrowCommonSchedule_mem_mass hp
      have H := hct a (List.mem_append_left _ ha) b hb
      have Ha := hm a (by simp [ha])
      rw [hpa]; linarith
    · obtain ⟨a,ha,hpa⟩ := narrowMiddleSchedule_mem_mass hv hp
      have H := hct a (List.mem_append_right _ ha) b hb
      have Ha := hm a (by simp [ha])
      rcases hpa with hpa|hpa <;> rw [hpa] <;> linarith

theorem narrowRetainedPrefix_mass (c v w : List (ℝ × (ℝ × ℝ)))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w,p.1∈Icc (0:ℝ) 1) :
    ∀ p∈narrowRetainedPrefix c v w,p.1∈Icc (0:ℝ) 1 := by
  intro p hp
  have H := narrowSchedule_mass_bounds 0 c v w [] hv (by simpa only [List.append_nil] using hm)
  rw [← narrowRetainedPrefix_image] at H
  simp only [tripleTailSchedule,List.flatMap_nil,List.append_nil] at H
  exact H (p.1,narrowRetainedEmbedding 0 p.2) (List.mem_map.mpr ⟨p,hp,rfl⟩)

theorem narrowRetainedPrefix_monotone (c v w : List (ℝ × (ℝ × ℝ)))
    (hv : weightedUnderlying v=weightedUnderlying w)
    (hm : ∀ p∈weightedUnderlying c++weightedUnderlying w,0≤p.1)
    (hs : (weightedUnderlying c++weightedUnderlying w).Pairwise (fun p q => p.1≤q.1)) :
    (narrowRetainedPrefix c v w).Pairwise (fun p q => p.1≤q.1) := by
  have H := narrowSchedule_monotone 0 c v w [] hv (by simpa only [List.append_nil] using hm)
    (by simpa only [List.append_nil] using hs)
  rw [← narrowRetainedPrefix_image] at H
  simpa only [tripleTailSchedule,List.flatMap_nil,List.append_nil,List.pairwise_map] using H

end SK.Analytic

end
end

end OAI
