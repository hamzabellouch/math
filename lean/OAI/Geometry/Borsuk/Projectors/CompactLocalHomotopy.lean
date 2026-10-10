import Mathlib

namespace OAI

namespace BorsukNine
open Set
open scoped Topology

lemma compact_local_homotopy {X E : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TopologicalSpace E] [Zero E]
    {U C : Set X} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (H : X → E) (hH : Continuous H) (hHz : ∀ x, H x ≠ 0)
    (K : ℝ × X → E) (hK : ContinuousOn K (Icc (0:ℝ) 1 ×ˢ U))
    (hK0 : ∀ x ∈ U, K (0,x) = H x)
    (hKz : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ≠ 0)
    (B : Set E) (houtside : ∀ x ∉ U, H x ∉ B)
    (hhits : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ U, K (t,x) ∈ B → x ∈ C)
    (hend : ∀ x ∈ U, K (1,x) ∉ B) :
    ∃ G : ℝ × X → E, ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) ∧
      (∀ x, G (0,x) = H x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, G (t,x) ≠ 0) ∧
      (∀ x, G (1,x) ∉ B) := by
  classical
  obtain ⟨q,hq1,-,hqs,hqb⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hC hU hCU
  let G : ℝ × X → E := fun p => if p.2 ∈ U then K (p.1 * q p.2,p.2) else H p.2
  have htm (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : X) : t * q x ∈ Icc (0:ℝ) 1 :=
    ⟨mul_nonneg ht.1 (hqb x).1,
      (mul_le_mul_of_nonneg_right ht.2 (hqb x).1).trans (by simpa using (hqb x).2)⟩
  have hG : ContinuousOn G (Icc (0:ℝ) 1 ×ˢ Set.univ) := by
    intro p hp
    by_cases hx : p.2 ∈ U
    · have hc : ContinuousOn (fun p : ℝ × X => K (p.1 * q p.2,p.2))
          (Icc (0:ℝ) 1 ×ˢ U) := hK.comp
        ((continuous_fst.mul (q.continuous.comp continuous_snd)).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨htm p.1 hp.1 p.2,hp.2⟩)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∈ U :=
        continuous_snd.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      have hset : Icc (0:ℝ) 1 ×ˢ U ∈ 𝓝[Icc (0:ℝ) 1 ×ˢ Set.univ] p := by
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear,
          self_mem_nhdsWithin] with p' hu hi
        exact ⟨hi.1,hu⟩
      apply ((hc p ⟨hp.1,hx⟩).mono_of_mem_nhdsWithin hset).congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hu
        simp [G,hu]
      · simp [G,hx]
    · have hxq : p.2 ∉ tsupport q := fun h => hx (hqs h)
      have hnear : ∀ᶠ p' in 𝓝 p, p'.2 ∉ tsupport q :=
        continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport q).isOpen_compl.mem_nhds hxq)
      apply (hH.comp continuous_snd).continuousAt.continuousWithinAt.congr_of_eventuallyEq
      · filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear] with p' hq
        have hz : q p'.2 = 0 := image_eq_zero_of_notMem_tsupport hq
        by_cases hu : p'.2 ∈ U
        · simp [G,hu,hz,hK0 p'.2 hu]
        · simp [G,hu]
      · simp [G,hx]
  refine ⟨G,hG,?_,?_,?_⟩
  · intro x
    by_cases hx : x ∈ U
    · simp [G,hx,hK0 x hx]
    · simp [G,hx]
  · intro t ht x
    by_cases hx : x ∈ U
    · simpa only [G,ite_eq_left hx] using hKz _ (htm t ht x) x hx
    · simpa only [G,ite_eq_right hx] using hHz x
  · intro x hb
    by_cases hx : x ∈ U
    · have hh : K (q x,x) ∈ B := by simpa only [G,ite_eq_left hx,one_mul] using hb
      have hc := hhits _ (hqb x) x hx hh
      rw [hq1 hc] at hh
      exact hend x hx hh
    · exact houtside x hx (by simpa only [G,ite_eq_right hx] using hb)

end BorsukNine

end OAI
