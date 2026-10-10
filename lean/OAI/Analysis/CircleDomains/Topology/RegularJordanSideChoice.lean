import OAI.Analysis.CircleDomains.Transfer.LevelChartBox

namespace OAI

/-! The choice of the inward scalar-level side is consistent along a
connected Jordan boundary. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_side_incompatible
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t})
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H))
    {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hxU : x ∈ U) (hxV : x ∈ V)
    (hp : ∀ y ∈ U, t < f y → y ∈ jordanInterior H)
    (hm : ∀ y ∈ V, f y < t → y ∈ jordanInterior H) : False := by
  obtain ⟨e, hxe, he, _, _⟩ := exists_smooth_planar_level_chart hf (ht x (hlevel hx))
  obtain ⟨r, hr, hb⟩ := exists_openPartialHomeomorph_box e hxe (hU.inter hV) ⟨hxU, hxV⟩
  have hx1 : (e x).1 = t := (he x).trans (hlevel hx)
  rw [hx1] at hb
  have hBt : Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆ e.target :=
    fun _ h => (hb h).1
  have hfq (q : ℝ × ℝ) (hq : q ∈ e.target) : f (e.symm q) = q.1 := by
    rw [← he, e.right_inv hq]
  rcases level_chart_jordan_sides H f t e he hlevel hx hxe hr hBt with h | h
  · let q : ℝ × ℝ := (t-r/2, (e x).2)
    have hq : q ∈ Ioo (t-r) t ×ˢ Ioo ((e x).2-r) ((e x).2+r) := by
      constructor <;> constructor <;> dsimp [q] <;> linarith
    have hqb : q ∈ Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) :=
      ⟨⟨hq.1.1, by dsimp [q]; linarith⟩, hq.2⟩
    have hj : e.symm q ∈ jordanInterior H := hm _ (hb hqb).2.2 (by
      rw [hfq q (hBt hqb)]; exact hq.1.2)
    exact h.2 ⟨q, hq, rfl⟩ (subset_closure hj)
  · let q : ℝ × ℝ := (t+r/2, (e x).2)
    have hq : q ∈ Ioo t (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) := by
      constructor <;> constructor <;> dsimp [q] <;> linarith
    have hqb : q ∈ Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) :=
      ⟨⟨by dsimp [q]; linarith, hq.1.2⟩, hq.2⟩
    have hj : e.symm q ∈ jordanInterior H := hp _ (hb hqb).2.1 (by
      rw [hfq q (hBt hqb)]; exact hq.1.1)
    exact h.2 ⟨q, hq, rfl⟩ (subset_closure hj)

lemma regular_jordan_global_side
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ U : Set ℂ, IsOpen U ∧ frontier (jordanInterior H) ⊆ U ∧
      ((∀ y ∈ U, t < f y → y ∈ jordanInterior H) ∨
        (∀ y ∈ U, f y < t → y ∈ jordanInterior H)) := by
  let P : Set ℂ := {x | ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, t < f y → y ∈ jordanInterior H}
  let M : Set ℂ := {x | ∃ U : Set ℂ, IsOpen U ∧ x ∈ U ∧
    ∀ y ∈ U, f y < t → y ∈ jordanInterior H}
  have hP : IsOpen P := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨U, hU, hxU, hp⟩
    exact Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => ⟨U, hU, hy, hp⟩)
  have hM : IsOpen M := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨U, hU, hxU, hp⟩
    exact Filter.mem_of_superset (hU.mem_nhds hxU) (fun y hy => ⟨U, hU, hy, hp⟩)
  have hcover : frontier (jordanInterior H) ⊆ P ∪ M := by
    intro x hx
    obtain ⟨U, hU, hxU, hp | hm⟩ := regular_jordan_local_side H hf ht hlevel hx
    · exact Or.inl ⟨U, hU, hxU, hp⟩
    · exact Or.inr ⟨U, hU, hxU, hm⟩
  have hdisj (x : ℂ) (hx : x ∈ frontier (jordanInterior H)) (hp : x ∈ P) (hm : x ∈ M) : False := by
    obtain ⟨U, hU, hxU, hp⟩ := hp
    obtain ⟨V, hV, hxV, hm⟩ := hm
    exact regular_jordan_side_incompatible H hf ht hlevel hx hU hV hxU hxV hp hm
  have halts : frontier (jordanInterior H) ⊆ P ∨ frontier (jordanInterior H) ⊆ M := by
    by_contra! hh
    obtain ⟨x, hx, hxP⟩ := Set.not_subset.mp hh.1
    obtain ⟨y, hy, hyM⟩ := Set.not_subset.mp hh.2
    have hxM : x ∈ M := (hcover hx).resolve_left hxP
    have hyP : y ∈ P := (hcover hy).resolve_right hyM
    obtain ⟨z, hz, hzP, hzM⟩ := (isConnected_frontier_jordanInterior H).isPreconnected
      P M hP hM hcover ⟨y, hy, hyP⟩ ⟨x, hx, hxM⟩
    exact hdisj z hz hzP hzM
  rcases halts with hp | hm
  · refine ⟨P, hP, hp, Or.inl ?_⟩
    rintro y ⟨U, _, hy, h⟩ hf
    exact h y hy hf
  · refine ⟨M, hM, hm, Or.inr ?_⟩
    rintro y ⟨U, _, hy, h⟩ hf
    exact h y hy hf

end CircleDomainRigidity

end

end OAI
