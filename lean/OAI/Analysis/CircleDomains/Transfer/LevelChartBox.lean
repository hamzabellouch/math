import OAI.Analysis.CircleDomains.Topology.LevelChartJordanSides

namespace OAI

/-! Symmetric coordinate boxes can be chosen inside any prescribed
ambient neighborhood of a regular level point. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_openPartialHomeomorph_box
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ)) {x : ℂ} (hx : x ∈ e.source)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r > 0, Ioo ((e x).1-r) ((e x).1+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆
      e.target ∩ e.symm ⁻¹' U := by
  have hW := e.isOpen_inter_preimage_symm hU
  have hxW : e x ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hx, by simpa only [mem_preimage, e.left_inv hx] using hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hW _ hxW
  refine ⟨r, hr, ?_⟩
  intro q hq
  apply hsub
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_lt] <;> constructor <;> linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]

lemma regular_jordan_local_side
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t})
    {x : ℂ} (hx : x ∈ frontier (jordanInterior H)) :
    ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧
      ((∀ y ∈ N, t < f y → y ∈ jordanInterior H) ∨
        (∀ y ∈ N, f y < t → y ∈ jordanInterior H)) := by
  obtain ⟨e, hxe, he, _, _⟩ := exists_smooth_planar_level_chart hf (ht x (hlevel hx))
  obtain ⟨r, hr, hbox⟩ := exists_openPartialHomeomorph_box e hxe isOpen_univ (mem_univ x)
  have hx1 : (e x).1 = t := (he x).trans (hlevel hx)
  rw [hx1] at hbox
  let B := Ioo (t-r) (t+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r)
  let N := e.symm '' B
  have hBt : B ⊆ e.target := fun _ hy => (hbox hy).1
  refine ⟨N, e.symm.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hBt,
    ⟨e x, ⟨⟨by rw [hx1]; linarith, by rw [hx1]; linarith⟩,
      ⟨by linarith, by linarith⟩⟩, e.left_inv hxe⟩, ?_⟩
  rcases level_chart_jordan_sides H f t e he hlevel hx hxe hr hBt with hp | hm
  · left
    rintro y ⟨q, hq, rfl⟩ hy
    apply hp.1
    refine ⟨q, ⟨⟨?_, hq.1.2⟩, hq.2⟩, rfl⟩
    have heq := congrArg Prod.fst (e.right_inv (hBt hq))
    rw [he] at heq
    linarith
  · right
    rintro y ⟨q, hq, rfl⟩ hy
    apply hm.1
    refine ⟨q, ⟨⟨hq.1.1, ?_⟩, hq.2⟩, rfl⟩
    have heq := congrArg Prod.fst (e.right_inv (hBt hq))
    rw [he] at heq
    linarith

end CircleDomainRigidity

end

end OAI
