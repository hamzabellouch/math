import Mathlib
import OAI.Geometry.Cannon.Modulus.Clip
import OAI.Geometry.Cannon.Energy.Plane

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set unitInterval
open Set Metric Topology
open Set Topology unitInterval

namespace CannonCharts

open unitInterval

def sideOrientation : Fin 4 → Plane ≃ₜ Plane :=
  ![Homeomorph.refl Plane,
    (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ),
    Homeomorph.prodComm ℝ ℝ,
    (Homeomorph.prodComm ℝ ℝ).trans
      ((Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ))]

lemma norm_sideOrientation (j : Fin 4) (z : Plane) : ‖sideOrientation j z‖ = ‖z‖ := by
  fin_cases j <;> simp [sideOrientation, Prod.norm_def, max_comm]

lemma side_at_frontier {z : Plane} (hz : ‖z‖ = 2) :
    ∃ j : Fin 4, (sideOrientation j z).1 = 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_eq_iff] at hz
  rcases hz with ⟨hx,_⟩ | ⟨hy,_⟩
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 2)).mp hx with hx | hx
    · exact ⟨0,by simpa [sideOrientation] using hx⟩
    · exact ⟨1,by simpa [sideOrientation] using (neg_eq_iff_eq_neg.mpr hx)⟩
  · rcases (abs_eq (by norm_num : (0:ℝ) ≤ 2)).mp hy with hy | hy
    · exact ⟨2,by simpa [sideOrientation] using hy⟩
    · exact ⟨3,by simpa [sideOrientation] using (neg_eq_iff_eq_neg.mpr hy)⟩

theorem box_exit_coordinates {X : Type*} [MetricSpace X]
    (e : Plane → X) (he : IsOpenEmbedding e) (p : I → X) (hp : Continuous p)
    (hzero : p 0 ∈ e '' openBox 1) (hone : p 1 ∉ e '' box 2) :
    ∃ q : I → Plane, Continuous q ∧ q 0 ∈ openBox 1 ∧
      (∀ t, q t ∈ box 2) ∧ ‖q 1‖ = 2 ∧ range (e ∘ q) ⊆ range p := by
  have hopen : IsOpen (e '' openBox 2) := he.isOpenMap _ isOpen_ball
  have hinside : e '' openBox 2 ⊆ interior (e '' box 2) :=
    hopen.subset_interior_iff.mpr (image_mono ball_subset_closedBall)
  have hstart : p 0 ∈ interior (e '' box 2) := by
    apply hinside
    apply image_mono (ball_subset_ball (by norm_num : (1:ℝ) ≤ 2)) hzero
  obtain ⟨b,hb,hfront,hbefore⟩ := first_exit
    ((isCompact_closedBall (0:Plane) 2).image he.continuous).isClosed p hp hstart hone
  let P : Path (p 0) (p 1) := ⟨⟨p,hp⟩,rfl,rfl⟩
  let Q := P.subpath 0 b
  have hQ (t : I) : Q t ∈ e '' box 2 := by
    have ht : Q t ∈ range Q := mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ zero_le] at ht
    obtain ⟨s,hs,hst⟩ := ht
    rw [← hst]
    exact hbefore s hs.2
  obtain ⟨q,hq,heq⟩ := continuous_lift he.isEmbedding Q Q.continuous
    (fun t => image_subset_range _ _ (hQ t))
  have hqmem (t : I) : q t ∈ box 2 := by
    obtain ⟨z,hz,hezt⟩ := hQ t
    exact (he.injective (hezt.trans (heq t).symm)) ▸ hz
  have hqzero : q 0 ∈ openBox 1 := by
    obtain ⟨z,hz,hez⟩ := hzero
    have hq0 : e (q 0) = p 0 := (heq 0).trans Q.source
    exact (he.injective (hez.trans hq0.symm)) ▸ hz
  refine ⟨q,hq,hqzero,hqmem,?_,?_⟩
  · have hle : ‖q 1‖ ≤ 2 := by simpa [box] using hqmem 1
    apply le_antisymm hle
    by_contra hn
    have hlt : q 1 ∈ openBox 2 := by simpa [openBox] using lt_of_not_ge hn
    have hbad := hinside (mem_image_of_mem e hlt)
    have hq1 : e (q 1) = p b := (heq 1).trans Q.target
    rw [hq1] at hbad
    exact hfront.2 hbad
  · rintro _ ⟨t,rfl⟩
    change e (q t) ∈ range p
    rw [heq]
    have ht : Q t ∈ range Q := mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ zero_le] at ht
    exact image_subset_range _ _ ht

theorem chart_strip_crossing {X : Type*} [MetricSpace X]
    (e : Plane → X) (he : IsOpenEmbedding e) (p : I → X) (hp : Continuous p)
    (hzero : p 0 ∈ e '' openBox 1) (hone : p 1 ∉ e '' box 2) :
    ∃ (j : Fin 4) (q : I → Plane), Continuous q ∧
      (q 0).1 = 1 ∧ (q 1).1 = 2 ∧
      (∀ t, (q t).1 ∈ Icc 1 2 ∧ |(q t).2| ≤ 2) ∧
      range (e ∘ (sideOrientation j).symm ∘ q) ⊆ range p := by
  obtain ⟨q,hq,hqzero,hqmem,hqone,hsub⟩ := box_exit_coordinates e he p hp hzero hone
  obtain ⟨j,hj⟩ := side_at_frontier hqone
  let f : I → Plane := sideOrientation j ∘ q
  have hf : Continuous f := (sideOrientation j).continuous.comp hq
  have hfzero : (f 0).1 ≤ 1 := by
    have hn : ‖f 0‖ < 1 := by
      simpa [f, norm_sideOrientation, openBox] using hqzero
    have hx : |(f 0).1| < 1 := (max_lt_iff.mp (by simpa [Prod.norm_def] using hn)).1
    exact (le_abs_self _).trans hx.le
  obtain ⟨a,b,hab,ha,hb,hbetween⟩ := CannonAnnular.radial_subinterval
    (fun t => (f t).1) hf.fst 1 2 (by norm_num) hfzero (le_of_eq hj.symm)
  let P : Path (f 0) (f 1) := ⟨⟨f,hf⟩,rfl,rfl⟩
  let Q := P.subpath a b
  refine ⟨j,Q,Q.continuous,?_,?_,?_,?_⟩
  · rw [Q.source]
    exact ha
  · rw [Q.target]
    exact hb
  · intro t
    have ht : Q t ∈ range Q := mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ hab.le] at ht
    obtain ⟨s,hs,hst⟩ := ht
    rw [← hst]
    refine ⟨hbetween s hs,?_⟩
    have hn : ‖f s‖ ≤ 2 := by simpa [f, norm_sideOrientation, box] using hqmem s
    change |(f s).2| ≤ 2
    exact (max_le_iff.mp (by simpa [Prod.norm_def] using hn)).2
  · rintro _ ⟨t,rfl⟩
    have ht : Q t ∈ range Q := mem_range_self t
    rw [Path.range_subpath_of_le _ _ _ hab.le] at ht
    obtain ⟨s,_,hs⟩ := ht
    change e ((sideOrientation j).symm (Q t)) ∈ range p
    rw [← hs]
    change e ((sideOrientation j).symm (sideOrientation j (q s))) ∈ range p
    rw [Homeomorph.symm_apply_apply]
    exact hsub (mem_range_self s)

end CannonCharts

end
end
end
end
end
end
end
end
end

end OAI
