import OAI.Analysis.CircleDomains.Topology.DiskRayJordan
import OAI.Analysis.CircleDomains.Topology.BoundaryArcComplement
import OAI.Analysis.CircleDomains.Topology.ConnectedDiskIntersection

namespace OAI

/-! The two actual Jordan sides of a disk crosscut closed by one circle arc. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma disk_crosscut_norm_le {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (t : PathTime) : ‖p t‖ ≤ 1 := by
  by_cases ht0 : t = 0
  · simp only [ht0, p.source, ha, le_refl]
  by_cases ht1 : t = 1
  · simp only [ht1, p.target, norm_one, le_refl]
  exact (hp t ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), lt_of_le_of_ne le_top ht1⟩).le

lemma disk_crosscut_circle_subset {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) :
    range p ∩ sphere (0 : ℂ) 1 ⊆ range (boundaryClosingArc a ha) := by
  rintro z ⟨⟨t,rfl⟩,hz⟩
  by_cases ht0 : t = 0
  · exact ⟨1, by simp only [ht0, p.source, (boundaryClosingArc a ha).target]⟩
  by_cases ht1 : t = 1
  · exact ⟨0, by simp only [ht1, p.target, (boundaryClosingArc a ha).source]⟩
  have hh := hp t ⟨lt_of_le_of_ne bot_le (Ne.symm ht0), lt_of_le_of_ne le_top ht1⟩
  exact (ne_of_lt hh (mem_sphere_zero_iff_norm.mp hz)).elim

lemma exists_disk_crosscut_jordan (hsch : PlanarSchoenflies)
    {a : ℂ} (p : Path a 1) (hi : Injective p)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1) (ha : ‖a‖ = 1) (ha1 : a ≠ 1) :
    ∃ H : ℂ ≃ₜ ℂ,
      frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha) ∧
      closure (jordanInterior H) ⊆ closedBall (0 : ℂ) 1 ∧
      jordanInterior H ⊆ ball (0 : ℂ) 1 := by
  obtain ⟨H,hH⟩ := exists_schoenflies_of_disk_crosscut hsch p hi hp ha ha1
  have hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha) := by
    rw [frontier_jordanInterior_eq_circle_range H _ hH]
    have hr : range (fun z : Circle => circleOfClosedPath (p.trans (boundaryClosingArc a ha))
        ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm z)) =
        range (circleOfClosedPath (p.trans (boundaryClosingArc a ha))) := by
      ext z
      constructor
      · rintro ⟨w,rfl⟩; exact mem_range_self _
      · rintro ⟨w,rfl⟩
        exact ⟨(AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) w, by simp⟩
    rw [hr,circleOfClosedPath_range]
    exact Path.trans_range _ _
  have hc : closure (jordanInterior H) ⊆ closedBall (0 : ℂ) 1 := by
    apply jordan_fill_subset_closed_unitDisk
    intro z hz
    rw [hf] at hz
    rcases hz with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · exact disk_crosscut_norm_le p ha hp t
    · exact (boundaryClosingArc_norm _ _ t).le
  refine ⟨H,hf,hc,?_⟩
  have hh := interior_mono hc
  rwa [interior_closure_jordanInterior, interior_closedBall _ one_ne_zero] at hh

lemma disk_crosscut_exterior_circle {a : ℂ} (p : Path a 1) (ha : ‖a‖ = 1)
    (hp : ∀ t ∈ Ioo (0 : PathTime) 1, ‖p t‖ < 1)
    (H : ℂ ≃ₜ ℂ)
    (hf : frontier (jordanInterior H) = range p ∪ range (boundaryClosingArc a ha))
    (hinside : jordanInterior H ⊆ ball (0 : ℂ) 1) :
    (closure (jordanInterior H))ᶜ ∩ sphere (0 : ℂ) 1 =
      sphere (0 : ℂ) 1 \ range (boundaryClosingArc a ha) := by
  ext z
  constructor
  · rintro ⟨hz,hzs⟩
    exact ⟨hzs,fun h => hz (frontier_subset_closure (hf ▸ Or.inr h))⟩
  · rintro ⟨hzs,hza⟩
    refine ⟨?_,hzs⟩
    rw [closure_eq_self_union_frontier,hf]
    rintro (hzJ | hzp | hza')
    · have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp (hinside hzJ)
      exact ne_of_lt hn (mem_sphere_zero_iff_norm.mp hzs)
    · exact hza (disk_crosscut_circle_subset p ha hp ⟨hzp,hzs⟩)
    · exact hza hza'

end CircleDomainRigidity

end

end OAI
