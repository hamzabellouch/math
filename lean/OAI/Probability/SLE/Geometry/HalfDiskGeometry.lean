import OAI.Probability.SLE.Geometry.DiskSemicircleGeometry
import OAI.Probability.SLE.Geometry.ComplexJordanRegions
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! The two standard closed half disks and their bounded Jordan interiors. -/
noncomputable section
open Set Complex Metric

namespace SLEExactGauge

def closedUpperDisk : Set ℂ := {z | ‖z‖ ≤ 1 ∧ 0 ≤ z.im}
def openUpperDisk : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}

lemma closedUpperDisk_eq :
    closedUpperDisk=closedBall (0:ℂ) 1 ∩ Complex.imCLM ⁻¹' Ici 0 := by
  ext z
  simp [closedUpperDisk,mem_closedBall,dist_zero_right]

lemma closedUpperDisk_isClosed : IsClosed closedUpperDisk :=
  (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_im)

lemma closedUpperDisk_convex : Convex ℝ closedUpperDisk := by
  rw [closedUpperDisk_eq]
  exact (convex_closedBall _ _).inter ((convex_Ici (0:ℝ)).linear_preimage _)

lemma closedUpperDisk_interior : interior closedUpperDisk=openUpperDisk := by
  rw [closedUpperDisk_eq,interior_inter,interior_closedBall _ (by norm_num : (1:ℝ)≠0)]
  rw [Complex.imCLM.interior_preimage (fun x => ⟨x*I,by simp⟩),interior_Ici]
  ext z
  simp [openUpperDisk,mem_ball,dist_zero_right]

lemma openUpperDisk_nonempty : openUpperDisk.Nonempty := by
  refine ⟨I/2,?_,?_⟩
  · norm_num
  · norm_num

lemma openUpperDisk_isOpen : IsOpen openUpperDisk :=
  (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)

lemma openUpperDisk_convex : Convex ℝ openUpperDisk := by
  rw [← closedUpperDisk_interior]
  exact closedUpperDisk_convex.interior

lemma openUpperDisk_closure : closure openUpperDisk=closedUpperDisk := by
  rw [← closedUpperDisk_interior,
    closedUpperDisk_convex.closure_interior_eq_closure_of_nonempty_interior
      (by rw [closedUpperDisk_interior]; exact openUpperDisk_nonempty),
    closedUpperDisk_isClosed.closure_eq]

lemma openUpperDisk_frontier :
    frontier openUpperDisk=diskDiameter '' Icc 0 1 ∪ diskUpperArc '' Icc 0 1 := by
  rw [openUpperDisk_isOpen.frontier_eq,openUpperDisk_closure,
    diskDiameter_image,diskUpperArc_image]
  ext z
  simp only [mem_sdiff,closedUpperDisk,openUpperDisk,mem_ofPred,mem_union]
  constructor
  · rintro ⟨⟨hn,hi⟩,he⟩
    by_cases hz : z.im=0
    · exact Or.inl ⟨hn,hz⟩
    · exact Or.inr ⟨le_antisymm hn (le_of_not_gt (fun h => he ⟨h,lt_of_le_of_ne hi
        (Ne.symm hz)⟩)),hi⟩
  · rintro (⟨hn,hi⟩|⟨hn,hi⟩)
    · exact ⟨⟨hn,hi.ge⟩,fun h => by simpa only [hi,lt_self_iff_false] using h.2⟩
    · exact ⟨⟨hn.le,hi⟩,fun h => (not_lt_of_ge hn.ge) h.1⟩

theorem complexInside_upperDisk :
    complexInside (diskDiameter '' Icc 0 1 ∪ diskUpperArc '' Icc 0 1)=openUpperDisk := by
  apply complexInside_eq_open
    (disk_crosscut_upper_jordan diskDiameter diskDiameter_continuous.continuousOn
      diskDiameter_injOn (by norm_num [diskDiameter]) (by norm_num [diskDiameter])
      diskDiameter_interior)
    openUpperDisk_isOpen openUpperDisk_convex.isPreconnected openUpperDisk_nonempty
    ?_ openUpperDisk_frontier
  exact (isBounded_ball (x := (0:ℂ)) (r := 1)).subset (fun z hz => by
    simpa only [mem_ball,dist_zero_right] using hz.1)

end SLEExactGauge

end

end OAI
