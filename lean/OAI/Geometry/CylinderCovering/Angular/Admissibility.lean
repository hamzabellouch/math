import OAI.Geometry.CylinderCovering.Angular.GeneralDefinitions
import OAI.Geometry.CylinderCovering.Angular.Partition
import OAI.Geometry.TriangularCovering.Main

namespace OAI

open Set
noncomputable section
namespace CylinderCovering.AngularGeneral

lemma node_abs_le_one {D : Data} (hzero : D.node 0 = -1) (hlast : D.node D.count = 1)
    (hstep : ∀ j < D.count, D.node j < D.node (j+1)) :
    ∀ j ≤ D.count, |D.node j| ≤ 1 := by
  have hm := (AngularPartition.node_strictMonoOn D.node hstep).monotoneOn
  intro j hj
  have hlo := hm (show 0 ∈ Iic D.count by simp) (show j ∈ Iic D.count from hj)
    (Nat.zero_le j)
  have hhi := hm (show j ∈ Iic D.count from hj) (show D.count ∈ Iic D.count by simp) hj
  rw [hzero] at hlo
  rw [hlast] at hhi
  exact abs_le.mpr ⟨hlo,hhi⟩

theorem admissible_of_adjacent_matching {τ η E : ℝ} {D : Data}
    (hcount : 0 < D.count) (hzero : D.node 0 = -1) (hlast : D.node D.count = 1)
    (hstep : ∀ j < D.count, D.node j < D.node (j+1))
    (hmatch : ∀ j, j+1 < D.count →
      D.alpha j-D.node (j+1)*D.beta j =
        D.alpha (j+1)-D.node (j+1)*D.beta (j+1))
    (hleft : D.alpha 0+D.beta 0=0)
    (hright : D.alpha (D.count-1)-D.beta (D.count-1)=0)
    (hcont : ∀ j < D.count, ContinuousOn (D.radius j) (interval D j))
    (hpos : ∀ j < D.count, ∀ q ∈ interval D j, 0 < D.radius j q)
    (herror : ∀ j < D.count, ∀ q ∈ interval D j,
      |D.alpha j-(1+q^2)/4| ≤ E*τ^2 ∧
      |D.beta j-q/2| ≤ E*τ^2 ∧
      |D.radius j q-(1/2+τ^2*(profile q+η))| ≤ E*τ^4) :
    Admissible τ η E D := by
  refine ⟨hcount,hzero,hlast,hstep,node_abs_le_one hzero hlast hstep,?_,hcont,hpos,herror⟩
  exact AngularPartition.exists_compatible_boundary_endpoints hcount D.node D.alpha D.beta
    hzero hlast hstep hmatch hleft hright

theorem admissible_ordinary_secants {τ η E : ℝ} {D : Data} (hE : 0 ≤ E)
    (hcount : 0 < D.count) (hzero : D.node 0 = -1) (hlast : D.node D.count = 1)
    (hstep : ∀ j < D.count, D.node j < D.node (j+1))
    (halpha : ∀ j < D.count,
      D.alpha j = TriangularCovering.alpha (D.node j) (D.node (j+1)))
    (hbeta : ∀ j < D.count,
      D.beta j = TriangularCovering.beta (D.node j) (D.node (j+1)))
    (hwidth : ∀ j < D.count, D.node (j+1)-D.node j ≤ E*τ^2)
    (hcont : ∀ j < D.count, ContinuousOn (D.radius j) (interval D j))
    (hpos : ∀ j < D.count, ∀ q ∈ interval D j, 0 < D.radius j q)
    (hcap : ∀ j < D.count, ∀ q ∈ interval D j,
      |D.radius j q-(1/2+τ^2*(profile q+η))| ≤ E*τ^4) :
    Admissible τ η E D := by
  apply admissible_of_adjacent_matching hcount hzero hlast hstep
  · intro j hj
    rw [halpha j (by omega),hbeta j (by omega),halpha (j+1) hj,hbeta (j+1) hj]
    dsimp [TriangularCovering.alpha,TriangularCovering.beta]
    ring
  · rw [halpha 0 hcount,hbeta 0 hcount,hzero]
    dsimp [TriangularCovering.alpha,TriangularCovering.beta]
    ring
  · have hm : D.count-1+1=D.count := by omega
    rw [halpha (D.count-1) (by omega),hbeta (D.count-1) (by omega),hm,hlast]
    dsimp [TriangularCovering.alpha,TriangularCovering.beta]
    ring
  · exact hcont
  · exact hpos
  · intro j hj q hq
    have hnodes := node_abs_le_one hzero hlast hstep
    have ha := hnodes j hj.le
    have hb := hnodes (j+1) (by omega)
    have hq' : D.node j ≤ q ∧ q ≤ D.node (j+1) := hq
    have hqabs : |q| ≤ 1 := abs_le.mpr
      ⟨(abs_le.mp ha).1.trans hq'.1,hq'.2.trans (abs_le.mp hb).2⟩
    have hea := TriangularCovering.alpha_error ha hqabs hq'.1 hq'.2
    have heb := TriangularCovering.beta_error hq'.1 hq'.2
    have hnonneg : 0 ≤ E*τ^2 := mul_nonneg hE (sq_nonneg τ)
    refine ⟨?_,?_,hcap j hj q hq⟩
    · rw [halpha j hj]
      exact hea.trans (by linarith [hwidth j hj])
    · rw [hbeta j hj]
      exact heb.trans (by linarith [hwidth j hj])

end CylinderCovering.AngularGeneral

end

end OAI
