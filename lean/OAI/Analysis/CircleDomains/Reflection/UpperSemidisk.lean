import OAI.Analysis.CircleDomains.Reflection.SemidiskBarrier
import Mathlib.Analysis.Complex.Convex

namespace OAI

/-! The fixed half disks used in the local boundary argument. -/
open Set Function Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

def upperSemidisk (R : ℝ) : Set ℂ := ball 0 R∩{z : ℂ | 0<z.im}

lemma upperSemidisk_open (R : ℝ) : IsOpen (upperSemidisk R) :=
  isOpen_ball.inter (isOpen_lt continuous_const continuous_im)

lemma upperSemidisk_convex (R : ℝ) : Convex ℝ (upperSemidisk R) :=
  (convex_ball 0 R).inter (convex_halfSpace_im_gt 0)

lemma upperSemidisk_nonempty {R : ℝ} (hR : 0<R) : (upperSemidisk R).Nonempty := by
  refine ⟨((R/2 : ℝ) : ℂ)*I,?_,?_⟩
  · rw [mem_ball_zero_iff,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (half_pos hR)]
    linarith
  · simpa only [mem_ofPred_eq,mul_im,ofReal_re,I_im,mul_one,ofReal_im,I_re,mul_zero,
      add_zero] using half_pos hR

lemma upperSemidisk_closure_subset (R : ℝ) :
    closure (upperSemidisk R) ⊆ closedBall 0 R∩{z : ℂ | 0≤z.im} := by
  apply closure_minimal
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1,(show 0<z.im from hz.2).le⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const continuous_im)

lemma upperSemidisk_compact_closure (R : ℝ) : IsCompact (closure (upperSemidisk R)) :=
  (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
    (fun _ hz => (upperSemidisk_closure_subset R hz).1)

lemma upperSemidisk_frontier_nonempty {R : ℝ} (hR : 0<R) :
    (frontier (upperSemidisk R)).Nonempty := by
  apply nonempty_frontier_iff.mpr
  refine ⟨upperSemidisk_nonempty hR,?_⟩
  intro he
  have hz : (0 : ℂ)∈upperSemidisk R := he.symm ▸ mem_univ _
  exact (lt_irrefl (0 : ℝ)) (by simpa only [upperSemidisk,mem_inter_iff,mem_ofPred_eq,zero_im] using hz.2)

lemma upperSemidisk_frontier_cases {R : ℝ} {p : ℂ} (hp : p∈frontier (upperSemidisk R)) :
    ‖p‖≤R ∧ 0≤p.im ∧ (‖p‖=R ∨ p.im=0) := by
  have hb := upperSemidisk_closure_subset R hp.1
  have hn : ‖p‖≤R := mem_closedBall_zero_iff.mp hb.1
  refine ⟨hn,hb.2,?_⟩
  by_cases he : ‖p‖=R
  · exact Or.inl he
  · right
    by_contra hi
    have hpU : p∈upperSemidisk R :=
      ⟨mem_ball_zero_iff.mpr (lt_of_le_of_ne hn he),(lt_of_le_of_ne hb.2 (Ne.symm hi))⟩
    exact hp.2 ((upperSemidisk_open R).interior_eq.symm ▸ hpU)

end CircleDomainRigidity

end

end OAI
