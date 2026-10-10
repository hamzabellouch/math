import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockSiteOneBody
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarMultiwellMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHoppingBounds

namespace OAI

/-! Entrywise control of the unwanted hopping between nonadjacent sites
in the actual localized one-body matrix. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb.HubbardGlobal

variable {Edge : Type*} [Fintype Edge]

theorem graphHoppingMatrix_symmetric (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ) (i j : Fin (m+1)) :
    graphHoppingMatrix m left right t i j = graphHoppingMatrix m left right t j i := by
  unfold graphHoppingMatrix
  apply Finset.sum_congr rfl
  intro e _
  simp only [and_comm]
  rw [add_comm]

theorem graphHoppingMatrix_diagonal (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e) (i : Fin (m+1)) :
    graphHoppingMatrix m left right t i i = 0 := by
  unfold graphHoppingMatrix
  apply Finset.sum_eq_zero
  intro e _
  have h : ¬ (i=left e ∧ i=right e) := fun h => hloop e (h.1.symm.trans h.2)
  simp only [h,and_comm,ite_false,add_zero]

theorem graphHoppingMatrix_edge (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e=left f ∧ right e=right f) ∧ ¬(left e=right f ∧ right e=left f))
    (e : Edge) : graphHoppingMatrix m left right t (left e) (right e) = t e := by
  unfold graphHoppingMatrix
  rw [Finset.sum_eq_single e]
  · simp [hloop e]
  · intro f _ hfe
    have h := hsimple e f (Ne.symm hfe)
    simp only [h.1,h.2,ite_false,add_zero]
  · intro he
    exact (he (Finset.mem_univ e)).elim

theorem graphHoppingMatrix_nonedge (m : ℕ)
    (left right : Edge → Fin (m+1)) (t : Edge → ℂ) (i j : Fin (m+1))
    (h : ∀ e, ¬(i=left e ∧ j=right e) ∧ ¬(i=right e ∧ j=left e)) :
    graphHoppingMatrix m left right t i j = 0 := by
  unfold graphHoppingMatrix
  exact Finset.sum_eq_zero (fun e _ => by simp only [(h e).1,(h e).2,ite_false,add_zero])

theorem planarHoppingMatrix_graph_error (m : ℕ)
    (left right : Edge → Fin (m+1)) (u : Fin (m+1) → PlanarPosition)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e=left f ∧ right e=right f) ∧ ¬(left e=right f ∧ right e=left f))
    {scale D L : ℝ} (hscale : 0 ≤ scale) (hD : 2 ≤ D)
    (hL : ∀ i j, ‖u i-u j‖ ≤ L)
    (hsep : ∀ i j, i ≠ j →
      (∀ e, ¬(i=left e ∧ j=right e) ∧ ¬(i=right e ∧ j=left e)) → D ≤ ‖u i-u j‖)
    (i j : Fin (m+1)) :
    ‖((scale*planarHoppingMatrix u i j:ℝ):ℂ) -
      graphHoppingMatrix m left right
        (fun e => (-(scale*planarHopping ‖u (left e)-u (right e)‖):ℝ)) i j‖ ≤
      scale*planarHoppingUpperConstant*(L+1)*Real.exp (-D) := by
  have hL0 : 0 ≤ L := by simpa only [sub_self,norm_zero] using hL i i
  have hLp : 0 ≤ L+1 := by linarith
  have hbound : 0 ≤ scale*planarHoppingUpperConstant*(L+1)*Real.exp (-D) :=
    mul_nonneg (mul_nonneg (mul_nonneg hscale planarHoppingUpperConstant_positive.le) hLp)
      (Real.exp_pos _).le
  by_cases hij : i=j
  · subst j
    rw [graphHoppingMatrix_diagonal m left right _ hloop]
    simpa only [planarHoppingMatrix,ite_true,mul_zero,Complex.ofReal_zero,sub_zero,norm_zero]
      using hbound
  by_cases he : ∃ e, (i=left e ∧ j=right e) ∨ (i=right e ∧ j=left e)
  · obtain ⟨e,he|he⟩ := he
    · rcases he with ⟨rfl,rfl⟩
      rw [graphHoppingMatrix_edge m left right _ hloop hsimple]
      simpa only [planarHoppingMatrix,ite_eq_right (hloop e),mul_neg,Complex.ofReal_neg,
        sub_self,norm_zero] using hbound
    · rcases he with ⟨rfl,rfl⟩
      rw [graphHoppingMatrix_symmetric,graphHoppingMatrix_edge m left right _ hloop hsimple]
      rw [planarHoppingMatrix,ite_eq_right (Ne.symm (hloop e))]
      simpa only [norm_sub_rev,mul_neg,Complex.ofReal_neg,sub_self,norm_zero] using hbound
  · have hn : ∀ e, ¬(i=left e ∧ j=right e) ∧ ¬(i=right e ∧ j=left e) := by
      intro e
      exact ⟨fun h => he ⟨e,Or.inl h⟩,fun h => he ⟨e,Or.inr h⟩⟩
    rw [graphHoppingMatrix_nonedge m left right _ i j hn,sub_zero]
    have hd := hsep i j hij hn
    have hh := planarHopping_sharp_upper (hD.trans hd)
    rw [Complex.norm_real,Real.norm_eq_abs,planarHoppingMatrix,ite_eq_right hij,
      abs_mul,abs_of_nonneg hscale,abs_neg,abs_of_pos (planarHopping_positive _)]
    have htail : planarHoppingUpperConstant*(‖u i-u j‖+1)*Real.exp (-‖u i-u j‖) ≤
        planarHoppingUpperConstant*(L+1)*Real.exp (-D) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith [hL i j]) planarHoppingUpperConstant_positive.le)
        (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
        (mul_nonneg planarHoppingUpperConstant_positive.le hLp)
    calc
      _ ≤ scale*(planarHoppingUpperConstant*(L+1)*Real.exp (-D)) :=
        mul_le_mul_of_nonneg_left (hh.trans htail) hscale
      _ = _ := by ring

end ContinuumCoulomb.HubbardGlobal

end

end OAI
