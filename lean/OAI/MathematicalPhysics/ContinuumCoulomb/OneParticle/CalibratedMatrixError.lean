import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockGraphEntries
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactCalibratedGeometry

namespace OAI

/-! The approximate edge calibrations control the entire hopping matrix.
Simplicity prevents an edge error from acquiring a graph-size factor. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
variable {Edge : Type*} [Fintype Edge]

theorem graphHoppingMatrix_stability (m : ℕ) (left right : Edge → Fin (m+1))
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e=left f ∧ right e=right f) ∧ ¬(left e=right f ∧ right e=left f))
    (t s : Edge → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hedge : ∀ e, ‖t e-s e‖ ≤ ε) (i j : Fin (m+1)) :
    ‖graphHoppingMatrix m left right t i j-graphHoppingMatrix m left right s i j‖ ≤ ε := by
  classical
  by_cases hij : i=j
  · subst j
    rw [graphHoppingMatrix_diagonal m left right t hloop,
      graphHoppingMatrix_diagonal m left right s hloop,sub_self,norm_zero]
    exact hε
  by_cases he : ∃ e, (i=left e ∧ j=right e) ∨ (i=right e ∧ j=left e)
  · obtain ⟨e,he|he⟩ := he
    · rcases he with ⟨rfl,rfl⟩
      simpa only [graphHoppingMatrix_edge m left right _ hloop hsimple] using hedge e
    · rcases he with ⟨rfl,rfl⟩
      rw [graphHoppingMatrix_symmetric m left right t,
        graphHoppingMatrix_symmetric m left right s]
      simpa only [graphHoppingMatrix_edge m left right _ hloop hsimple] using hedge e
  · have hn : ∀ e, ¬(i=left e ∧ j=right e) ∧ ¬(i=right e ∧ j=left e) := by
      intro e
      exact ⟨fun h => he ⟨e,Or.inl h⟩,fun h => he ⟨e,Or.inr h⟩⟩
    rw [graphHoppingMatrix_nonedge m left right t i j hn,
      graphHoppingMatrix_nonedge m left right s i j hn,sub_self,norm_zero]
    exact hε

theorem planarHoppingMatrix_calibrated_error (m : ℕ)
    (left right : Edge → Fin (m+1)) (u : Fin (m+1) → PlanarPosition)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e=left f ∧ right e=right f) ∧ ¬(left e=right f ∧ right e=left f))
    {scale D L ε : ℝ} (hscale : 0 ≤ scale) (hD : 2 ≤ D) (hε : 0 ≤ ε)
    (hL : ∀ i j, ‖u i-u j‖ ≤ L)
    (hsep : ∀ i j, i ≠ j →
      (∀ e, ¬(i=left e ∧ j=right e) ∧ ¬(i=right e ∧ j=left e)) → D ≤ ‖u i-u j‖)
    (target : Edge → ℝ)
    (hres : ∀ e, |scale*planarHopping ‖u (left e)-u (right e)‖-target e| ≤ ε)
    (i j : Fin (m+1)) :
    ‖((scale*planarHoppingMatrix u i j:ℝ):ℂ)-
      graphHoppingMatrix m left right (fun e => (-(target e):ℝ)) i j‖ ≤
        scale*planarHoppingUpperConstant*(L+1)*Real.exp (-D)+ε := by
  let actual : Edge → ℂ := fun e => (-(scale*planarHopping ‖u (left e)-u (right e)‖):ℝ)
  have hc := graphHoppingMatrix_stability m left right hloop hsimple actual
    (fun e => (-(target e):ℝ)) hε (fun e => ?_) i j
  · exact (norm_sub_le_norm_sub_add_norm_sub _ (graphHoppingMatrix m left right actual i j) _).trans
      (add_le_add (planarHoppingMatrix_graph_error m left right u hloop hsimple
        hscale hD hL hsep i j) hc)
  · simpa only [actual,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      neg_sub_neg,abs_sub_comm] using hres e

end ContinuumCoulomb.HubbardGlobal

end

end OAI
