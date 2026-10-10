import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialTotal

namespace OAI

/-! Finite qubit relabeling preserves the spatial data and the exact Hamiltonian spectrum. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {Q R : Type*} [Fintype Q] [DecidableEq Q] [Fintype R] [DecidableEq R]

def qmaQubitBasisEquiv (e : Q ≃ R) : (R → Fin 2) ≃ (Q → Fin 2) :=
  Equiv.arrowCongr e.symm (Equiv.refl (Fin 2))

omit [DecidableEq Q] [DecidableEq R] in
theorem qmaPauliWord_relabel (e : Q ≃ R) (w : Q → Fin 4) :
    qmaPauliWord (w ∘ e.symm) =
      (qmaPauliWord w).submatrix (qmaQubitBasisEquiv e) (qmaQubitBasisEquiv e) := by
  ext s t
  change (∏ r, qmaPauli (w (e.symm r)) (s r) (t r)) =
    ∏ q, qmaPauli (w q) (s (e q)) (t (e q))
  exact Fintype.prod_equiv e.symm _ _ (by intro r; simp)

omit [DecidableEq Q] [DecidableEq R] in
theorem qmaPauliSupport_relabel (e : Q ≃ R) (w : Q → Fin 4) :
    qmaPauliSupport (w ∘ e.symm) = (qmaPauliSupport w).map e.toEmbedding := by
  ext r
  simp only [Finset.mem_map_equiv,qmaPauliSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  rfl

def QMASpatialXZModel.reindex {A B : ℕ} (M : QMASpatialXZModel A B)
    {R : Type} [Fintype R] [DecidableEq R] (e : M.Q ≃ R) : QMASpatialXZModel A B where
  toQMAXZModel := QMAXZModel.ofWords (fun a => M.word a ∘ e.symm) M.coefficient
    (fun a r => M.noY a (e.symm r))
    (fun a => by rw [qmaPauliSupport_relabel,Finset.card_map]; exact M.card a)
  rows := M.rows
  width := M.width
  cell r := M.cell (e.symm r)
  anchor := M.anchor
  geometry := by
    intro a r hr
    apply M.geometry a (e.symm r)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2⟩
  qubitDensity := by
    intro p
    change (Finset.univ.filter (fun r : R => M.cell (e.symm r) = p)).card ≤ A
    have he : (Finset.univ.filter (fun r : R => M.cell (e.symm r) = p)).card =
        (Finset.univ.filter (fun q : M.Q => M.cell q = p)).card := by
      apply Finset.card_equiv e.symm
      intro r
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [he]
    exact M.qubitDensity p
  termDensity := M.termDensity

theorem QMASpatialXZModel.reindex_energy {A B : ℕ} (M : QMASpatialXZModel A B)
    {R : Type} [Fintype R] [DecidableEq R] (e : M.Q ≃ R) :
    (M.reindex e).toQMAXZModel.energy = M.toQMAXZModel.energy := by
  change MediatorGraph.normalizedBottom (∑ a, (M.coefficient a:ℂ) • qmaPauliWord (M.word a ∘ e.symm)) = _
  simp only [qmaPauliWord_relabel]
  have hs : (∑ a, (M.coefficient a:ℂ) •
      (qmaPauliWord (M.word a)).submatrix (qmaQubitBasisEquiv e) (qmaQubitBasisEquiv e)) =
      (∑ a, (M.coefficient a:ℂ) • qmaPauliWord (M.word a)).submatrix
        (qmaQubitBasisEquiv e) (qmaQubitBasisEquiv e) := by
    ext s t
    simp only [Matrix.sum_apply,Matrix.smul_apply,Matrix.submatrix_apply]
  rw [hs]
  exact MediatorGraph.normalizedBottom_reindex (qmaQubitBasisEquiv e) _

end ContinuumCoulomb

end

end OAI
