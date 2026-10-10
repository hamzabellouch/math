import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialExchange
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialReindex

namespace OAI

/-! The private-pair spatial X/Z model has a spatial rational exchange simulator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem QMASpatialXZModel.toExchange {A B : ℕ} (M : QMASpatialXZModel A B)
    (hprivate : ∀ p q, (qmaPauliSupport (M.word p)).card = 2 →
      qmaPauliSupport (M.word p) = qmaPauliSupport (M.word q) → p = q)
    (N : ℕ) (hN : 0 < N) :
    ∃ G : QMASpatialExchangeModel (4*A) (6*A+25*B),
      G.rows = M.rows ∧ G.width = M.width ∧
      |G.energy-M.toQMAXZModel.energy| ≤ 2/(N:ℝ) := by
  let E := Fintype.equivFin M.Q
  let w := fun a => M.word a ∘ E.symm
  have hy : ∀ a i, w a i ≠ 2 := fun a i => M.noY a (E.symm i)
  have hw : ∀ a, (qmaPauliSupport (w a)).card ≤ 2 := by
    intro a
    rw [qmaPauliSupport_relabel,Finset.card_map]
    exact M.card a
  choose t ht using fun a => qmaXZWord_term (w a) (hy a) (hw a)
  have hp : ∀ a b, (qmaPauliSupport (t a).word).card = 2 →
      qmaPauliSupport (t a).word = qmaPauliSupport (t b).word → a = b := by
    intro a b ha hab
    simp only [ht,w,qmaPauliSupport_relabel,Finset.card_map] at ha hab
    exact hprivate a b ha (Finset.map_injective E.toEmbedding hab)
  have hl : ∀ a, ∀ i ∈ qmaPauliSupport (t a).word,
      QMAGridCellsNear (M.cell (E.symm i)) (M.anchor a) := by
    intro a i hi
    rw [ht] at hi
    apply M.geometry a (E.symm i)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have hc : ∀ p, (Finset.univ.filter (fun i => M.cell (E.symm i) = p)).card ≤ A :=
    (M.reindex E).qubitDensity
  obtain ⟨G,hr,hwG,he⟩ := qmaSpatialXZTerms_exchange t M.coefficient
    (fun i => M.cell (E.symm i)) M.anchor hl hc M.termDensity hp N hN
  refine ⟨G,hr,hwG,?_⟩
  have hm : (∑ a, (M.coefficient a:ℂ) • (t a).matrix) =
      ∑ a, (M.coefficient a:ℂ) • qmaPauliWord (w a) := by
    simp only [← QMAXZTerm.word_matrix,ht]
  rw [hm] at he
  change |G.energy-(M.reindex E).toQMAXZModel.energy| ≤ _ at he
  rwa [M.reindex_energy E] at he

end ContinuumCoulomb

end

end OAI
