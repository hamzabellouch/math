import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialGadgets
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZSupported
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZFamily

namespace OAI

/-! X/Z conversion with explicit neighboring-cell support and constant density. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

structure QMASpatialXZModel (A B : ℕ) extends QMAXZModel where
  rows : ℕ
  width : ℕ
  cell : Q → QMAGridCell rows width
  anchor : Term → QMAGridCell rows width
  geometry : ∀ e, ∀ q ∈ qmaPauliSupport (word e), QMAGridCellsNear (cell q) (anchor e)
  qubitDensity : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A
  termDensity : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B

theorem qmaSpatialXZ_of_stages {A B : ℕ} (M : QMASpatialModel 2 A B)
    (v : ((QMALocalEvenPauliTerm M.sites × Fin 4) × Fin 7) →
      ((M.Q ⊕ QMALocalEvenPauliTerm M.sites) ⊕ (QMALocalEvenPauliTerm M.sites × Fin 4)) → Fin 4)
    (K : ((QMALocalEvenPauliTerm M.sites × Fin 4) × Fin 7) → ℝ)
    (hvy : ∀ e i, v e i ≠ 2) (hv : ∀ e, (qmaPauliSupport (v e)).card ≤ 2)
    (hvs : ∀ e, qmaPauliSupport (v e) ⊆
      qmaMediatorSupport (qmaMediatorSupport
        (qmaPauliSupport (qmaLocalPauliWord M.sites e.1.1.val)) e.1.1) e.1) :
    ∃ G : QMASpatialXZModel (A+80*B) (448*B),
      G.toQMAXZModel = QMAXZModel.ofWords v K hvy hv ∧ G.rows = M.rows ∧ G.width = M.width := by
  let E := QMALocalEvenPauliTerm M.sites
  let a₀ := fun p : E => M.anchor p.val.1
  let c₁ := qmaMediatorCell M.cell a₀
  let a₁ := fun p : E × Fin 4 => a₀ p.1
  let c₂ := qmaMediatorCell c₁ a₁
  let a₂ := fun p : (E × Fin 4) × Fin 7 => a₁ p.1
  have hE (p : QMAGridCell M.rows M.width) :
      (Finset.univ.filter (fun e : E => a₀ e = p)).card ≤ 16*B := by
    have h := qmaLocalEvenPauli_filter_card M.sites M.card (fun a => M.anchor a = p)
    exact h.trans (Nat.mul_le_mul_left 16 (M.termDensity p))
  have hT (p : QMAGridCell M.rows M.width) :
      (Finset.univ.filter (fun e : E × Fin 4 => a₁ e = p)).card ≤ 64*B := by
    change (Finset.univ.filter (fun e : E × Fin 4 => a₀ e.1 = p)).card ≤ _
    rw [qmaProdFilter_card (α := E) 4 (fun e => a₀ e = p)]
    exact (Nat.mul_le_mul_left 4 (hE p)).trans (by omega)
  have hC₁ (p : QMAGridCell M.rows M.width) :
      (Finset.univ.filter (fun q : M.Q ⊕ E => c₁ q = p)).card ≤ A+16*B := by
    rw [qmaSumFilter_card]
    exact Nat.add_le_add (M.qubitDensity p) (hE p)
  have hU (e : E × Fin 4) (q : M.Q ⊕ E)
      (hq : q ∈ qmaMediatorSupport
        (qmaPauliSupport (qmaLocalPauliWord M.sites e.1.val)) e.1) :
      QMAGridCellsNear (c₁ q) (a₁ e) := by
    apply qmaMediatorSupport_geometry M.cell a₀ (M.sites e.1.val.1) e.1
      (M.geometry e.1.val.1) q
    exact (qmaMediatorSupport_mono (qmaPauliExtend_support _ _) e.1) hq
  let G : QMASpatialXZModel (A+80*B) (448*B) := {
    toQMAXZModel := QMAXZModel.ofWords v K hvy hv
    rows := M.rows
    width := M.width
    cell := c₂
    anchor := a₂
    geometry := by
      intro e q hq
      exact qmaMediatorSupport_geometry c₁ a₁
        (qmaMediatorSupport (qmaPauliSupport (qmaLocalPauliWord M.sites e.1.1.val)) e.1.1) e.1
        (hU e.1) q (hvs e hq)
    qubitDensity := by
      intro p
      change (Finset.univ.filter (fun q : (M.Q ⊕ E) ⊕ (E × Fin 4) => c₂ q = p)).card ≤ _
      rw [qmaSumFilter_card]
      exact (Nat.add_le_add (hC₁ p) (hT p)).trans (by omega)
    termDensity := by
      intro p
      change (Finset.univ.filter (fun e : (E × Fin 4) × Fin 7 => a₁ e.1 = p)).card ≤ _
      rw [qmaProdFilter_card (α := E × Fin 4) 7 (fun e => a₁ e = p)]
      exact (Nat.mul_le_mul_left 7 (hT p)).trans (by omega) }
  exact ⟨G,rfl,rfl,rfl⟩

theorem QMASpatialModel.toXZ {A B : ℕ} (M : QMASpatialModel 2 A B)
    {N : ℝ} (hN : 1 ≤ N) :
    ∃ G : QMASpatialXZModel (A+80*B) (448*B),
      |G.toQMAXZModel.energy-M.toQMARealLocalModel.energy| ≤ 1/N ∧
      G.rows = M.rows ∧ G.width = M.width := by
  let E := QMALocalEvenPauliTerm M.sites
  obtain ⟨v,K,hvy,hv,hvs,he⟩ := qmaTwoLocalXZ_supported
    (fun p : E => qmaLocalPauliWord M.sites p.val)
    (fun p => qmaLocalPauliCoefficient M.matrix M.sites p.val)
    (qmaLocalEvenPauli_support M.sites M.card) (qmaLocalEvenPauli_even M.sites) hN
  obtain ⟨G,hG,hr,hw⟩ := qmaSpatialXZ_of_stages M v K hvy hv hvs
  refine ⟨G,?_,hr,hw⟩
  have hs := qmaLocalEvenPauli_sum M.matrix M.sites M.localOn M.hermitian M.real
  change (∑ e : E, (qmaLocalPauliCoefficient M.matrix M.sites e.val:ℂ) •
    qmaPauliWord (qmaLocalPauliWord M.sites e.val)) = ∑ a, M.matrix a at hs
  rw [hG]
  change |(QMAXZModel.ofWords v K hvy hv).energy-M.toQMARealLocalModel.energy| ≤ 1/N
  rw [QMAXZModel.ofWords_energy,QMARealLocalModel.energy,← hs]
  convert he using 1
  congr 2
  exact qmaNormalizedBottom_instances _ _ _ _ _

end ContinuumCoulomb

end

end OAI
