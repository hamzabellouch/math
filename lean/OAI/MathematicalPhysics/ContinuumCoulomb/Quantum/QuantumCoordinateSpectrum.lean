import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalFamily
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalRealification

namespace OAI

/-! The local qubit-coordinate matrices retain the full-space spectral
bounds, through explicit basis equivalences. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : β ≃ α) (A : Matrix α α ℂ) (u : α → ℂ) :
    qmaQuadratic (A.submatrix e e) (u ∘ e) = qmaQuadratic A u := by
  have he : (u ∘ e) ∘ e.symm = u := by funext i; simp
  unfold qmaQuadratic
  rw [Matrix.submatrix_mulVec_equiv,he]
  change (∑ i : β, star (u (e i))*A.mulVec u (e i)).re =
    (∑ i : α, star (u i)*A.mulVec u i).re
  exact congrArg Complex.re (e.sum_comp (fun i => star (u i)*A.mulVec u i))

theorem qmaNorm_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : β ≃ α) (u : α → ℂ) : ‖WithLp.toLp 2 (u ∘ e)‖ = ‖WithLp.toLp 2 u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq,Function.comp_apply]
  exact e.sum_comp (fun i => ‖u i‖^2)

def qmaRebitQubitSplit (ι : Type*) : (Unit ⊕ ι → Fin 2) ≃ Fin 2 × (ι → Fin 2) where
  toFun s := (s (Sum.inl ()),s ∘ Sum.inr)
  invFun p := Sum.elim (fun _ => p.1) p.2
  left_inv s := by
    funext i
    cases i with
    | inl u => cases u; rfl
    | inr i => rfl
  right_inv p := rfl

def qmaRealCircuitQubitSplit (c : QMACircuit) :
    (Unit ⊕ QMACircuitQubit c → Fin 2) ≃ QMARealBasis c :=
  (qmaRebitQubitSplit (QMACircuitQubit c)).trans
    (Equiv.prodCongr (Equiv.refl _) (qmaCircuitQubitSplit c))

def qmaRealQubitHamiltonian (c : QMACircuit) := qmaRebitOnQubits (qmaQubitHamiltonian c)

theorem qmaRealQubitHamiltonian_reindex (c : QMACircuit) :
    qmaRealQubitHamiltonian c = (qmaRealHamiltonian c).submatrix
      (qmaRealCircuitQubitSplit c) (qmaRealCircuitQubitSplit c) := rfl

theorem qmaRealQubitHamiltonian_sound (c : QMACircuit) (hc : c.WellFormed)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : EuclideanSpace ℂ (Unit ⊕ QMACircuitQubit c → Fin 2)) :
    2*‖u‖^2 ≤ 5*(c.gates.length+1:ℝ)*
      qmaQuadratic (qmaRealQubitHamiltonian c) (fun p => u p) := by
  let e := qmaRealCircuitQubitSplit c
  let v := (fun p => u p) ∘ e.symm
  have hu : v ∘ e = fun p => u p := by funext p; simp [v]
  have hn := qmaNorm_reindex e v
  rw [hu] at hn
  have hq := qmaQuadratic_reindex e (qmaRealHamiltonian c) v
  rw [hu,←qmaRealQubitHamiltonian_reindex] at hq
  have h := qmaRealHamiltonian_sound c hc hsound (WithLp.toLp 2 v)
  simpa only [←hn,PiLp.toLp_apply,←hq] using h

theorem qmaRealQubitHamiltonian_accepting (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : EuclideanSpace ℂ (Unit ⊕ QMACircuitQubit c → Fin 2), ‖u‖ = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaRealQubitHamiltonian c) (fun p => u p) ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaRealHamiltonian_accepting c hc psi hpsi hacc
  let e := qmaRealCircuitQubitSplit c
  refine ⟨WithLp.toLp 2 ((fun p => v p) ∘ e),?_,?_⟩
  · rw [qmaNorm_reindex]
    exact hv
  · change 3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaRealQubitHamiltonian c)
      ((fun p => v p) ∘ e) ≤ 1
    rw [qmaRealQubitHamiltonian_reindex,qmaQuadratic_reindex]
    exact he

end ContinuumCoulomb

end

end OAI
