import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumQuadraticReindex

namespace OAI

/-! The distributed history bounds transported to the actual tensor-qubit basis. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaDistributedQubit_lower (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (hsound : ∀ psi : EuclideanSpace ℂ (SourceSpinBasis c.witness),
      ‖psi‖ = 1 → qmaAcceptance c hc psi ≤ 1/3)
    (u : (QMACircuitQubit c → Fin 2) → ℂ) :
    (2/(5*(c.gates.length+1:ℝ)))*(∑ i, Complex.normSq (u i)) ≤
      qmaQuadratic (qmaDistributedQubitHamiltonian c τ) u := by
  let e := qmaCircuitQubitSplit c
  have h := qmaUnaryDistributedHamiltonian_sound c hc τ hi hsound
    (WithLp.toLp 2 (u ∘ e.symm))
  simp only [EuclideanSpace.norm_sq_eq,Complex.sq_norm] at h
  have hm : (∑ i, Complex.normSq ((u ∘ e.symm) i)) = ∑ i, Complex.normSq (u i) :=
    qmaMass_reindex e u
  rw [hm] at h
  unfold qmaDistributedQubitHamiltonian
  rw [qmaQuadratic_reindex_equiv]
  have hd : 0 < 5*(c.gates.length+1:ℝ) := by positivity
  calc
    _ = (2*(∑ i, Complex.normSq (u i)))/(5*(c.gates.length+1:ℝ)) := by ring
    _ ≤ _ := (div_le_iff₀ hd).mpr (by simpa only [mul_comm] using h)

theorem qmaDistributedQubit_accepting (c : QMACircuit) (hc : c.WellFormed)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1))
    (hi : ∀ i, ∀ g ∈ c.gates.take (τ i).val, i ∉ qmaGateSites c.work g)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) (hpsi : ‖psi‖ = 1)
    (hacc : 2/3 ≤ qmaAcceptance c hc psi) :
    ∃ u : (QMACircuitQubit c → Fin 2) → ℂ,
      (∑ i, Complex.normSq (u i)) = 1 ∧
      3*(c.gates.length+1:ℝ)*qmaQuadratic (qmaDistributedQubitHamiltonian c τ) u ≤ 1 := by
  obtain ⟨v,hv,he⟩ := qmaUnaryDistributedHamiltonian_accepting c hc τ hi psi hpsi hacc
  let e := qmaCircuitQubitSplit c
  refine ⟨(fun s => v (e s)),?_,?_⟩
  · have hm := e.sum_comp (fun p => Complex.normSq (v p))
    rw [hm]
    have hn := congrArg (fun t : ℝ => t^2) hv
    simpa only [EuclideanSpace.norm_sq_eq,Complex.sq_norm,one_pow] using hn
  · unfold qmaDistributedQubitHamiltonian
    rw [qmaQuadratic_reindex_equiv]
    have hh : (fun s => v (e s)) ∘ e.symm = fun p => v p := by funext p; simp
    rw [hh]
    exact he

end ContinuumCoulomb

end

end OAI
