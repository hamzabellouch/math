import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedYYFactors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSubdivisionSites

namespace OAI

/-! The literal rational YY-to-XZ subdivision, retaining ordered source sites. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedYY
open Matrix QuantumOrderedSubdivision
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def outputWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    κ × Fin 4 → (ι ⊕ κ → Fin 4) :=
  fun p => qmaXZSubdivisionWord (factor (xs p.1) (w p.1)).1
    (factor (xs p.1) (w p.1)).2 p.1 p.2

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 4) : ℚ :=
  QuantumOrderedSubdivision.outputCoefficient J N p

def outputSites (xs : κ → List ι) (p : κ × Fin 4) : List (ι ⊕ κ) :=
  ![[],[Sum.inr p.1],appendMediator (xs p.1) p.1,appendMediator (xs p.1) p.1] p.2

omit [Fintype κ] in
theorem output_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 4) (i : ι ⊕ κ) :
    outputWord xs w p i ≠ 2 := by
  obtain ⟨ha,hb,_⟩ := factors (xs p.1) (w p.1) (hlen p.1)
    (hx p.1) (hcover p.1) (he p.1)
  exact qmaXZSubdivision_noY _ _ _ ha hb p.2 i

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup)
    (p : κ × Fin 4) : (outputSites xs p).Nodup := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · exact List.nodup_nil
  · exact List.nodup_singleton _
  · exact appendMediator_nodup _ (hx e) e
  · exact appendMediator_nodup _ (hx e) e

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_length (xs : κ → List ι) (hlen : ∀ e, (xs e).length ≤ 2)
    (p : κ × Fin 4) : (outputSites xs p).length ≤ 3 := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change 0 ≤ 3; omega
  · change 1 ≤ 3; omega
  · change (appendMediator (xs e) e).length ≤ 3
    rw [appendMediator_length]
    have := hlen e
    omega
  · change (appendMediator (xs e) e).length ≤ 3
    rw [appendMediator_length]
    have := hlen e
    omega

theorem outputSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 4) :
    qmaPauliSupport (outputWord xs w p) ⊆ (outputSites xs p).toFinset := by
  rcases p with ⟨e,k⟩
  obtain ⟨_,_,ha,hb,_⟩ := factors (xs e) (w e) (hlen e) (hx e) (hcover e) (he e)
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] at hx
    | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
        simpa [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] using hx
      simpa [outputSites] using qmaSinglePauliWord_support e 3 hj
  · exact join_support_cover (xs e) _ ha e 1
  · exact join_support_cover (xs e) _ hb e 1

theorem output_accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (outputWord xs w)
        (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let a := fun e => (factor (xs e) (w e)).1
  let b := fun e => (factor (xs e) (w e)).2
  have hf (e : κ) := factors (xs e) (w e) (hlen e) (hx e) (hcover e) (he e)
  have hfactor (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) = qmaPauliWord (w e) :=
    (hf e).2.2.2.2.1
  have hcomm (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e) := (hf e).2.2.2.2.2
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaXZSubdivision_accuracy a b (fun e => (J e:ℝ)) hcomm hNR
  simp only [qmaPauliFamily,outputWord,outputCoefficient,
    QuantumOrderedSubdivision.outputCoefficient,QuantumPolarizedSubdivision.weight_cast,
    QuantumOrderedSubdivision.scale_cast]
  simpa only [hfactor,a,b] using h

end ContinuumCoulomb.QuantumOrderedYY

end

end OAI
