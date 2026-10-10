import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPolarizedSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionGadget
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliRounding

namespace OAI

/-! An explicit simultaneous subdivision of an ordered rational Pauli
family.  This is the actual four-word Hamiltonian, with a rational scale
and a full-space ground-energy estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSubdivision
open Matrix
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def budget (J : κ → ℚ) : ℚ := 4*(1+∑ e, (1+|J e|)^2)
def scale (J : κ → ℚ) (N : ℕ) : ℚ := 8*(budget J)^4*N

omit [DecidableEq κ] in
theorem budget_cast (J : κ → ℚ) :
    (budget J:ℝ) = qmaThirdBudget 0 (fun e => (J e:ℝ)) := by
  simp [budget,qmaThirdBudget,qmaThirdWeight]

omit [DecidableEq κ] in
theorem scale_cast (J : κ → ℚ) (N : ℕ) :
    (scale J N:ℝ) = 8*(qmaThirdBudget 0 (fun e => (J e:ℝ)))^4*N := by
  simp [scale,budget_cast]

def phase (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4) : κ → Bool :=
  fun e => decide (Odd (qmaPauliYCount (QuantumOrderedSplit.firstWord (xs e) d (w e))))

def outputWord (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4) :
    κ × Fin 4 → (ι ⊕ κ → Fin 4) :=
  fun p => QuantumPolarizedSubdivision.word
    (QuantumOrderedSplit.firstWord (xs p.1) d (w p.1))
    (QuantumOrderedSplit.secondWord (xs p.1) d (w p.1)) p.1 (phase xs d w) p.2

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 4) : ℚ :=
  QuantumPolarizedSubdivision.weight (scale J N) (J p.1) p.2

theorem output_support (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2*d) (p : κ × Fin 4) :
    (qmaPauliSupport (outputWord xs d w p)).card ≤ d+1 :=
  QuantumPolarizedSubdivision.support _ _ _ _
    (QuantumOrderedSplit.first_support (xs p.1) d (w p.1))
    (QuantumOrderedSplit.second_support (xs p.1) d (w p.1) (hlen p.1)) p.2

theorem output_even (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4)
    (hxs : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 4) :
    Even (qmaPauliYCount (outputWord xs d w p)) := by
  exact QuantumPolarizedSubdivision.even
    (QuantumOrderedSplit.firstWord (xs p.1) d (w p.1))
    (QuantumOrderedSplit.secondWord (xs p.1) d (w p.1)) p.1 (phase xs d w) rfl
    (QuantumOrderedSplit.same_parity (xs p.1) (hxs p.1) d (w p.1)
      (hcover p.1) (he p.1)) p.2

theorem output_accuracy (xs : κ → List ι) (d : ℕ) (w : κ → ι → Fin 4)
    (J : κ → ℚ) (hxs : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom
        (qmaPauliFamily (outputWord xs d w) (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let A := fun e => qmaPauliWord (QuantumOrderedSplit.firstWord (xs e) d (w e))
  let B := fun e => qmaPauliWord (QuantumOrderedSplit.secondWord (xs e) d (w e))
  let m := phase xs d w
  have hAB (e : κ) : A e*B e = B e*A e :=
    QuantumOrderedSplit.commute (xs e) (hxs e) d (w e)
  have hfactor (e : κ) : A e*B e = qmaPauliWord (w e) :=
    QuantumOrderedSplit.factor (xs e) (hxs e) d (w e) (hcover e)
  have hsum : qmaPauliFamily (outputWord xs d w) (fun p => (outputCoefficient J N p:ℝ)) =
      qmaSubdivisionOnQubits 0 A B (scale J N:ℝ) (fun e => (J e:ℝ)) m := by
    have hc (q : ℚ) : ((q:ℝ):ℂ) = (q:ℂ) := by norm_cast
    simp only [qmaPauliFamily,Fintype.sum_prod_type,outputWord,outputCoefficient,hc]
    simp_rw [QuantumPolarizedSubdivision.sum_eq]
    unfold qmaSubdivisionOnQubits
    rw [qmaSubdivisionPolarized_decomposition]
    simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum,
      qmaSubdivisionPiece_reindex]
    rfl
  have htarget : qmaSubdivisionTarget 0 A B (fun e => ((J e:ℝ):ℂ)) =
      qmaPauliFamily w (fun e => (J e:ℝ)) := by
    simp only [qmaSubdivisionTarget,zero_add,hfactor,qmaPauliFamily]
  rw [hsum,qmaSubdivisionOnQubits_bottom,← htarget]
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaSubdivision_polynomial_accuracy 0 A B (fun e => (J e:ℝ))
    (by norm_num : (0:ℝ) ≤ 0) hNR Matrix.conjTranspose_zero (by simp)
    (fun e => qmaPauliWord_hermitian _) (fun e => qmaPauliWord_hermitian _)
    (fun e => qmaPauliWord_square _) (fun e => qmaPauliWord_square _) hAB
    (EuclideanSpace.single (fun _ : ι => (0:Fin 2)) (1:ℂ)) (by simp [PiLp.norm_single])
  simpa only [scale_cast] using h

end ContinuumCoulomb.QuantumOrderedSubdivision

end

end OAI
