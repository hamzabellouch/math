import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedTripleFactors
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPolarizedThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdEnvelope

namespace OAI

/-! The literal simultaneous rational three-to-two-local reduction, with
ordered factors and an ordinary full-Hilbert-space energy estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedThird
open Matrix QuantumOrderedTriple
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def phase (xs : κ → List ι) (w : κ → ι → Fin 4) : κ → Bool :=
  fun e => decide (Odd (qmaPauliYCount (first (xs e) (w e))))

def outputWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    κ × Fin 7 → (ι ⊕ κ → Fin 4) :=
  fun p => QuantumPolarizedThird.word (first (xs p.1) (w p.1))
    (second (xs p.1) (w p.1)) (third (xs p.1) (w p.1))
    (pairWord (xs p.1) (w p.1)) p.1 (phase xs w) p.2

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 7) : ℚ :=
  QuantumPolarizedThird.weight (QuantumOrderedSubdivision.scale J N) (J p.1) p.2

theorem output_support (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 7) :
    (qmaPauliSupport (outputWord xs w p)).card ≤ 2 := by
  obtain ⟨ha,hb,hc,_⟩ := factors (xs p.1) (w p.1) (hlen p.1)
    (hx p.1) (hcover p.1) (he p.1)
  exact QuantumPolarizedThird.support (first (xs p.1) (w p.1))
    (second (xs p.1) (w p.1)) (third (xs p.1) (w p.1))
    (pairWord (xs p.1) (w p.1)) p.1 (phase xs w) ha hb hc
    (pair_support _ _ (hlen p.1)) p.2

theorem output_even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : κ × Fin 7) :
    Even (qmaPauliYCount (outputWord xs w p)) := by
  obtain ⟨_,_,_,_,_,_,_,_,hpar,hc⟩ := factors (xs p.1) (w p.1) (hlen p.1)
    (hx p.1) (hcover p.1) (he p.1)
  exact QuantumPolarizedThird.even (first (xs p.1) (w p.1))
    (second (xs p.1) (w p.1)) (third (xs p.1) (w p.1))
    (pairWord (xs p.1) (w p.1)) p.1 (phase xs w) rfl hpar hc
    (pair_even _ _ (hlen p.1) (hx p.1) (hcover p.1) (he p.1)) p.2

theorem output_accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 3) (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (outputWord xs w)
        (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let A := fun e => qmaPauliWord (first (xs e) (w e))
  let B := fun e => qmaPauliWord (second (xs e) (w e))
  let C := fun e => qmaPauliWord (third (xs e) (w e))
  let m := phase xs w
  have hf (e : κ) := factors (xs e) (w e) (hlen e) (hx e) (hcover e) (he e)
  have hpair (e : κ) : A e*B e = qmaPauliWord (pairWord (xs e) (w e)) := (hf e).2.2.2.1
  have habc (e : κ) : A e*B e*C e = qmaPauliWord (w e) := (hf e).2.2.2.2.1
  have hab (e : κ) : A e*B e = B e*A e := (hf e).2.2.2.2.2.1
  have hac (e : κ) : A e*C e = C e*A e := (hf e).2.2.2.2.2.2.1
  have hbc (e : κ) : B e*C e = C e*B e := (hf e).2.2.2.2.2.2.2.1
  have hsum : qmaPauliFamily (outputWord xs w) (fun p => (outputCoefficient J N p:ℝ)) =
      (qmaThirdPhased 0 A B C (QuantumOrderedSubdivision.scale J N:ℝ)
        (fun e => (J e:ℝ)) m).submatrix
          (Equiv.sumArrowEquivProdArrow ι κ (Fin 2))
          (Equiv.sumArrowEquivProdArrow ι κ (Fin 2)) := by
    have hc (q : ℚ) : ((q:ℝ):ℂ) = (q:ℂ) := by norm_cast
    simp only [qmaPauliFamily,Fintype.sum_prod_type,outputWord,outputCoefficient,hc]
    simp_rw [QuantumPolarizedThird.sum_eq _ _ _ _ _ _ _ _ (hpair _)]
    rw [qmaThirdPhased_decomposition]
    simp only [Matrix.zero_kronecker,zero_add,MediatorGraph.submatrix_sum]
    rfl
  have htarget : qmaThirdSeriesTarget 0 A B C (fun e => ((J e:ℝ):ℂ)) =
      qmaPauliFamily w (fun e => (J e:ℝ)) := by
    simp only [qmaThirdSeriesTarget,zero_add,habc,qmaPauliFamily]
  rw [hsum,MediatorGraph.normalizedBottom_reindex,qmaThirdPhased_bottom,← htarget]
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaThirdGadget_polynomial_accuracy 0 A B C (fun e => (J e:ℝ))
    (by norm_num : (0:ℝ) ≤ 0) hNR Matrix.conjTranspose_zero (by simp)
    (fun _ => qmaPauliWord_hermitian _) (fun _ => qmaPauliWord_hermitian _)
    (fun _ => qmaPauliWord_hermitian _)
    (fun _ => qmaPauliWord_square _) (fun _ => qmaPauliWord_square _)
    (fun _ => qmaPauliWord_square _) hab hac hbc
    (EuclideanSpace.single (fun _ : ι => (0:Fin 2)) (1:ℂ)) (by simp [PiLp.norm_single])
  simpa only [QuantumOrderedSubdivision.scale_cast] using h

end ContinuumCoulomb.QuantumOrderedThird

end

end OAI
