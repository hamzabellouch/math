import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedYYReduction
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZPrivate

namespace OAI

/-! A literal private-pair subdivision of an ordered X/Z family.  The
source site's list order determines both factors and every output site. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedPrivate
open Matrix QuantumOrderedSubdivision
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def outputWord (xs : κ → List ι) (w : κ → ι → Fin 4) :
    κ × Fin 4 → (ι ⊕ κ → Fin 4) :=
  fun p => qmaXZSubdivisionWord
    (QuantumOrderedSplit.firstWord (xs p.1) 1 (w p.1))
    (QuantumOrderedSplit.secondWord (xs p.1) 1 (w p.1)) p.1 p.2

def outputSites (xs : κ → List ι) : κ × Fin 4 → List (ι ⊕ κ) :=
  QuantumOrderedSubdivision.outputSites xs 1

def outputCoefficient (J : κ → ℚ) (N : ℕ) (p : κ × Fin 4) : ℚ :=
  QuantumOrderedSubdivision.outputCoefficient J N p

omit [Fintype ι] [Fintype κ] in
theorem output_noY (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hy : ∀ e i, w e i ≠ 2) (p : κ × Fin 4) (i : ι ⊕ κ) :
    outputWord xs w p i ≠ 2 :=
  qmaXZSubdivision_noY _ _ _ (qmaPauliRestrict_noY _ _ (hy p.1))
    (qmaPauliRestrict_noY _ _ (hy p.1)) _ _

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup)
    (p : κ × Fin 4) : (outputSites xs p).Nodup :=
  QuantumOrderedSubdivision.outputSites_nodup xs 1 hx p

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem outputSites_length (xs : κ → List ι) (hx : ∀ e, (xs e).length ≤ 2)
    (p : κ × Fin 4) : (outputSites xs p).length ≤ 2 :=
  QuantumOrderedSubdivision.outputSites_length xs 1 hx p

theorem outputSites_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (p : κ × Fin 4) :
    qmaPauliSupport (outputWord xs w p) ⊆ (outputSites xs p).toFinset := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · change qmaPauliSupport (fun _ : ι ⊕ κ => 0) ⊆ ([] : List (ι ⊕ κ)).toFinset
    simp [qmaPauliSupport]
  · intro x hx
    cases x with
    | inl i => simp [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] at hx
    | inr j =>
      have hj : j ∈ qmaPauliSupport (qmaSinglePauliWord e 3) := by
        simpa [outputWord,qmaXZSubdivisionWord,qmaPauliSupport] using hx
      simpa [outputSites,QuantumOrderedSubdivision.outputSites] using
        qmaSinglePauliWord_support e 3 hj
  · exact join_support_cover ((xs e).take 1)
      (QuantumOrderedSplit.firstWord (xs e) 1 (w e))
      (qmaPauliRestrict_support _ _) e 1
  · exact join_support_cover ((xs e).drop 1)
      (QuantumOrderedSplit.secondWord (xs e) 1 (w e))
      (qmaPauliRestrict_support _ _) e 1

theorem output_private (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup) (p q : κ × Fin 4)
    (hp : (qmaPauliSupport (outputWord xs w p)).card = 2)
    (hpq : qmaPauliSupport (outputWord xs w p) = qmaPauliSupport (outputWord xs w q)) :
    p = q := by
  have hd (e : κ) : Disjoint
      (qmaPauliSupport (QuantumOrderedSplit.firstWord (xs e) 1 (w e)))
      (qmaPauliSupport (QuantumOrderedSplit.secondWord (xs e) 1 (w e))) :=
    (QuantumOrderedSplit.disjoint (xs e) (hx e) 1).mono
      (qmaPauliRestrict_support _ _) (qmaPauliRestrict_support _ _)
  obtain ⟨he,hk⟩ := qmaXZSubdivision_private_pair
    (fun e => QuantumOrderedSplit.firstWord (xs e) 1 (w e))
    (fun e => QuantumOrderedSplit.secondWord (xs e) 1 (w e)) hd p.1 q.1 p.2 q.2 hp hpq
  exact Prod.ext he hk

theorem output_accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (outputWord xs w)
        (fun p => (outputCoefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 1/(N:ℝ) := by
  let a := fun e => QuantumOrderedSplit.firstWord (xs e) 1 (w e)
  let b := fun e => QuantumOrderedSplit.secondWord (xs e) 1 (w e)
  have hfactor (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) = qmaPauliWord (w e) :=
    QuantumOrderedSplit.factor (xs e) (hx e) 1 (w e) (hcover e)
  have hcomm (e : κ) : qmaPauliWord (a e)*qmaPauliWord (b e) =
      qmaPauliWord (b e)*qmaPauliWord (a e) :=
    QuantumOrderedSplit.commute (xs e) (hx e) 1 (w e)
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have h := qmaXZSubdivision_accuracy a b (fun e => (J e:ℝ)) hcomm hNR
  simp only [qmaPauliFamily,outputWord,outputCoefficient,
    QuantumOrderedSubdivision.outputCoefficient,QuantumPolarizedSubdivision.weight_cast,
    QuantumOrderedSubdivision.scale_cast]
  simpa only [hfactor,a,b] using h

end ContinuumCoulomb.QuantumOrderedPrivate

end

end OAI
