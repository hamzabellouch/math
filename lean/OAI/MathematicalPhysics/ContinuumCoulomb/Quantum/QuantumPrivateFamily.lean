import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateAccuracy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateRaw

namespace OAI

/-! The private subdivision has ordinary finite indices and feeds the checked compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPrivate
open Matrix
open scoped BigOperators Classical
variable {n m : ℕ}

def familyTerm (t : Fin m → QMAXZTerm n) (p : Fin (m*4)) : QMAXZTerm (n+m) :=
  let e := (finProdFinEquiv : Fin m × Fin 4 ≃ Fin (m*4)).symm p
  term e.1 (t e.1) e.2

def familyWeight (N : ℕ) (J : Fin m → ℚ) (p : Fin (m*4)) : ℚ :=
  let e := (finProdFinEquiv : Fin m × Fin 4 ≃ Fin (m*4)).symm p
  weight (scale N J) (J e.1) e.2

theorem family_private (t : Fin m → QMAXZTerm n) (p q : Fin (m*4))
    (hp : (qmaPauliSupport (familyTerm t p).word).card = 2)
    (he : qmaPauliSupport (familyTerm t p).word = qmaPauliSupport (familyTerm t q).word) : p = q := by
  apply (finProdFinEquiv : Fin m × Fin 4 ≃ Fin (m*4)).symm.injective
  exact term_private t _ _ hp he

theorem family_accuracy (N : ℕ) (hN : 0 < N) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    |MediatorGraph.normalizedBottom (∑ p : Fin (m*4), (familyWeight N J p:ℂ) • (familyTerm t p).matrix)-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 1/(N:ℝ) := by
  have hs : (∑ p : Fin (m*4), (familyWeight N J p:ℂ) • (familyTerm t p).matrix) =
      ∑ p : Fin m × Fin 4, (weight (scale N J) (J p.1) p.2:ℂ) • (term p.1 (t p.1) p.2).matrix :=
    Fintype.sum_equiv (finProdFinEquiv : Fin m × Fin 4 ≃ Fin (m*4)).symm _ _ (by intro p; rfl)
  rw [hs]
  exact accuracy N hN t J

theorem compiled_accuracy (N : ℕ) (hN : 0 < N) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    |MediatorGraph.normalizedBottom (QuantumRawExchange.rawMatrix ((n+m)*4)
        (QuantumRawExchange.compile (n+m,N,QuantumRawExchange.packed (familyTerm t) (familyWeight N J))))-
      MediatorGraph.normalizedBottom (∑ e, (J e:ℂ) • (t e).matrix)| ≤ 3/(N:ℝ) := by
  have h₁ := QuantumRawExchange.compile_accuracy N hN (familyTerm t) (familyWeight N J) (family_private t)
  have h₂ := family_accuracy N hN t J
  apply (abs_sub_le _ _ _).trans (add_le_add h₁ h₂ |>.trans _)
  exact le_of_eq (by ring)

end ContinuumCoulomb.QuantumPrivate

end

end OAI
