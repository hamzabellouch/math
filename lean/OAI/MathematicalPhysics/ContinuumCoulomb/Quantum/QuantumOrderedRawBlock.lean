import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZTerm
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCompiler
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliRounding

namespace OAI

/-! The existing literal rational four-spin compiler applied to the actual
ordered X/Z words. Its input list preserves term and endpoint order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedRawBlock
open scoped BigOperators Classical

def terms {n m : ℕ} (xs : Fin m → List (Fin n)) (w : Fin m → Fin n → Fin 4) :
    Fin m → QMAXZTerm n := fun e => QuantumOrderedXZTerm.ofSites (xs e) (w e)

def output {n m : ℕ} (N : ℕ) (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ) :=
  QuantumRawExchange.compile (n,N,QuantumRawExchange.packed (terms xs w) J)

theorem private_terms {n m : ℕ} (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hs : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset) (hy : ∀ e i, w e i ≠ 2)
    (hp : ∀ e f, (qmaPauliSupport (w e)).card = 2 →
      qmaPauliSupport (w e) = qmaPauliSupport (w f) → e = f) :
    ∀ e f, (qmaPauliSupport (terms xs w e).word).card = 2 →
      qmaPauliSupport (terms xs w e).word = qmaPauliSupport (terms xs w f).word → e = f := by
  intro e f he hef
  have ht (i : Fin m) : (terms xs w i).word = w i :=
    QuantumOrderedXZTerm.word_eq (xs i) (w i) (hlen i) (hx i) (hs i) (hy i)
  rw [ht e] at he
  rw [ht e,ht f] at hef
  exact hp e f he hef

theorem output_accuracy {n m : ℕ} (N : ℕ) (hN : 0 < N)
    (xs : Fin m → List (Fin n)) (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ)
    (hlen : ∀ e, (xs e).length ≤ 2) (hx : ∀ e, (xs e).Nodup)
    (hs : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset) (hy : ∀ e i, w e i ≠ 2)
    (hp : ∀ e f, (qmaPauliSupport (w e)).card = 2 →
      qmaPauliSupport (w e) = qmaPauliSupport (w f) → e = f) :
    |MediatorGraph.normalizedBottom (QuantumRawExchange.rawMatrix (n*4) (output N xs w J))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 2/(N:ℝ) := by
  have h := QuantumRawExchange.compile_accuracy N hN (terms xs w) J
    (private_terms xs w hlen hx hs hy hp)
  have ht (e : Fin m) : (terms xs w e).matrix = qmaPauliWord (w e) :=
    QuantumOrderedXZTerm.matrix_eq (xs e) (w e) (hlen e) (hx e) (hs e) (hy e)
  have hc (q : ℚ) : ((q:ℝ):ℂ) = (q:ℂ) := by norm_cast
  simpa only [output,qmaPauliFamily,hc,ht] using h

theorem output_valid {n m : ℕ} (N : ℕ) (xs : Fin m → List (Fin n))
    (w : Fin m → Fin n → Fin 4) (J : Fin m → ℚ)
    (b : MediatorListProgram.Bond) (hb : b ∈ (output N xs w J).1) :
    b.1 < n*4 ∧ b.2.1 < n*4 ∧ b.1 ≠ b.2.1 :=
  QuantumRawExchange.compile_valid N (terms xs w) J b hb

end ContinuumCoulomb.QuantumOrderedRawBlock

end

end OAI
