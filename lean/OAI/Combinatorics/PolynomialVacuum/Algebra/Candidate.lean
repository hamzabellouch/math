import OAI.Combinatorics.PolynomialVacuum.Algebra.PrescriptionDegree
import OAI.Combinatorics.PolynomialVacuum.Algebra.RegularInterpolation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical PolynomialVacuumInterpolation

noncomputable def dividedCupPrescription {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) : MvPolynomial (Fin (n+1)) ℂ :=
  C (1+T)*leftFusionFactors i*transportCup i (rightSpectators i) (initialCup ψ i) s

theorem cupPrescription_factor {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) : cupPrescription ψ i s=X i*dividedCupPrescription ψ i s := by
  unfold cupPrescription dividedCupPrescription
  ring

def CollisionCompatible {m : ℕ} (V : Fin m → MvPolynomial (Fin m) ℂ) : Prop :=
  ∀ i j, mergeVariable i j (V i)=mergeVariable i j (V j)

noncomputable def canonicalInterpolant {m : ℕ} (V : Fin m → MvPolynomial (Fin m) ℂ) :
    Polynomial (MvPolynomial (Fin m) ℂ) :=
  if h : CollisionCompatible V then
    (regular_lagrange_exists Finset.univ V (fun i _ j _ => h i j)).choose
  else 0

theorem canonicalInterpolant_degree {m : ℕ} (V : Fin m → MvPolynomial (Fin m) ℂ) :
    (canonicalInterpolant V).degree < (m : WithBot ℕ) := by
  unfold canonicalInterpolant
  split_ifs with h
  · simpa using (regular_lagrange_exists Finset.univ V (fun i _ j _ => h i j)).choose_spec.1
  · simp

theorem canonicalInterpolant_eval {m : ℕ} (V : Fin m → MvPolynomial (Fin m) ℂ)
    (h : CollisionCompatible V) (i : Fin m) : (canonicalInterpolant V).eval (X i)=V i := by
  unfold canonicalInterpolant
  rw [dite_eq_left h]
  exact (regular_lagrange_exists Finset.univ V (fun i _ j _ => h i j)).choose_spec.2 i (Finset.mem_univ _)

 

noncomputable def reinsertLast {m : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℂ)) :
    MvPolynomial (Fin (m+1)) ℂ :=
  p.eval₂ (rename Fin.castSucc).toRingHom (C T⁻¹*X (Fin.last m))

noncomputable def interpolateState {n : ℕ} (ψ : State n) (χ : State (n+1)) : State (n+2) :=
  fun s =>
    let V := fun i => cupPrescription ψ i s
    let W := fun i => dividedCupPrescription ψ i s
    let z : MvPolynomial (Fin (n+2)) ℂ := C T⁻¹*X (Fin.last (n+1))
    if s (Fin.last (n+1))=Spin.plus then reinsertLast (canonicalInterpolant V)
    else z*reinsertLast (canonicalInterpolant W) +
      if s (Fin.last (n+1))=Spin.zero then
        (∏ i : Fin (n+1), (X i.castSucc-z))*rename Fin.castSucc (χ (s ∘ Fin.castSucc))
      else 0

noncomputable def vacuumCandidate : Family
  | 0 => fun _ => 1
  | 1 => fun s => if s 0=Spin.zero then 1 else 0
  | n+2 => interpolateState (vacuumCandidate n) (vacuumCandidate (n+1))

 

def CandidateCollisionObligation : Prop :=
  ∀ n (s : Fin (n+2) → Spin),
    CollisionCompatible (fun i => cupPrescription (vacuumCandidate n) i s)

 
def CandidateVacuumObligation : Prop := IsPolynomialVacuum vacuumCandidate

end PolynomialVacuumAlgebra

end OAI
