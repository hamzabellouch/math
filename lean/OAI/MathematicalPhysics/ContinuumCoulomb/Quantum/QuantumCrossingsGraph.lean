import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumParallelGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCalibration

namespace OAI

/-! Ordinary spin edges and polynomial full-space error for a parallel crossing-elimination round. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaCrossingsBaseLeft {n r : ℕ} (left : ν → Fin n) (site : Fin r → Fin 4 → Fin n) :
    ν ⊕ (Fin r × Fin 4) → Fin n := Sum.elim left (fun p => site p.1 (qmaCrossingLeft p.2))
def qmaCrossingsBaseRight {n r : ℕ} (right : ν → Fin n) (site : Fin r → Fin 4 → Fin n) :
    ν ⊕ (Fin r × Fin 4) → Fin n := Sum.elim right (fun p => site p.1 (qmaCrossingRight p.2))
def qmaCrossingsBaseWeight {r : ℕ} (weight : ν → ℝ) (J K : Fin r → ℝ) :
    ν ⊕ (Fin r × Fin 4) → ℝ := Sum.elim weight (fun p => qmaCrossingWeight (J p.1) (K p.1) p.2)

omit [Fintype ν] in
theorem qmaCrossingsBase_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) :
    ∀ a, qmaCrossingsBaseLeft left site a ≠ qmaCrossingsBaseRight right site a := by
  intro a
  cases a with
  | inl a => exact hneq a
  | inr p =>
    intro h
    have hh := hsite p.1 h
    rcases p with ⟨e,a⟩
    fin_cases a <;> norm_num [qmaCrossingLeft,qmaCrossingRight] at hh

theorem qmaCrossingsBase_matrix {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant : ℝ) (site : Fin r → Fin 4 → Fin n) (J K : Fin r → ℝ) :
    qmaExchangeMatrix (qmaCrossingsBaseLeft left site) (qmaCrossingsBaseRight right site)
      (qmaCrossingsBaseWeight weight J K) (constant+∑ e, qmaCrossingOffset (J e) (K e)) =
      qmaExchangeMatrix left right weight constant +
        ∑ e, qmaCrossingCorrection (site e) (J e) (K e) := by
  simp only [qmaCrossingCorrection_exchange,qmaExchangeMatrix,Fintype.sum_sum_type,
    Fintype.sum_prod_type,qmaCrossingsBaseLeft,qmaCrossingsBaseRight,qmaCrossingsBaseWeight,
    Sum.elim_inl,Sum.elim_inr,Complex.ofReal_add,Complex.ofReal_sum,add_smul,
    Finset.sum_add_distrib,Finset.sum_smul]
  abel

def qmaCrossingsGraph {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (site : Fin r → Fin 4 → Fin n) (J K : Fin r → ℝ) :
    Matrix (SourceSpinBasis (n+r*2)) (SourceSpinBasis (n+r*2)) ℂ :=
  qmaExchangeMatrix
    (qmaParallelGraphLeft (qmaCrossingsBaseLeft left site) site)
    (qmaParallelGraphRight (qmaCrossingsBaseRight right site) (fun _ => qmaCrossingMember))
    (qmaParallelGraphWeight (qmaCrossingsBaseWeight weight J K) (R^2)
      (fun e => qmaCrossingAmplitude R (J e) (K e)))
    ((constant+∑ e, qmaCrossingOffset (J e) (K e))+3*r*(R^2))

theorem qmaCrossingsGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R : ℝ)
    (site : Fin r → Fin 4 → Fin n) (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    (qmaCrossingsGraph left right weight constant R site J K).submatrix
      (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r (R^2)
        (qmaExchangeMatrix left right weight constant+∑ e, qmaCrossingCorrection (site e) (J e) (K e))
        site (fun _ => qmaCrossingMember) (fun e => qmaCrossingAmplitude R (J e) (K e)) := by
  unfold qmaCrossingsGraph
  simpa only [qmaCrossingsBase_matrix] using
    qmaParallelGraph_matrix _ _ (qmaCrossingsBase_distinct left right hneq site hsite)
      (qmaCrossingsBaseWeight weight J K) (constant+∑ e, qmaCrossingOffset (J e) (K e)) (R^2)
      site (fun _ => qmaCrossingMember) (fun e => qmaCrossingAmplitude R (J e) (K e))

theorem qmaCrossingsGraph_accuracy {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ)
    (site : Fin r → Fin 4 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (J K : Fin r → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |weight a|)+|constant|
    let A := 6*∑ e, (1+|J e|+|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+r*2) (qmaCrossingsGraph left right weight constant R site J K) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)))| ≤ 1/N := by
  dsimp only
  rw [sourceMatrixBottom_eq_mediator n r,qmaCrossingsGraph_matrix left right hneq weight constant _ site hsite,
    qmaPhysicalParallel_bottom]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaCrossings_accuracy site hsite J K (by positivity) hN _ hC
    (qmaExchangeMatrix_lift_norm left right hneq weight constant)

end ContinuumCoulomb

end

end OAI
