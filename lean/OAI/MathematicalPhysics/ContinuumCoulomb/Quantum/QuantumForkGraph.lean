import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumParallelGraph

namespace OAI

/-! Ordinary spin edges and polynomial full-space error for a parallel fork round. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix MediatorGraph
open scoped BigOperators Kronecker Classical
variable {ν : Type*} [Fintype ν]

def qmaForksBaseLeft {n r : ℕ} (left : ν → Fin n) (site : Fin r → Fin 3 → Fin n) :
    ν ⊕ Fin r → Fin n := Sum.elim left (fun e => site e 1)
def qmaForksBaseRight {n r : ℕ} (right : ν → Fin n) (site : Fin r → Fin 3 → Fin n) :
    ν ⊕ Fin r → Fin n := Sum.elim right (fun e => site e 2)
def qmaForksBaseWeight {r : ℕ} (weight : ν → ℝ) (J K : Fin r → ℝ) :
    ν ⊕ Fin r → ℝ := Sum.elim weight (fun e => 2*J e*K e)

omit [Fintype ν] in
theorem qmaForksBase_distinct {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) :
    ∀ a, qmaForksBaseLeft left site a ≠ qmaForksBaseRight right site a := by
  intro a
  cases a with
  | inl a => exact hneq a
  | inr e => exact fun h => (by decide : (1 : Fin 3) ≠ 2) (hsite e h)

theorem qmaForksBase_matrix {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant : ℝ) (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℝ) :
    qmaExchangeMatrix (qmaForksBaseLeft left site) (qmaForksBaseRight right site)
      (qmaForksBaseWeight weight J K) (constant+∑ e, qmaForkOffset (J e) (K e)) =
      qmaExchangeMatrix left right weight constant +
        ∑ e, qmaForkCorrection (site e) (J e) (K e) := by
  simp only [qmaExchangeMatrix,Fintype.sum_sum_type,qmaForksBaseLeft,qmaForksBaseRight,
    qmaForksBaseWeight,Sum.elim_inl,Sum.elim_inr,qmaForkCorrection,qmaForkOffset,
    Complex.ofReal_add,Complex.ofReal_sum,add_smul,Finset.sum_add_distrib,Finset.sum_smul]
  abel

def qmaForksGraph {n r : ℕ} (left right : ν → Fin n) (weight : ν → ℝ)
    (constant R : ℝ) (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℝ) :
    Matrix (SourceSpinBasis (n+r*2)) (SourceSpinBasis (n+r*2)) ℂ :=
  qmaExchangeMatrix
    (qmaParallelGraphLeft (qmaForksBaseLeft left site) site)
    (qmaParallelGraphRight (qmaForksBaseRight right site) (fun _ => qmaForkMember))
    (qmaParallelGraphWeight (qmaForksBaseWeight weight J K) (R^2)
      (fun e => qmaForkAmplitude R (J e) (K e)))
    ((constant+∑ e, qmaForkOffset (J e) (K e))+3*r*(R^2))

theorem qmaForksGraph_matrix {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant R : ℝ)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    (qmaForksGraph left right weight constant R site J K).submatrix
      (basisEquiv n r) (basisEquiv n r) =
      qmaPhysicalParallelHamiltonian n r (R^2)
        (qmaExchangeMatrix left right weight constant+∑ e, qmaForkCorrection (site e) (J e) (K e))
        site (fun _ => qmaForkMember) (fun e => qmaForkAmplitude R (J e) (K e)) := by
  unfold qmaForksGraph
  simpa only [qmaForksBase_matrix] using
    qmaParallelGraph_matrix _ _ (qmaForksBase_distinct left right hneq site hsite)
      (qmaForksBaseWeight weight J K) (constant+∑ e, qmaForkOffset (J e) (K e)) (R^2)
      site (fun _ => qmaForkMember) (fun e => qmaForkAmplitude R (J e) (K e))

theorem qmaForksGraph_accuracy {n r : ℕ} (left right : ν → Fin n)
    (hneq : ∀ a, left a ≠ right a) (weight : ν → ℝ) (constant : ℝ)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (J K : Fin r → ℝ) {N : ℝ} (hN : 0 < N) :
    let B := 3*(∑ a, |weight a|)+|constant|
    let A := 3*∑ e, (1+2*|J e|+2*|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |sourceMatrixBottom (n+r*2) (qmaForksGraph left right weight constant R site J K) -
      sourceMatrixBottom n (qmaExchangeMatrix left right weight constant + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤ 1/N := by
  dsimp only
  rw [sourceMatrixBottom_eq_mediator n r,qmaForksGraph_matrix left right hneq weight constant _ site hsite,
    qmaPhysicalParallel_bottom]
  have hC : (qmaExchangeMatrix left right weight constant).conjTranspose =
      qmaExchangeMatrix left right weight constant := by
    simp only [qmaExchangeMatrix,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,
      Matrix.conjTranspose_smul,sourceHeisenbergMatrix_star n _ _ (hneq _),
      Complex.star_def,Complex.conj_ofReal,Matrix.conjTranspose_one]
  exact qmaForks_accuracy site hsite J K (by positivity) hN _ hC
    (qmaExchangeMatrix_lift_norm left right hneq weight constant)

end ContinuumCoulomb

end

end OAI
