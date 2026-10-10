import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListMatrix

namespace OAI

/-! The finite bond packet emitted for parallel forks has the exact full-space
Hamiltonian used in the calibrated perturbation estimate. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

def packetBonds {n r : ℕ} (e : Fin r) (site : Fin 3 → Fin n) (J K R : ℚ) :
    List MediatorListProgram.Bond :=
  pairBonds n e.val R ((site 1 |>.val,J),(site 2 |>.val,K)) ++
    [((site 0).val,n+2*e.val,R)]

theorem packetBonds_matrix {n r : ℕ} (e : Fin r) (site : Fin 3 → Fin n) (J K R : ℚ) :
    ((packetBonds e site J K R).map (rawBondMatrix (n+r*2))).sum =
      ((2*J*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 1)) (old n r (site 2)) +
      (((R^2:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (fresh n r e 0) (fresh n r e 1) +
      (((2*R*J:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 1)) (fresh n r e 1) +
      ((2*R*K:ℚ):ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 2)) (fresh n r e 1))) +
      (R:ℂ) • sourceHeisenbergMatrix (n+r*2) (old n r (site 0)) (fresh n r e 0) := by
  have h : ((site 0).val,n+2*e.val,R) =
      erase (old n r (site 0),fresh n r e 0,R) := by
    simp [erase,MediatorIteration.old_val,MediatorIteration.fresh_val]
  simp only [packetBonds,List.map_append,List.sum_append,pairBonds_matrix,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,h,
    rawBondMatrix_erase,typedBondMatrix]

def graphBonds {n r m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℚ) (R : ℚ) :
    List MediatorListProgram.Bond :=
  List.ofFn (fun a => erase (old n r (left a),old n r (right a),w a)) ++
    (List.ofFn (fun e => packetBonds e (site e) (J e) (K e) R)).flatten

def graphConstant {r : ℕ} (c R : ℚ) (J K : Fin r → ℚ) : ℚ :=
  (c+∑ e, (3/4+3*(J e)^2+3*(K e)^2))+3*r*R^2

theorem graph_matrix {n r m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 3 → Fin n) (J K : Fin r → ℚ) (c R : ℚ) :
    rawMatrix (n+r*2) (graphBonds left right w site J K R,graphConstant c R J K) =
      qmaForksGraph left right (fun a => (w a:ℝ)) (c:ℝ) (R:ℝ) site
        (fun e => (J e:ℝ)) (fun e => (K e:ℝ)) := by
  simp only [rawMatrix,← Rat.cast_smul_eq_qsmul ℂ,graphBonds,List.map_append,List.sum_append,List.map_ofFn,
    List.sum_ofFn,List.map_flatten,List.sum_flatten,Function.comp_def,
    rawBondMatrix_erase,typedBondMatrix,packetBonds_matrix]
  simp only [qmaForksGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Fin.sum_univ_three,qmaParallelGraphLeft,qmaParallelGraphRight,
    qmaParallelGraphWeight,qmaForksBaseLeft,qmaForksBaseRight,qmaForksBaseWeight,
    Sum.elim_inl,Sum.elim_inr,qmaForkAmplitude,qmaForkMember,qmaForkOffset,
    graphConstant]
  push_cast
  simp only [Finset.sum_add_distrib]
  abel

def graphScale {r m : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ) (c N : ℚ) : ℚ :=
  let B := 3*(∑ a, |w a|)+|c|
  let A := 3*∑ e, (1+2*|J e|+2*|K e|)
  let D := B+12*∑ e, (1+|J e|+|K e|)^2
  16*(A+D+1)^3*N+4*(A+D+1)+1

theorem graphScale_cast {r m : ℕ} (w : Fin m → ℚ) (J K : Fin r → ℚ) (c N : ℚ) :
    (graphScale w J K c N : ℝ) =
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|+2*|(K e:ℝ)|))
        (3*(∑ a, |(w a:ℝ)|)+|(c:ℝ)|+
          12*∑ e, (1+|(J e:ℝ)|+|(K e:ℝ)|)^2) (N:ℝ) := by
  unfold graphScale qmaRoutingScale
  push_cast
  rfl

theorem graph_accuracy {n r m : ℕ} (left right : Fin m → Fin n)
    (hneq : ∀ a, left a ≠ right a) (w : Fin m → ℚ)
    (site : Fin r → Fin 3 → Fin n) (hsite : ∀ e, Function.Injective (site e))
    (J K : Fin r → ℚ) (c N : ℚ) (hN : 0 < N) :
    let R := graphScale w J K c N
    |sourceMatrixBottom (n+r*2)
        (rawMatrix (n+r*2) (graphBonds left right w site J K R,graphConstant c R J K)) -
      sourceMatrixBottom n (qmaExchangeMatrix left right (fun a => (w a:ℝ)) (c:ℝ) +
        ∑ e, ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤ 1/(N:ℝ) := by
  dsimp only
  rw [graph_matrix,graphScale_cast]
  have hJ : ∀ e, ((J e:ℝ):ℂ)=(J e:ℂ) := by intro e; norm_cast
  have hK : ∀ e, ((K e:ℝ):ℂ)=(K e:ℂ) := by intro e; norm_cast
  have h := qmaForksGraph_accuracy left right hneq (fun a => (w a:ℝ)) (c:ℝ)
    site hsite (fun e => (J e:ℝ)) (fun e => (K e:ℝ)) (show (0:ℝ) < N by exact_mod_cast hN)
  dsimp only at h
  simpa only [hJ,hK] using h

end ContinuumCoulomb.QuantumForkList

end

end OAI
