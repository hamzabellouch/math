import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSampleAssembly
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawTermProgram

namespace OAI

/-! The literal raw edge instructions encode the proved physical matrix. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram
open scoped BigOperators Classical

def erase {m : ℕ} (b : TypedBond m) : Bond := (b.1.val,b.2.1.val,b.2.2)

theorem field_erase {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ) :
    (fieldBonds k i a J).map erase = field k i.val a J := by
  simp [fieldBonds,field,erase,finProdFinEquiv,Nat.add_comm]

theorem cross_erase {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (a b : Fin 2) (J : ℚ) :
    (crossBonds k r i j a b J).map erase = cross k r i.val j.val a b J := by
  simp only [crossBonds,cross,List.map_ofFn]
  apply congrArg List.ofFn
  funext e
  dsimp only [Function.comp_apply]
  generalize (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e = pq
  change (pq.1.val+4*i.val,pq.2.val+4*j.val,crossValue k r a b J pq.1 pq.2) = _
  simp only [Nat.add_comm]

theorem bonds_pack {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) :
    bonds ((k,r),pack t J) = (termBonds k r t J).map erase := by
  cases t <;> simp [bonds,pack,axis_pack,termBonds,List.map_append,field_erase,cross_erase]

theorem scalar_pack {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) :
    scalar ((k,r),pack t J) = termScalar k t J := by
  cases t <;> simp [scalar,pack,axis_pack,termScalar]

theorem fieldBonds_distinct {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ)
    (b : TypedBond (n*4)) (hb : b ∈ fieldBonds k i a J) : b.1 ≠ b.2.1 := by
  obtain ⟨e,he⟩ := List.mem_ofFn.mp hb
  subst b
  intro h
  exact qmaFieldEdgeRight_ne e (congrArg Prod.snd (finProdFinEquiv.injective h))

theorem crossBonds_distinct {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (hij : i ≠ j)
    (a b : Fin 2) (J : ℚ) (e : TypedBond (n*4))
    (he : e ∈ crossBonds k r i j a b J) : e.1 ≠ e.2.1 := by
  obtain ⟨p,hp⟩ := List.mem_ofFn.mp he
  subst e
  intro h
  exact hij (congrArg Prod.fst (finProdFinEquiv.injective h))

theorem termBonds_distinct {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ)
    (b : TypedBond (n*4)) (hb : b ∈ termBonds k r t J) : b.1 ≠ b.2.1 := by
  cases t with
  | scalar => simp [termBonds] at hb
  | field i a => exact fieldBonds_distinct k i a J b hb
  | pair i j hij a c =>
    simp only [termBonds,List.mem_append] at hb
    rcases hb with (hb|hb)|hb
    · exact crossBonds_distinct k r i j hij a c J b hb
    · exact fieldBonds_distinct _ _ _ _ b hb
    · exact fieldBonds_distinct _ _ _ _ b hb

theorem penaltyBonds_distinct (n : ℕ) (r : ℚ) (b : TypedBond (n*4))
    (hb : b ∈ penaltyBonds n r) : b.1 ≠ b.2.1 := by
  obtain ⟨e,he⟩ := List.mem_ofFn.mp hb
  subst b
  intro h
  exact qmaFourEdge_distinct _ (congrArg Prod.snd (finProdFinEquiv.injective h))

def family {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    List (TypedBond (n*4)) :=
  penaltyBonds n r ++ (List.ofFn (fun e => termBonds k r (t e) (J e))).flatten

theorem family_matrix {n m : ℕ} (k : ℕ) (r : ℚ) (t : Fin m → QMAXZTerm n) (J : Fin m → ℚ) :
    ((family k r t J).map typedBondMatrix).sum+
      (r^2*(n*6)+∑ e, termScalar k (t e) (J e):ℚ) •
        (1 : Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ) = matrixValue k r t J := by
  rw [termScalar_sum]
  rw [matrixValue_assembly]
  simp only [family,List.map_append,List.sum_append,List.map_flatten,List.map_ofFn,
    List.sum_flatten,List.sum_ofFn,Function.comp_apply]
  rfl

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
