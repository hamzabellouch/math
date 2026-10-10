import Mathlib
import OAI.Computability.QuantumFactoring.CircuitSemantics
import OAI.Computability.QuantumFactoring.GateSemantics

namespace OAI

section


namespace ExactQuantumFactoring
open scoped BigOperators Kronecker

noncomputable def basisVector {ι : Type*} [DecidableEq ι] (x : ι) : ι → ℂ :=
  fun y => if y = x then 1 else 0

lemma matrix_basisVector {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix κ ι ℂ) (x : ι) : A.mulVec (basisVector x) = fun y => A y x := by
  funext y
  simp [Matrix.mulVec, dotProduct, basisVector]

lemma permutationMatrix_basisVector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Equiv.Perm ι) (x : ι) :
    (permutationMatrix e).mulVec (basisVector x) = basisVector (e x) := by
  rw [matrix_basisVector]
  rfl

/-- Lift a local classical reversible gate to the actual wires; this is not an
additional circuit instruction, just its classical semantics. -/
noncomputable def Instruction.liftPerm {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) : Equiv.Perm (Basis q) :=
  (o.splitBasis.trans (Equiv.prodCongr e (Equiv.refl _))).trans o.splitBasis.symm

lemma Instruction.liftPerm_matrix {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity))
    (he : o.gate.localMatrix = permutationMatrix e) :
    o.matrix = permutationMatrix (o.liftPerm e) := by
  classical
  rw [o.matrix_eq_reindex, he]
  ext x y
  change ((if (o.splitBasis x).1 = e (o.splitBasis y).1 then (1:ℂ) else 0) *
      if (o.splitBasis x).2 = (o.splitBasis y).2 then 1 else 0) =
    if x = o.liftPerm e y then 1 else 0
  have hh : x = o.liftPerm e y ↔
      (o.splitBasis x).1 = e (o.splitBasis y).1 ∧
      (o.splitBasis x).2 = (o.splitBasis y).2 := by
    rw [← o.splitBasis.injective.eq_iff]
    simp [Instruction.liftPerm, Prod.ext_iff]
  simp only [hh]
  split_ifs <;> simp_all

lemma Instruction.liftPerm_wire {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) (x : Basis q) (i : Fin o.gate.arity) :
    o.liftPerm e x (o.wire i) = e (x ∘ o.wire) i := by
  have h := congrArg (fun z => z.1 i) (o.splitBasis.apply_symm_apply
    ((Equiv.prodCongr e (Equiv.refl (o.Unused → Bool))) (o.splitBasis x)))
  exact h

lemma Instruction.liftPerm_unused {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity)) (x : Basis q) (i : Fin q)
    (hi : ∀ j, o.wire j ≠ i) : o.liftPerm e x i = x i := by
  have h := congrArg (fun z => z.2 ⟨i,hi⟩) (o.splitBasis.apply_symm_apply
    ((Equiv.prodCongr e (Equiv.refl (o.Unused → Bool))) (o.splitBasis x)))
  exact h

lemma Instruction.liftPerm_basisVector {q : ℕ} (o : Instruction q)
    (e : Equiv.Perm (Basis o.gate.arity))
    (he : o.gate.localMatrix = permutationMatrix e) (x : Basis q) :
    o.matrix.mulVec (basisVector x) = basisVector (o.liftPerm e x) := by
  rw [o.liftPerm_matrix e he, permutationMatrix_basisVector]

/-- No inverse/control flag is used in these elementary fresh-bit operations. -/
abbrev plainGate (p : Primitive) : Gate := ⟨p,false,false⟩

lemma plainGate_arity (p : Primitive) : (plainGate p).arity = p.arity := by
  simp [Gate.arity]

lemma plainGate_localMatrix (p : Primitive) :
    (plainGate p).localMatrix = p.localMatrix := rfl

abbrev notAt {q : ℕ} (t : Fin q) : Instruction q :=
  ⟨plainGate .not, fun _ => t, by
    change Function.Injective (fun _ : Fin 1 => t)
    intro a b _
    exact Subsingleton.elim a b⟩

abbrev cnotAt {q : ℕ} (c t : Fin q) (hct : c ≠ t) : Instruction q :=
  ⟨plainGate .cnot, ![c,t], by
    change Function.Injective (![c,t] : Fin 2 → Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

abbrev toffoliAt {q : ℕ} (a b t : Fin q) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    Instruction q :=
  ⟨plainGate .toffoli, ![a,b,t], by
    change Function.Injective (![a,b,t] : Fin 3 → Fin q)
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

lemma notAt_lift {q : ℕ} (t : Fin q) (x : Basis q) :
    (notAt t).liftPerm notPerm x = Function.update x t (!x t) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (notAt t).liftPerm_wire notPerm x ⟨0,by change 0<1; decide⟩
  · rw [(notAt t).liftPerm_unused notPerm x i (by intro j; exact hi)]
    simp [Function.update, Ne.symm hi]

lemma cnotAt_lift {q : ℕ} (c t : Fin q) (hct : c ≠ t) (x : Basis q) :
    (cnotAt c t hct).liftPerm cnotPerm x =
      Function.update x t (Bool.xor (x c) (x t)) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (cnotAt c t hct).liftPerm_wire cnotPerm x ⟨1,by change 1<2; decide⟩
  · by_cases hc : c = i
    · subst i
      rw [Function.update_of_ne (Ne.symm hi)]
      exact (cnotAt c t hct).liftPerm_wire cnotPerm x ⟨0,by change 0<2; decide⟩
    · rw [(cnotAt c t hct).liftPerm_unused cnotPerm x i (by
        intro j; fin_cases j <;> simpa [cnotAt] using (by assumption : _))]
      simp [Function.update, Ne.symm hi]

lemma toffoliAt_lift {q : ℕ} (a b t : Fin q)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (x : Basis q) :
    (toffoliAt a b t hab hat hbt).liftPerm toffoliPerm x =
      Function.update x t (Bool.xor (x t) (x a && x b)) := by
  classical
  funext i
  by_cases hi : t = i
  · subst i
    rw [Function.update_self]
    exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨2,by change 2<3; decide⟩
  · by_cases ha : a = i
    · subst i
      rw [Function.update_of_ne (Ne.symm hi)]
      exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨0,by change 0<3; decide⟩
    · by_cases hb : b = i
      · subst i
        rw [Function.update_of_ne (Ne.symm hi)]
        exact (toffoliAt a b t hab hat hbt).liftPerm_wire toffoliPerm x ⟨1,by change 1<3; decide⟩
      · rw [(toffoliAt a b t hab hat hbt).liftPerm_unused toffoliPerm x i (by
          intro j; fin_cases j <;> simpa [toffoliAt] using (by assumption : _))]
        simp [Function.update, Ne.symm hi]

lemma notAt_basis {q : ℕ} (t : Fin q) (x : Basis q) :
    (notAt t).matrix.mulVec (basisVector x) = basisVector (Function.update x t (!x t)) := by
  rw [Instruction.liftPerm_basisVector (notAt t) notPerm (by exact not_localMatrix), notAt_lift]

lemma cnotAt_basis {q : ℕ} (c t : Fin q) (hct : c ≠ t) (x : Basis q) :
    (cnotAt c t hct).matrix.mulVec (basisVector x) =
      basisVector (Function.update x t (Bool.xor (x c) (x t))) := by
  rw [Instruction.liftPerm_basisVector (cnotAt c t hct) cnotPerm (by exact cnot_localMatrix), cnotAt_lift]

lemma toffoliAt_basis {q : ℕ} (a b t : Fin q) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t)
    (x : Basis q) :
    (toffoliAt a b t hab hat hbt).matrix.mulVec (basisVector x) =
      basisVector (Function.update x t (Bool.xor (x t) (x a && x b))) := by
  rw [Instruction.liftPerm_basisVector (toffoliAt a b t hab hat hbt) toffoliPerm (by exact toffoli_localMatrix), toffoliAt_lift]

end ExactQuantumFactoring


end

end OAI
