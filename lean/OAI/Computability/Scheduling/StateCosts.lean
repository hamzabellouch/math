import OAI.Computability.Scheduling.PolynomialTactic

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_setFilter {γ : ℕ → Type u4} [∀ n, Coding (γ n)]
    {p : ∀ n, Fin n × γ n → Bool} (P : Uniform p) (n : ℕ) (x : Finset (Fin n) × γ n) :
    P.setFilter.time n x = (setList.onFst.comp P.filter).time n x := rfl

theorem time_setEmpty (n : ℕ) (x : Universe n) : setEmpty.time n x = 2 := rfl

theorem time_vectorMap {α : ℕ → Type u5} {β : ℕ → Type u6} [∀ n, Coding (α n)] [∀ n, Coding (β n)]
    {f : ∀ n, Fin n × α n → β n} (R : Uniform f) (n : ℕ) (x : Universe n × α n) :
    R.vectorMap.time n x = (universeList.onFst.comp R.map).time n x := rfl

theorem time_vectorMapAny (d : I → ℕ) {f : ∀ i, Fin (d i) × α i → β i}
    (R : Uniform f) (i : I) (x : Universe (d i) × α i) :
    (R.vectorMapAny d).time i x = ((universeListAny d).onFst.comp R.map).time i x := rfl
end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u7} {α : I → Type u8} [∀ i, Coding (α i)]
theorem time_andD_le {p q : ∀ i, α i → Prop}
    [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x)))
    (i : I) (x : α i) : (P.andD Q).time i x ≤ P.time i x+Q.time i x+20*volume x+11000 := by
  rw [andD,time_congr,time_comp,time_pair,time_uniform]
  have h := Realizer.time_and_le (decide (p i x),decide (q i x))
  have hp := volume_bool (decide (p i x))
  have hq := volume_bool (decide (q i x))
  simp only [volume_pair] at *
  omega
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
namespace Costs
theorem matrixGet : Poly (fun x : Σ n, Matrix n × (Fin n × Fin n) => x.1)
    (fun x => Uniform.matrixGet.time x.1 x.2) 3 := by poly_auto
theorem finEq : Poly (fun x : Σ n, Fin n × Fin n => x.1)
    (fun x => Uniform.finEq.time x.1 x.2) 2 := by
  apply Poly.of_le (g := fun x : Σ n, Fin n × Fin n => 1000000000000*(x.1+2)^2)
  · rintro ⟨n,a,b⟩
    have hf (n : ℕ) (v : Fin n) : Uniform.finVal.time n v = volume v+2 := rfl
    have h := Realizer.time_eqNat_le a.val b.val
    have hsq := Nat.pow_le_pow_left (show a.val+b.val+1 ≤ 2*n+1 by omega) 2
    simp only [Uniform.finEq,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,
      Uniform.time_fst,Uniform.time_snd,hf,
      Uniform.time_uniform,volume_pair,volume_fin,volume_nat,Function.comp_apply]
    nlinarith [a.isLt,b.isLt]
  · poly_auto
theorem setMem : Poly (fun x : Σ n, Fin n × Finset (Fin n) => x.1)
    (fun x => Uniform.setMem.time x.1 x.2) 3 := by poly_auto
theorem setSubset : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setSubset.time x.1 x.2) 4 := by poly_auto
theorem setEq : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setEq.time x.1 x.2) 4 := by poly_auto
theorem setInter : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setInter.time x.1 x.2) 4 := by poly_auto
theorem setDiff : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setDiff.time x.1 x.2) 4 := by poly_auto
theorem setDisjoint : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setDisjoint.time x.1 x.2) 4 := by poly_auto
end Costs
namespace Uniform

def noEdgeTest : Uniform (fun n (x : Fin n × (Matrix n × Fin n)) => !x.2.1 x.2.2 x.1) :=
  (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp matrixGet).comp (Realizer.not.uniform ℕ)

def noEdgeRow : Uniform (fun n (x : Fin n × (Matrix n × Finset (Fin n))) =>
    decide (∀ b ∈ x.2.2, ¬matrixRel x.2.1 x.1 b)) :=
  (((snd.comp snd).pair ((snd.comp fst).pair fst)).comp noEdgeTest.setAll).congr (fun _ _ => by
    simp only [Function.comp_apply,Bool.not_eq_true,matrixRel,Bool.not_eq_true'])

theorem time_noEdges (n : ℕ) (x : Matrix n × (Finset (Fin n) × Finset (Fin n))) :
    noEdges.time n x =
      (((snd.comp fst).pair (fst.pair (snd.comp snd))).comp noEdgeRow.setAll).time n x := rfl

end Uniform
namespace Costs
theorem noEdgeTest : Poly (fun x : Σ n, Fin n × (Matrix n × Fin n) => x.1)
    (fun x => Uniform.noEdgeTest.time x.1 x.2) 3 := by poly_auto
theorem noEdgeRow : Poly (fun x : Σ n, Fin n × (Matrix n × Finset (Fin n)) => x.1)
    (fun x => Uniform.noEdgeRow.time x.1 x.2) 4 := by poly_auto
theorem noEdges : Poly (fun x : Σ n, Matrix n × (Finset (Fin n) × Finset (Fin n)) => x.1)
    (fun x => Uniform.noEdges.time x.1 x.2) 5 := by poly_auto
end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev StateEqInput (n : ℕ) := Algorithm.State (Fin n) × Algorithm.State (Fin n)
def stateEqL : Uniform (fun n (x : StateEqInput n) => decide (x.1.left = x.2.left)) :=
  ((fst.comp stateLeft).pair (snd.comp stateLeft)).comp setEq
def stateEqM : Uniform (fun n (x : StateEqInput n) => decide (x.1.middle = x.2.middle)) :=
  ((fst.comp stateMiddle).pair (snd.comp stateMiddle)).comp setEq
def stateEqR : Uniform (fun n (x : StateEqInput n) => decide (x.1.right = x.2.right)) :=
  ((fst.comp stateRight).pair (snd.comp stateRight)).comp setEq
def stateEqMR := (stateEqM.pair stateEqR).comp (Realizer.and.uniform ℕ)
def stateEqLMR := (stateEqL.pair stateEqMR).comp (Realizer.and.uniform ℕ)
theorem time_stateEq (n : ℕ) (x : StateEqInput n) : stateEq.time n x = stateEqLMR.time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem stateEqL : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqL.time x.1 x.2) 4 := by poly_auto
theorem stateEqM : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqM.time x.1 x.2) 4 := by poly_auto
theorem stateEqR : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqR.time x.1 x.2) 4 := by poly_auto
theorem stateEqMR : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqMR.time x.1 x.2) 4 := by poly_auto
theorem stateEqLMR : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqLMR.time x.1 x.2) 4 := by poly_auto
theorem stateEq : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEq.time x.1 x.2) 4 := by poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
theorem setCard : Poly (fun x : Σ n, Finset (Fin n) => x.1)
    (fun x => Uniform.setCard.time x.1 x.2) 3 := by poly_auto
theorem setUnion : Poly (fun x : Σ n, Universe n × (Finset (Fin n) × Finset (Fin n)) => x.1)
    (fun x => Uniform.setUnion.time x.1 x.2) 4 := by poly_auto
theorem stateCandidate : Poly (fun x : Σ n, Universe n ×
    (Finset (Fin n) × (Finset (Fin n) × Finset (Fin n))) => x.1)
    (fun x => Uniform.stateCandidate.time x.1 x.2) 4 := by poly_auto
theorem stateUpto : Poly (fun x : Σ n, Universe n × Algorithm.State (Fin n) => x.1)
    (fun x => Uniform.stateUpto.time x.1 x.2) 4 := by poly_auto
end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
theorem time_stateCompatible (n : ℕ) (x : CompatInput n) :
    stateCompatible.time n x = scAll.time n x := by
  simp only [stateCompatible,time_congr]
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem scLZ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scLZ.time x.1 x.2) 4 := by poly_auto
theorem scLZR : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scLZR.time x.1 x.2) 4 := by poly_auto
theorem scA : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scA.time x.1 x.2) 4 := by poly_auto
theorem scB : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scB.time x.1 x.2) 4 := by poly_auto
theorem scC : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scC.time x.1 x.2) 4 := by poly_auto
theorem scD : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scD.time x.1 x.2) 4 := by poly_auto
theorem scE : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scE.time x.1 x.2) 3 := by poly_auto
theorem scF : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scF.time x.1 x.2) 5 := by poly_auto
theorem scH : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scH.time x.1 x.2) 5 := by poly_auto
theorem scI : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scI.time x.1 x.2) 5 := by poly_auto
theorem scJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scJ.time x.1 x.2) 5 := by poly_auto
theorem scIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scIJ.time x.1 x.2) 5 := by poly_auto
theorem scHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scHIJ.time x.1 x.2) 5 := by poly_auto
theorem scFHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scFHIJ.time x.1 x.2) 5 := by poly_auto
theorem scEFHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scEFHIJ.time x.1 x.2) 5 := by poly_auto
theorem scDEFHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scDEFHIJ.time x.1 x.2) 5 := by poly_auto
theorem scCDEFHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scCDEFHIJ.time x.1 x.2) 5 := by poly_auto
theorem scBCDEFHIJ : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scBCDEFHIJ.time x.1 x.2) 5 := by poly_auto
theorem scAll : Poly (fun x : Σ n, Uniform.CompatInput n => x.1)
    (fun x => Uniform.scAll.time x.1 x.2) 5 := by poly_auto
theorem stateCompatible : Poly (fun x : Σ n, Universe n ×
    (Matrix n × (Finset (Fin n) × Algorithm.State (Fin n))) => x.1)
    (fun x => Uniform.stateCompatible.time x.1 x.2) 5 := by poly_auto
theorem blockEmpty : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.blockEmpty.time x.1 x.2) 3 := by poly_auto
theorem blockTriple : Poly (fun x : Σ n, Universe n => x.1)
    (fun x => Uniform.blockTriple.time x.1 x.2) 3 := by poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
