import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathStep

namespace OAI

/-! The literal bond-list subdivision has the same full-space ground-energy
estimate as the calibrated singlet construction. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathStep
open Matrix
open scoped BigOperators

def encodedInput {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (even : Bool) (N c : ℚ) : Input :=
  ((n,even,N,c),(List.ofFn fun i => ((left i).val,(right i).val,w i),
    List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)))

theorem scale_cast {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (even : Bool) (N c : ℚ) :
    ((parameters (encodedInput left right w site J even N c)).2.2:ℝ) =
      qmaRoutingScale (3*∑ i, (1+2*|(J i:ℝ)|))
        ((3*(∑ i, |(w i:ℝ)|)+|(c:ℝ)|)+4*∑ i, (1+|(J i:ℝ)|)^2) N := by
  simp only [parameters,scaleInput,encodedInput,QuantumPathScaleProgram.value,
    QuantumPathScaleProgram.active,QuantumPathScaleProgram.correction,QuantumPathScaleProgram.base,
    List.map_ofFn,List.sum_ofFn,Function.comp_apply,QuantumPathScaleProgram.linearCost,
    QuantumPathScaleProgram.squareCost,qmaRoutingScale]
  push_cast
  rfl

theorem encoded_matrix {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (even : Bool) (N c : ℚ) :
    let x := encodedInput left right w site J even N c
    SourceBondLists.matrix (n+r*2) (bonds x)+(constant x:ℂ) • 1 =
      qmaPathsGraph left right (fun i => (w i:ℝ)) c (parameters x).2.2 site
        (fun _ => even) (fun i => (J i:ℝ)) := by
  simpa only [encodedInput,count,bonds,constant,parameters,List.length_ofFn] using
    QuantumListPathProgram.fixed_step_matrix left right w site even
      (parameters (encodedInput left right w site J even N c)).2.2 c J

theorem source_matrix {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (J : Fin r → ℚ) (c : ℚ) :
    SourceBondLists.matrix n ((List.ofFn fun i => ((left i).val,(right i).val,w i))++
      List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))+(c:ℂ) • 1 =
      qmaExchangeMatrix left right (fun i => (w i:ℝ)) c+
        ∑ i, (J i:ℂ) • sourceHeisenbergMatrix n (site i 0) (site i 1) := by
  simp only [SourceBondLists.matrix,List.map_append,List.sum_append]
  change SourceBondLists.matrix n (List.ofFn fun i => ((left i).val,(right i).val,w i))+
    SourceBondLists.matrix n (List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))+
      (c:ℂ) • 1 = _
  rw [QuantumListPathProgram.matrix_ofFn,QuantumListPathProgram.matrix_ofFn]
  simp only [qmaExchangeMatrix,Complex.ofReal_ratCast]
  abel

theorem energy_error {n m r : ℕ} (left right : Fin m → Fin n)
    (hne : ∀ i, left i ≠ right i) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (hsite : ∀ i, Function.Injective (site i))
    (J : Fin r → ℚ) (even : Bool) {N : ℚ} (hN : 0 < N) (c : ℚ) :
    let x := encodedInput left right w site J even N c
    |sourceMatrixBottom (count x) (SourceBondLists.matrix (count x) (bonds x)+(constant x:ℂ) • 1)-
      sourceMatrixBottom n (SourceBondLists.matrix n (x.2.1++x.2.2)+(c:ℂ) • 1)| ≤ 1/(N:ℝ) := by
  dsimp only
  have hc : count (encodedInput left right w site J even N c) = n+r*2 := by
    simp only [count,encodedInput,List.length_ofFn]
  have hs : SourceBondLists.matrix n
      ((encodedInput left right w site J even N c).2.1++
        (encodedInput left right w site J even N c).2.2)+(c:ℂ) • 1 =
      qmaExchangeMatrix left right (fun i => (w i:ℝ)) c+
        ∑ i, (J i:ℂ) • sourceHeisenbergMatrix n (site i 0) (site i 1) :=
    source_matrix left right w site J c
  rw [hc,encoded_matrix,hs,scale_cast]
  exact qmaPathsGraph_accuracy left right hne (fun i => (w i:ℝ)) c site hsite
    (fun _ => even) (fun i => (J i:ℝ)) (by exact_mod_cast hN)

end ContinuumCoulomb.QuantumListPathStep

end

end OAI
