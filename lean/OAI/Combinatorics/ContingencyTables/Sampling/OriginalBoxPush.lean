import OAI.Combinatorics.ContingencyTables.Sampling.OriginalResidualVector

namespace OAI

/-! # Transporting weighted sums through the original-table enumeration -/

namespace ContingencyTables.OriginalBoxLaw
open OriginalTableBox ProfilePrograms DensePrograms
open scoped BigOperators Classical
noncomputable section
variable {m n N Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma sum_tableAt (hN : (∑ i,r i)≤N) (w : Table r c → ℕ) :
    (∑ k : Index m n N,(tableAt r c k).elim 0 w)=∑ X,w X := by
  have he (k : Index m n N) : (tableAt r c k).elim 0 w=
      ∑ X : Table r c,if tableAt r c k=some X then w X else 0 := by
    cases tableAt r c k <;> simp
  simp_rw [he]
  rw [Finset.sum_comm]
  simp_rw [tableAt_eq_some r c hN]
  simp

lemma push_count (hN : (∑ i,r i)≤N) (p : IntegerLaw (Table r c) Q) (k : Index m n N) :
    (p.push (index r c hN)).count k=(tableAt r c k).elim 0 p.count := by
  change (∑ X,if index r c hN X=k then p.count X else 0)=_
  simp_rw [←tableAt_eq_some r c hN]
  cases tableAt r c k <;> simp

/-- The literal correction vector is the integer residual law embedded in
its enumerated box, so its total and zero weights are exact. -/
lemma residualVector_law (p : IntegerLaw (Table r c) Q) (fallback : Table r c)
    (T : ℕ) (hQ : 0<Q) (hT : 0<T)
    (hdom : let _ : Nonempty (Table r c) := ⟨fallback⟩
      ∀ X,(1-1/(T:ℚ))*(p.toRational hQ).mass X≤ResidualMixture.uniformMass (α := Table r c)) :
    let _ : Nonempty (Table r c) := ⟨fallback⟩
    residualVector ((originalCandidates (List.ofFn r,List.ofFn c),
        List.ofFn ((p.push (index r c le_rfl)).count)),
        ((Q,T),originalCardinality (List.ofFn r,List.ofFn c)))=
      List.ofFn ((IntegerResidualCorrection.law p T hQ hT hdom).push (index r c le_rfl)).count := by
  let : Nonempty (Table r c) := ⟨fallback⟩
  dsimp only at hdom ⊢
  rw [residualVector_actual r c p fallback T hT]
  apply congrArg List.ofFn
  funext k
  rw [push_count]
  rfl

end
end ContingencyTables.OriginalBoxLaw

end OAI
