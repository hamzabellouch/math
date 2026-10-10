import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixLimits
import OAI.Combinatorics.ContingencyTables.Sampling.ExactMatrixLookup
import OAI.Combinatorics.ContingencyTables.Transport.IntegerLawEmbedding
import OAI.Combinatorics.ContingencyTables.Machines.MatrixCodeEquality

namespace OAI

/-! # Exact weighted matrix selection realizes a table law -/

namespace ContingencyTables.ExactMatrixTrial
open MatchingFPRAS MatchingFPRAS.PhysicalStream DensePrograms ProfilePrograms OriginalTableBox
open ExactIntegerChoice ResidualMixture FirstSuccess
open scoped BigOperators Classical
noncomputable section
attribute [local irreducible] lookup originalCandidates

lemma normalized_counts {K Q : ℕ} (p : IntegerLaw (Fin K) Q)
    (hQ : 0<Q) (a : Fin K) : (p.count a:ℚ)/totalWeight p.count=(p.toRational hQ).mass a := by
  unfold totalWeight
  rw [p.total]
  rfl

lemma count_weight_pos {K Q : ℕ} (p : IntegerLaw (Fin K) Q)
    (hQ : 0<Q) : 0<totalWeight p.count := by
  unfold totalWeight
  rwa [p.total]

/-- An integer law's full original-box vector pushes back to precisely
that table law under the executed matrix lookup. -/
lemma table_normalized_event {m n Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : IntegerLaw (Table r c) Q) (hQ : 0<Q) (fallback X : Table r c) :
    (∑ i : Index m n (∑ j,r j),
      if lookup ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),i.val)=
          matrixCode X.val then normalized (p.push (index r c le_rfl)).count i else 0)=
      (p.toRational hQ).mass X := by
  let test : Index m n (∑ j,r j) → Bool := fun i => decide
    (lookup ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),i.val)=matrixCode X.val)
  have hn (i : Index m n (∑ j,r j)) :
      normalized (p.push (index r c le_rfl)).count i=
        ((p.push (index r c le_rfl)).toRational hQ).mass i :=
    normalized_counts _ hQ i
  simp_rw [hn]
  have hm : (mapLaw ((p.push (index r c le_rfl)).toRational hQ) test).mass true=
      (mapLaw (p.toRational hQ) (fun T => test (index r c le_rfl T))).mass true := by
    rw [IntegerLaw.toRational_push,mapLaw_comp]
  have he (T : Table r c) : test (index r c le_rfl T)=true ↔ T=X := by
    simp only [test,decide_eq_true_eq,lookup_index]
    exact ⟨fun h => Subtype.ext (matrixCode_injective h),fun h => by rw [h]⟩
  simp only [mapLaw] at hm
  simp only [test,decide_eq_true_eq] at hm
  rw [hm]
  have htest (T : Table r c) :
      (lookup ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),
        (index r c le_rfl T).val)=matrixCode X.val) ↔ T=X := by
        simpa only [test,decide_eq_true_eq] using he T
  simp only [htest,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- The finite prefixes of the actual exact matrix loop converge to the
input table law. -/
theorem table_prefix_limit {m n Q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : IntegerLaw (Table r c) Q) (hQ : 0<Q) (fallback X : Table r c) :
    Filter.Tendsto (fun N =>
      ((OnlineIntegerRetry.prefixExperiment (f := trial)
        ((originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val),
          List.ofFn (p.push (index r c le_rfl)).count) N).mean
        (fun o => if o=some (matrixCode X.val) then 1 else 0):ℝ))
      Filter.atTop (nhds ((p.toRational hQ).mass X:ℝ)) := by
  have h := prefix_limit (originalCandidates (List.ofFn r,List.ofFn c),matrixCode fallback.val)
    (p.push (index r c le_rfl)).count (count_weight_pos _ hQ) (matrixCode X.val)
  rw [table_normalized_event r c p hQ fallback X] at h
  exact h

end
end ContingencyTables.ExactMatrixTrial

end OAI
