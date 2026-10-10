import OAI.Combinatorics.ContingencyTables.Counting.CountingPublicTerminalBounds
import OAI.Combinatorics.ContingencyTables.Counting.CountingControlBounds

namespace OAI

/-! # All dynamic scalar controls are polynomial in the public input -/

namespace ContingencyTables.CountingPublicControls
open CountingPublicInputBounds CountingPublicTerminalBounds CountingControlBounds
open CompanionFactorialApplication Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

def inputPolynomial : Polynomial ℕ := basicPolynomial+restartPolynomial+X
def observationPolynomial : Polynomial ℕ := CountingControlBounds.observationPolynomial.comp inputPolynomial
def returnPolynomial : Polynomial ℕ := CountingControlBounds.returnPolynomial.comp inputPolynomial
def precisionPolynomial : Polynomial ℕ := CountingControlBounds.precisionPolynomial.comp inputPolynomial

lemma scalar_bound (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let H := ComputedCountingParameters.phases r c b epsilon
    let L := ComputedCountingParameters.capacityBits r c b
    ∀ x∈[Fintype.card (Labels A),A.W,H,CompanionTargetMixing.restartTime A H L,L],
      x ≤ inputPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hs : ∀ x∈[Fintype.card (Labels A),A.W,H,0,0,0,L],
      x ≤ basicPolynomial.eval (size r c b epsilon delta) :=
    scalar_public hEK r c b hne epsilon delta he
  have ht := restart_public hEK r c b hne epsilon delta he
  have hp := hs (Fintype.card (Labels A)) (by simp only [List.mem_cons, eq_self, true_or])
  have hw := hs A.W (by simp only [List.mem_cons, eq_self, true_or, or_true])
  have hh := hs H (by simp only [List.mem_cons, eq_self, true_or, or_true])
  have hl := hs L (by simp only [List.mem_cons, eq_self, true_or, or_true])
  change ∀ x∈[Fintype.card (Labels A),A.W,H,CompanionTargetMixing.restartTime A H L,L],
    x ≤ inputPolynomial.eval (size r c b epsilon delta)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [inputPolynomial,Polynomial.eval_add,Polynomial.eval_X]
  change CompanionTargetMixing.restartTime A H L ≤ _ at ht
  omega

lemma settings_bounds (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    s.N ≤ observationPolynomial.eval (size r c b epsilon delta) ∧
    s.n ≤ returnPolynomial.eval (size r c b epsilon delta) ∧
    s.k ≤ precisionPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  let T := CompanionTargetMixing.restartTime A H L
  let M := inputPolynomial.eval (size r c b epsilon delta)
  have hs : ∀ x∈[Fintype.card (Labels A),A.W,H,T,L],x ≤ M :=
    scalar_bound hEK r c b hne epsilon delta he
  have hp : Fintype.card (Labels A) ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or])
  have hw : A.W ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])
  have hh : H ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])
  have ht : T ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])
  have hSM : size r c b epsilon delta ≤ M := by
    dsimp only [M]
    simp only [inputPolynomial,Polynomial.eval_add,Polynomial.eval_X]
    omega
  have hi : 1/epsilon ≤ (M:ℚ) := (inverse_le r c b epsilon delta).trans (by exact_mod_cast hSM)
  refine ⟨?_,?_,?_⟩
  · change CountingPhaseSchedule.observations (Fintype.card (Labels A)) A.W H
        (CountingPhaseSchedule.tolerance H (epsilon/2)) ≤ _
    simpa only [observationPolynomial,Polynomial.eval_comp,M] using
      observations_bound _ _ _ M epsilon he hp hw hh hi
  · change CountingPhaseSchedule.returnCap (Fintype.card (Labels A)) H T ≤ _
    simpa only [returnPolynomial,Polynomial.eval_comp,M] using return_bound _ _ _ M hp hh ht
  · change CountingPhaseSchedule.precision H T
        (CountingPhaseSchedule.observations (Fintype.card (Labels A)) A.W H
          (CountingPhaseSchedule.tolerance H (epsilon/2)))
        (CountingPhaseSchedule.returnCap (Fintype.card (Labels A)) H T)
        (CountingPhaseSchedule.tolerance H (epsilon/2)) ≤ _
    simpa only [precisionPolynomial,Polynomial.eval_comp,M] using
      precision_bound _ _ _ _ M epsilon he hp hw hh ht hi

end
end ContingencyTables.CountingPublicControls

end OAI
