import OAI.NumberTheory.DirichletL.Reflection.Reindex
import OAI.NumberTheory.DirichletL.Descent.ReflectedDual

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}

lemma reindexControlled_matrix_one (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).matrix (fun _ => 1)=D.matrix (fun _ => 1) := by
  change D.matrix (unitFrequencyEquiv p e (fun _ => 1))=_
  rw [unitFrequencyEquiv_one]

lemma reindexControlled_fixedFactor (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).fixedFactor=D.fixedFactor := by
  unfold ControlledStratumArithmetic.fixedFactor
  rw [reindexControlled_matrix_one]

lemma reindexControlled_U (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).U=D.U := rfl

def reindexMarks (e : κ≃ι) (S : Finset ι) : Finset κ := Finset.univ.filter (fun k => e k∈S)

omit [Fintype ι] in
lemma mem_reindexMarks (e : κ≃ι) (S : Finset ι) (k : κ) : k∈reindexMarks e S ↔ e k∈S := by
  simp [reindexMarks]

lemma mixedActiveBracket_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (hp : ∀ i, p i≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (k : κ) (x : Eis) :
    mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
      (reindexMarks e S) (reindexControlled D e) k x =mixedActiveBracket hp hg j S D (e k) x := by
  simp only [mixedActiveBracket,mem_reindexMarks]
  rfl

theorem mixedReflectedValue_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =mixedReflectedValue D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [mixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]
end
end SevenEighths.InverseReflectedPhase

end OAI
