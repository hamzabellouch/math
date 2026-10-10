import OAI.NumberTheory.DirichletL.Reflection.MarkedSource

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein CompletedGauss CubicJacobiGlobal FiniteGaussPhase ShortDraftCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma cofactor_reindex (p : ι→Eis) (e : κ≃ι) (k : κ) :
    cofactor (fun k => p (e k)) k=cofactor p (e k) := by
  unfold cofactor
  apply Finset.prod_equiv e
  · intro i
    simp only [Finset.mem_erase,Finset.mem_univ,and_true,ne_eq,EmbeddingLike.apply_eq_iff_eq]
  · intro i hi
    rfl

lemma finiteCrossNumerator_reindex (a c l : Eis) (p : ι→Eis) (e : κ≃ι) (h : ι→Eis) :
    finiteCrossNumerator a c l (fun k => p (e k)) (fun k => h (e k))=
      finiteCrossNumerator a c l p h := by
  unfold finiteCrossNumerator
  simp_rw [cofactor_reindex]
  rw [e.prod_comp,e.sum_comp (fun i => h i*cofactor p i)]

def unitFrequencyEquiv (p : ι→Eis) (e : κ≃ι) :
    (∀ k, (Eis⧸Ideal.span {p (e k)})ˣ)≃(∀ i, (Eis⧸Ideal.span {p i})ˣ) :=
  Equiv.piCongrLeft (fun i => (Eis⧸Ideal.span {p i})ˣ) e

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_apply (p : ι→Eis) (e : κ≃ι)
    (v : ∀ k, (Eis⧸Ideal.span {p (e k)})ˣ) (k : κ) :
    unitFrequencyEquiv p e v (e k)=v k := Equiv.piCongrLeft_apply_apply _ _ _ _

omit [Fintype ι] [Fintype κ] in
lemma unitFrequencyEquiv_one (p : ι→Eis) (e : κ≃ι) :
    unitFrequencyEquiv p e (fun _ => 1)=(fun _ => 1) := by
  funext i
  obtain ⟨k,rfl⟩ := e.surjective i
  exact unitFrequencyEquiv_apply p e _ k

def reindexControlled {p : ι→Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    ControlledStratumArithmetic (fun k => p (e k)) N a c mode where
  lift v k := D.lift (unitFrequencyEquiv p e v) (e k)
  lift_period v k := D.lift_period _ _
  lift_residue v k := (D.lift_residue _ _).trans (congrArg Units.val (unitFrequencyEquiv_apply p e v k))
  U := D.U
  w := D.w
  bezout := by simpa only [e.prod_comp] using D.bezout
  sigma k := D.sigma (e k)
  epsilon k := D.epsilon (e k)
  sigma_value k := by simpa only [cofactor_reindex] using D.sigma_value (e k)
  epsilon_value k := by simpa only [cofactor_reindex] using D.epsilon_value (e k)
  matrix v := D.matrix (unitFrequencyEquiv p e v)
  numerator v := by
    rw [D.numerator,finiteCrossNumerator_reindex]
  denominator v := by simpa only [e.prod_comp] using D.denominator (unitFrequencyEquiv p e v)
  matrix_fixed v i j := by
    simpa only [unitFrequencyEquiv_one] using D.matrix_fixed (unitFrequencyEquiv p e v) i j
  conditions v := D.conditions (unitFrequencyEquiv p e v)
end
end SevenEighths.InverseReflectedPhase

end OAI
