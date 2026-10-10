import Mathlib
import OAI.Analysis.FreeWords.AmplifiedCyclicApprox
import OAI.Analysis.FreeWords.ControlledMatrixConjugation
import OAI.Analysis.FreeWords.HaarEndpoints

namespace OAI

noncomputable section

namespace KKFiniteTransport

noncomputable section

open KKTraceTransfer KKFreeLiftFrontier KKMatrixExpectation KKHaarEndpoints KKControlledConjugation

open scoped Matrix.Norms.Operator

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M:VonNeumannAlgebra H}

abbrev Block (τ:FaithfulNormalTrace M) (n:ℕ) :=
  {z:List (ℤ×MatrixAlgebra n M)×ℤ //
    CenteredPowerWord (matrixTraceMap τ.map n) (numericalHom n).range.toSubalgebra z.1 ∧ z.2≠0}

def blockValue {τ:FaithfulNormalTrace M} {n:ℕ} (U:unitary (MatrixAlgebra n M)) (b:Block τ n) :=
  powerWord U b.val.1*(U^b.val.2).val

def blockCenter (τ:FaithfulNormalTrace M) {n:ℕ} (U:unitary (MatrixAlgebra n M)) (b:Block τ n) :=
  blockValue U b-matrixExpectation τ.map n (blockValue U b)

def conjStarMonoid {n:ℕ} (u:unitary (ConcreteAlgebra M)) :
    MatrixAlgebra n M →⋆* MatrixAlgebra n M :=
  { (amplifyConj n u).toAlgHom.toMonoidHom with map_star' := map_star (amplifyConj n u) }

def conjUnitary {n:ℕ} (u:unitary (ConcreteAlgebra M)) (U:unitary (MatrixAlgebra n M)) :=
  Unitary.map (conjStarMonoid u) U

@[simp] theorem conjUnitary_val {n:ℕ} (u:unitary (ConcreteAlgebra M)) (U:unitary (MatrixAlgebra n M)) :
    (conjUnitary u U).val=amplifyConj n u U.val := rfl

theorem conjUnitary_zpow {n:ℕ} (u:unitary (ConcreteAlgebra M)) (U:unitary (MatrixAlgebra n M)) (k:ℤ) :
    (conjUnitary u U^k).val=amplifyConj n u (U^k).val := by
  change ((Unitary.map (conjStarMonoid u) U)^k).val=_
  rw [← map_zpow]
  rfl

theorem conjUnitary_good {n:ℕ} (u:unitary (ConcreteAlgebra M)) (U:unitary (MatrixAlgebra n M))
    (h:FullMatrixUnitary n U) : FullMatrixUnitary n (conjUnitary u U) := by
  obtain ⟨d,hd,ρ,hρ,hentry⟩ := h
  refine ⟨d,hd,(Unitary.conjStarAlgAut ℂ (ConcreteAlgebra M) u).toStarAlgHom.comp ρ,?_,?_⟩
  · exact (Unitary.conjStarAlgAut ℂ (ConcreteAlgebra M) u).injective.comp hρ
  · exact amplifyConj_entry_range u ρ U.val hentry

theorem powerWord_conj {τ:FaithfulNormalTrace M} {n:ℕ} (u:unitary (ConcreteAlgebra M))
    (U:unitary (MatrixAlgebra n M)) (w:List (ℤ×MatrixAlgebra n M))
    (h:CenteredPowerWord (matrixTraceMap τ.map n) (numericalHom n).range.toSubalgebra w) :
    powerWord (A := MatrixAlgebra n M) (conjUnitary (n := n) u U) w=
      amplifyConj n u (powerWord U w) := by
  induction w with
  | nil => simp [powerWord]
  | cons z w ih =>
    have hz := (h z List.mem_cons_self).2.1
    have ht := fun a ha => h a (List.mem_cons_of_mem _ ha)
    obtain ⟨b,hb⟩ := hz
    have hfix : amplifyConj n u z.2=z.2 := by
      rw [← hb]
      exact amplifyConj_numerical n u b
    simp only [powerWord_cons,conjUnitary_zpow,ih ht,map_mul,hfix]

theorem blockValue_conj {τ:FaithfulNormalTrace M} {n:ℕ} (u:unitary (ConcreteAlgebra M))
    (U:unitary (MatrixAlgebra n M)) (b:Block τ n) :
    blockValue (conjUnitary u U) b=amplifyConj n u (blockValue U b) := by
  rw [blockValue,powerWord_conj u U _ b.property.1,conjUnitary_zpow,← map_mul]
  rfl

theorem blockCenter_conj (τ:FaithfulNormalTrace M) {n:ℕ} (u:unitary (ConcreteAlgebra M))
    (U:unitary (MatrixAlgebra n M)) (b:Block τ n) :
    blockCenter τ (conjUnitary u U) b=amplifyConj n u (blockCenter τ U b) := by
  have hfix : amplifyConj n u (matrixExpectation τ.map n (blockValue U b))=
      matrixExpectation τ.map n (blockValue U b) := by
    exact amplifyConj_numerical n u _
  simp only [blockCenter,blockValue_conj,map_sub,
    amplifyConj_expectation τ.map τ.tracial,hfix]

end

end KKFiniteTransport
end

end OAI
