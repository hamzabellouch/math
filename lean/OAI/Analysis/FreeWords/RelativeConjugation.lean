import Mathlib
import OAI.Analysis.FreeWords.RelativeConjugationDefinitions
import OAI.Analysis.FreeWords.RelativeMatrix

namespace OAI

noncomputable section

namespace KKRelativeMatrix

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def conjugationWord {M : VonNeumannAlgebra H} {n : ℕ}
    (w : List (Matrix (Fin n) (Fin n) (ConcreteAlgebra M) × Matrix (Fin n) (Fin n) (ConcreteAlgebra M))) : List (ℤ × Matrix (Fin n) (Fin n) (ConcreteAlgebra M)) :=
  w.flatMap (fun z => [(1,z.1),(-1,z.2)])

theorem conjugationWord_ne_nil {M : VonNeumannAlgebra H} {n : ℕ}
    {w : List (Matrix (Fin n) (Fin n) (ConcreteAlgebra M) × Matrix (Fin n) (Fin n) (ConcreteAlgebra M))} (h : w≠[]) :
    conjugationWord w≠[] := by
  cases w with
  | nil => exact (h rfl).elim
  | cons z w => simp [conjugationWord]

theorem conjugationWord_value {M : VonNeumannAlgebra H} {n : ℕ}
    (u : unitary (ConcreteAlgebra M))
    (w : List (Matrix (Fin n) (Fin n) (ConcreteAlgebra M) × Matrix (Fin n) (Fin n) (ConcreteAlgebra M))) :
    ((conjugationWord w).map (fun z =>
      Matrix.diagonal (fun _ : Fin n => (u^z.1).val)*z.2)).prod=
    (w.map (fun z => scalarConjugate u z.1*z.2)).prod := by
  induction w with
  | nil => simp [conjugationWord]
  | cons z w ih =>
    simp only [conjugationWord,List.flatMap_cons,List.map_append,List.prod_append,
      List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,zpow_one,zpow_neg_one]
    change _ * ((conjugationWord w).map _).prod=_
    rw [ih]
    simp only [scalarConjugate,mul_assoc]

theorem finite_relative_conjugation : FiniteRelativeConjugation (H := H) := by
  classical
  intro M τ hF hD n K F hne hc ε hε
  have hn' : ∀w∈F.image conjugationWord, w≠[] := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    exact conjugationWord_ne_nil (hne v hv)
  have hc' : ∀w∈F.image conjugationWord, ∀z∈w,
      z.1≠0 ∧ ∀i j,τ.map (z.2 i j)=0 := by
    intro w hw z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,ha,hza⟩ := List.mem_flatMap.mp hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hza
    rcases hza with rfl | rfl
    · exact ⟨by norm_num,fun i j => (hc v hv a ha i j).1⟩
    · exact ⟨by norm_num,fun i j => (hc v hv a ha i j).2⟩
  obtain ⟨u,hK,hW⟩ := finite_relative_matrix_independence M τ hF hD n K
    (F.image conjugationWord) hn' hc' ε hε
  refine ⟨u,hK,?_⟩
  intro w hw i j
  have hh := hW (conjugationWord w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩) i j
  rwa [conjugationWord_value] at hh

end

end KKRelativeMatrix
end

end OAI
