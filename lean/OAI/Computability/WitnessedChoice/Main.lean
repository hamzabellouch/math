import OAI.Computability.WitnessedChoice.ChoiceSeparation

namespace OAI


namespace WitnessedChoice

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Grid BGS

theorem main : BGS.MainStatement := by
  let φ := SourceProgram.program.sentence SourceProgram.polynomial
  refine ⟨φ,SourceProgram.one_occurrence,
    SourceProgram.boolean_all SourceProgram.polynomial SourceProgram.resource_basic,?_⟩
  intro ψ hψ heq
  obtain ⟨n,hn,hh⟩ := ψ.agrees_on_some_grid_pair hψ
  let vstar : Vertex n := (0,0,0)
  have hzero : φ.eval (gridInput (0 : Vertex n → WitnessedSeparation.Scalar)) = some true := by
    change SourceProgram.program.formula.eval (atomInput (0 : Vertex n → WitnessedSeparation.Scalar))
      SourceProgram.polynomial Fin.elim0 = _
    rw [QuotedGrid.formula_value _ (gridResources hn) hn]
    simp
  have hone : φ.eval (gridInput (Pi.single vstar 1)) = some false := by
    change SourceProgram.program.formula.eval (atomInput (Pi.single vstar 1))
      SourceProgram.polynomial Fin.elim0 = _
    rw [QuotedGrid.formula_value _ (gridResources hn) hn]
    simp
  have hmem : gridInput (0 : Vertex n → WitnessedSeparation.Scalar) ∈ ψ.TrueModels := by
    rw [←heq]
    exact hzero
  have hmem' : gridInput (Pi.single vstar 1) ∈ φ.TrueModels := by
    rw [heq]
    exact (hh vstar).symm.trans hmem
  change φ.eval (gridInput (Pi.single vstar 1)) = some true at hmem'
  rw [hone] at hmem'
  contradiction

end

end WitnessedChoice

end OAI
