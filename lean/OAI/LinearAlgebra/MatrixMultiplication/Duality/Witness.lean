import OAI.LinearAlgebra.MatrixMultiplication.Duality.CompletionLaws
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformInstances
import OAI.LinearAlgebra.MatrixMultiplication.Completion.TerminationLaw
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessProgram

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws DualCompletionLaws

def law : FiniteLaw Support :=
  CompletionTerminationLaw.law source .B .C (laws288 .B) (laws288 .C) state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)

def rate (pair : ReaderPair) : ℝ :=
  ConditionalLabels.lawPairingRate law program.labels (1 + readable.depth)
    (fun n => program.pair n.val) pair

theorem law_uniform : UniformCoordinate law x (fun _ => True) := by
  have hu := DualUniformMixtures.colorMix_uniform_complement source .B .C
    (laws288 .B) (laws288 .C) state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)
    source.flagB DualUniform.laws288_uniform.B DualUniform.laws288_uniform.C
    DualUniform.rho288.symm
  intro u
  change ((law.map (fun a : Support => a.val.val.1)).mass u) = _
  exact (CompletionTerminationLaw.law_map_mass source .B .C
    (laws288 .B) (laws288 .C) state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)
    (fun a : Leaf source => a.val.1) u).trans (hu u)

theorem x_entropy : finiteEntropy (law.map x).mass = 288 * Real.log 2 := by
  rw [uniform_coordinate_entropy law x (fun _ => True) law_uniform]
  simp only [Fintype.card_subtype_true, word_card, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow]

theorem rate_sum : rate .xy + rate .xz + rate .yz = finiteEntropy law.mass :=
  ConditionalLabels.lawPairingRate_sum law program.labels (1 + readable.depth)
    (fun n => program.pair n.val) record_injective

end MatrixMultiplication.DualWitness

end

end OAI
