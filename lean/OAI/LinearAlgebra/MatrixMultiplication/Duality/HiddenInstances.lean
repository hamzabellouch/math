import OAI.LinearAlgebra.MatrixMultiplication.Duality.HiddenRates
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformInstances
import OAI.LinearAlgebra.MatrixMultiplication.Duality.WitnessRecurrence

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

private theorem coord_nonempty (s : Script) : Nonempty (Script.Coord (Fin 2) s) := by
  induction s with
  | base => exact inferInstanceAs (Nonempty (Fin 2))
  | step prior center m ih =>
    let := ih
    exact inferInstanceAs (Nonempty (Fin m → Script.Coord (Fin 2) prior))
attribute [local instance] coord_nonempty

theorem base_hidden : HiddenInvariant BaseTwo.flagged baseLaws DualWitness.initial := by
  have hc : Fintype.card {x // BaseTwo.flagged.flagB x} = 1 :=
    @Fintype.card_subtype_eq (Fin 2) 1
      (inferInstanceAs (Fintype {x // BaseTwo.flagged.flagB x}))
  constructor <;>
    norm_num [baseLaws, DualWitness.initial, activeCount, inactiveCount,
      BaseTwo.flagged, BaseTwo.flagB, Fintype.card_subtype_compl]
  all_goals norm_num [hc]

theorem laws2_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script2)
    laws2 DualWitness.state2 :=
  minus_hidden BaseTwo.flagged baseLaws DualWitness.initial 2 (by norm_num)
    (by norm_num [DualWitness.initial]) (by norm_num [DualWitness.initial])
    DualUniform.base_activeFraction.symm base_hidden

theorem laws4_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script4)
    laws4 DualWitness.state4 :=
  plusA_hidden _ laws2 DualWitness.state2 2 (by norm_num)
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    DualUniform.rho2.symm laws2_hidden

theorem laws8_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script8)
    laws8 DualWitness.state8 :=
  plusC_hidden _ laws4 DualWitness.state4 2 (by norm_num)
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    DualUniform.rho4.symm laws4_hidden

theorem laws24_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script24)
    laws24 DualWitness.state24 :=
  minus_hidden _ laws8 DualWitness.state8 3 (by norm_num)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.1)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.2)
    DualUniform.rho8.symm laws8_hidden

theorem laws48_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script48)
    laws48 DualWitness.state48 :=
  plusC_hidden _ laws24 DualWitness.state24 2 (by norm_num)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.1)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.2)
    DualUniform.rho24.symm laws24_hidden

theorem laws96_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged script96)
    laws96 DualWitness.state96 :=
  minus_hidden _ laws48 DualWitness.state48 2 (by norm_num)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.1)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.2)
    DualUniform.rho48.symm laws48_hidden

theorem laws288_hidden : HiddenInvariant (Script.tensor BaseTwo.flagged Script.dual)
    laws288 DualWitness.state288 :=
  plusA_hidden _ laws96 DualWitness.state96 3 (by norm_num)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.1)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.2)
    DualUniform.rho96.symm laws96_hidden

theorem laws288_hidden_B :
    finiteEntropy (laws288 .B).mass -
      finiteEntropy ((laws288 .B).map (fun a => a.val.val.1)).mass =
        DualWitness.state288.hB := by
  rw [laws288_hidden.B,
    DualUniform.UniformLaws.entropy_B _ _ DualUniform.laws288_uniform]
  ring

theorem laws288_hidden_A :
    finiteEntropy (laws288 .A).mass -
      finiteEntropy ((laws288 .A).map (fun a => a.val.val.1)).mass =
        DualWitness.state288.hA := by
  rw [laws288_hidden.A,
    DualUniform.UniformLaws.entropy_A _ _ DualUniform.laws288_uniform]
  ring

theorem laws288_hidden_C :
    finiteEntropy (laws288 .C).mass -
      finiteEntropy ((laws288 .C).map (fun a => a.val.val.1)).mass =
        DualWitness.state288.hC := by
  rw [laws288_hidden.C,
    DualUniform.UniformLaws.entropy_C _ _ DualUniform.laws288_uniform]
  ring

theorem laws288_normalizedHidden :
    (DualWitness.state288.rho * (finiteEntropy (laws288 .B).mass -
      finiteEntropy ((laws288 .B).map (fun a => a.val.val.1)).mass) +
      (1 - DualWitness.state288.rho) * (finiteEntropy (laws288 .C).mass -
        finiteEntropy ((laws288 .C).map (fun a => a.val.val.1)).mass)) / 288 =
      DualWitness.hiddenRate := by
  rw [laws288_hidden_B, laws288_hidden_C]
  have h := DualWitness.state288_normalizedHidden
  rw [DualWitness.normalizedHidden, DualWitness.state288_max,
    DualWitness.state_factors] at h
  exact h

theorem laws288_weightedHidden :
    DualWitness.state288.rho * (finiteEntropy (laws288 .B).mass -
      finiteEntropy ((laws288 .B).map (fun a => a.val.val.1)).mass) +
      (1 - DualWitness.state288.rho) * (finiteEntropy (laws288 .C).mass -
        finiteEntropy ((laws288 .C).map (fun a => a.val.val.1)).mass) =
      288 * DualWitness.hiddenRate := by
  linarith only [laws288_normalizedHidden]

theorem laws288_coordinateEntropy :
    CompletionEntropyAlgebra.binaryEntropy DualWitness.state288.rho +
      DualWitness.state288.rho *
        Real.log (activeCount (Script.tensor BaseTwo.flagged Script.dual)) +
      (1 - DualWitness.state288.rho) *
        Real.log (inactiveCount (Script.tensor BaseTwo.flagged Script.dual)) =
      Real.log (Fintype.card (Script.Coord (Fin 2) Script.dual)) := by
  have hc := counts_pos (Script.tensor BaseTwo.flagged Script.dual)
    (by
      rw [DualUniform.rho288, DualWitness.state288_rho]
      exact DualWitness.rho288_range.1)
    (by
      rw [DualUniform.rho288, DualWitness.state288_rho]
      exact DualWitness.rho288_range.2)
  have h := CompletionEntropyAlgebra.binaryEntropy_cardinal_mixture
    (activeCount (Script.tensor BaseTwo.flagged Script.dual))
    (inactiveCount (Script.tensor BaseTwo.flagged Script.dual)) hc.1 hc.2
  dsimp only at h
  rw [← activeFraction_ratio, DualUniform.rho288, ← Nat.cast_add, partition_count] at h
  exact h

end MatrixMultiplication.DualHiddenRates

end

end OAI
