import OAI.LinearAlgebra.MatrixMultiplication.Duality.Uniform

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
namespace MatrixMultiplication.DualUniform

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

private theorem coord_nonempty (s : Script) : Nonempty (Script.Coord (Fin 2) s) := by
  induction s with
  | base => exact inferInstanceAs (Nonempty (Fin 2))
  | step prior center m ih =>
    let _ := ih
    exact inferInstanceAs (Nonempty (Fin m → Script.Coord (Fin 2) prior))
attribute [local instance] coord_nonempty

theorem base_activeFraction : activeFraction BaseTwo.flagged = (1/2 : ℝ) := by
  have hc : activeCount BaseTwo.flagged = 1 :=
    @Fintype.card_subtype_eq (Fin 2) 1
      (inferInstanceAs (Fintype {x // BaseTwo.flagged.flagB x}))
  rw [activeFraction, hc]
  norm_num

theorem rho2 : activeFraction (Script.tensor BaseTwo.flagged script2) =
    DualWitness.state2.rho := by
  change activeFraction (complete BaseTwo.flagged .B 2) = _
  rw [activeFraction_minus, base_activeFraction]
  rfl

theorem rho4 : activeFraction (Script.tensor BaseTwo.flagged script4) =
    DualWitness.state4.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script2) .A 2) = _
  rw [activeFraction_plus _ .A (by intro h; cases h), rho2]
  rfl

theorem rho8 : activeFraction (Script.tensor BaseTwo.flagged script8) =
    DualWitness.state8.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script4) .C 2) = _
  rw [activeFraction_plus _ .C (by intro h; cases h), rho4]
  rfl

theorem rho24 : activeFraction (Script.tensor BaseTwo.flagged script24) =
    DualWitness.state24.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script8) .B 3) = _
  rw [activeFraction_minus, rho8]
  rfl

theorem rho48 : activeFraction (Script.tensor BaseTwo.flagged script48) =
    DualWitness.state48.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script24) .C 2) = _
  rw [activeFraction_plus _ .C (by intro h; cases h), rho24]
  rfl

theorem rho96 : activeFraction (Script.tensor BaseTwo.flagged script96) =
    DualWitness.state96.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script48) .B 2) = _
  rw [activeFraction_minus, rho48]
  rfl

theorem rho288 : activeFraction (Script.tensor BaseTwo.flagged Script.dual) =
    DualWitness.state288.rho := by
  change activeFraction (complete (Script.tensor BaseTwo.flagged script96) .A 3) = _
  rw [activeFraction_plus _ .A (by intro h; cases h), rho96]
  rfl

theorem laws2_uniform : UniformLaws (Script.tensor BaseTwo.flagged script2) laws2 :=
  minusLaws_uniform BaseTwo.flagged baseLaws 2 (Nat.zero_lt_succ _) (1/2) (by norm_num)
    (by norm_num) baseLaws_uniform base_activeFraction.symm

theorem laws4_uniform : UniformLaws (Script.tensor BaseTwo.flagged script4) laws4 :=
  plusALaws_uniform _ laws2 2 (Nat.zero_lt_succ _)
    DualWitness.state2.rho DualWitness.state2.hA DualWitness.state2.hC
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    laws2_uniform rho2.symm

theorem laws8_uniform : UniformLaws (Script.tensor BaseTwo.flagged script8) laws8 :=
  plusCLaws_uniform _ laws4 2 (Nat.zero_lt_succ _)
    DualWitness.state4.rho DualWitness.state4.hA DualWitness.state4.hC
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA]) laws4_uniform rho4.symm

theorem laws24_uniform : UniformLaws (Script.tensor BaseTwo.flagged script24) laws24 :=
  minusLaws_uniform _ laws8 3 (Nat.zero_lt_succ _) DualWitness.state8.rho
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.1)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.2)
    laws8_uniform rho8.symm

theorem laws48_uniform : UniformLaws (Script.tensor BaseTwo.flagged script48) laws48 :=
  plusCLaws_uniform _ laws24 2 (Nat.zero_lt_succ _)
    DualWitness.state24.rho DualWitness.state24.hA DualWitness.state24.hC
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.1)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.2)
    laws24_uniform rho24.symm

theorem laws96_uniform : UniformLaws (Script.tensor BaseTwo.flagged script96) laws96 :=
  minusLaws_uniform _ laws48 2 (Nat.zero_lt_succ _) DualWitness.state48.rho
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.1)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.2)
    laws48_uniform rho48.symm

theorem laws288_uniform : UniformLaws (Script.tensor BaseTwo.flagged Script.dual) laws288 :=
  plusALaws_uniform _ laws96 3 (Nat.zero_lt_succ _)
    DualWitness.state96.rho DualWitness.state96.hA DualWitness.state96.hC
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.1)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.2)
    laws96_uniform rho96.symm

end MatrixMultiplication.DualUniform

end

end OAI
