import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]

@[simp] theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy, xlogx]

@[simp] theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy, xlogx]

end LeanBlast.CourtadeKumar

end

end OAI
