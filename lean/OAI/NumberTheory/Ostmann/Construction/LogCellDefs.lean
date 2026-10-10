import OAI.NumberTheory.Ostmann.Section07SmoothPartitionBasic

namespace OAI

open scoped Classical
namespace Ostmann.Construction

noncomputable def logCellPrimes (c : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 ⌈Real.exp (c+1)⌉₊).filter Nat.Prime

noncomputable def logCellWeight (c : ℝ) (p : ℕ) : ℝ :=
  Ostmann.smoothPartition (Real.log p-c)/(p:ℝ)

noncomputable def logCellMass (c : ℝ) (E : Finset ℕ) : ℝ :=
  ∑ p ∈ logCellPrimes c \ E, logCellWeight c p

noncomputable def logCellLogMass (c : ℝ) (E : Finset ℕ) : ℝ :=
  ∑ p ∈ logCellPrimes c \ E, Real.log p * logCellWeight c p

end Ostmann.Construction

end OAI
