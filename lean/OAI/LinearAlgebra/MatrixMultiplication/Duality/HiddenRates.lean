import OAI.LinearAlgebra.MatrixMultiplication.Duality.LawEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Completion.CenterLaw
import OAI.LinearAlgebra.MatrixMultiplication.Duality.CompletionLaws
import OAI.LinearAlgebra.MatrixMultiplication.Duality.HiddenCounts

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

universe u

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open DualCompletionLaws CompletionPartitions CompletionEntropyAlgebra
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

structure HiddenInvariant (S : FlaggedTensor X Y Z) (p : Laws S)
    (s : DualWitness.State) : Prop where
  B : finiteEntropy (p .B).mass = Real.log (activeCount S) + s.hB
  A : finiteEntropy (p .A).mass = Real.log (inactiveCount S) + s.hA
  C : finiteEntropy (p .C).mass = Real.log (inactiveCount S) + s.hC

variable [Nonempty X]

private theorem incident_minus_entropy (S : FlaggedTensor X Y Z) (output : Color)
    (hne : Color.B ≠ output)
    (pc : FiniteLaw (ColorSlice S .B)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (rho hb ho : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (hrho : rho = activeFraction S)
    (hpc : finiteEntropy pc.mass = Real.log (activeCount S) + hb)
    (hpo : finiteEntropy po.mass = Real.log (inactiveCount S) + ho) :
    finiteEntropy (conditionalCompletionLaw S .B output pc po m hm rho h0.le h1).mass =
      Real.log (inactiveCount (complete S .B m)) +
        m * ((rho - rho ^ m) / (1 - rho ^ m) * hb +
          (1 - rho) / (1 - rho ^ m) * ho) := by
  have hc := counts_pos S (hrho ▸ h0) (hrho ▸ h1)
  have hr : (activeCount S : ℝ) / ((activeCount S : ℝ) + inactiveCount S) = rho :=
    (activeFraction_ratio S).symm.trans hrho.symm
  have he := conditionalMixEntropy_incident (activeCount S) (inactiveCount S)
    hb ho m hc.1 hc.2 hm
  dsimp only at he
  rw [hr] at he
  rw [DualLawEntropy.conditionalCompletionLaw_entropy S .B output hne,
    hpc, hpo, inactiveCount_minus_real]
  linarith only [he]

private theorem incident_plus_entropy (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S .B))
    (m : ℕ) (hm : 0 < m) (rho hcEntropy hb : ℝ) (h0 : 0 < rho) (h1 : rho < 1)
    (hrho : rho = activeFraction S)
    (hpc : finiteEntropy pc.mass = Real.log (inactiveCount S) + hcEntropy)
    (hpo : finiteEntropy po.mass = Real.log (activeCount S) + hb) :
    finiteEntropy (conditionalCompletionLaw S center .B pc po m hm (1 - rho)
      (sub_nonneg.mpr h1.le) (by linarith)).mass =
      Real.log (activeCount (complete S center m)) +
        m * (rho / (1 - (1 - rho) ^ m) * hb +
          ((1 - (1 - rho) ^ m) - rho) / (1 - (1 - rho) ^ m) * hcEntropy) := by
  have hcounts := counts_pos S (hrho ▸ h0) (hrho ▸ h1)
  have hr : (inactiveCount S : ℝ) / ((inactiveCount S : ℝ) + activeCount S) =
      1 - rho := by rw [← inactiveFraction_ratio S, ← hrho]
  have he := conditionalMixEntropy_incident (inactiveCount S) (activeCount S)
    hcEntropy hb m hcounts.2 hcounts.1 hm
  dsimp only at he
  rw [hr] at he
  have hcoeff :
      (m : ℝ) * (((1 - rho) - (1 - rho) ^ m) / (1 - (1 - rho) ^ m) * hcEntropy +
        (1 - (1 - rho)) / (1 - (1 - rho) ^ m) * hb) =
      m * (rho / (1 - (1 - rho) ^ m) * hb +
        ((1 - (1 - rho) ^ m) - rho) / (1 - (1 - rho) ^ m) * hcEntropy) := by ring
  rw [hcoeff] at he
  rw [DualLawEntropy.conditionalCompletionLaw_entropy S center .B hc,
    hpc, hpo, activeCount_plus_real S center hc]
  linarith only [he]

omit [Nonempty X] in
private theorem gibbs_entropy (S : FlaggedTensor X Y Z) (center output : Color)
    (hc : center ≠ .B) (hne : center ≠ output)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (hcEntropy hoEntropy : ℝ)
    (hpc : finiteEntropy pc.mass = Real.log (inactiveCount S) + hcEntropy)
    (hpo : finiteEntropy po.mass = Real.log (inactiveCount S) + hoEntropy) :
    finiteEntropy (conditionalCompletionLaw S center output pc po m hm
      (gibbsWeight hcEntropy hoEntropy) (gibbsWeight_nonneg _ _)
      (gibbsWeight_lt_one _ _)).mass =
      Real.log (inactiveCount (complete S center m)) +
        Real.log ((Real.exp hcEntropy + Real.exp hoEntropy) ^ m -
          Real.exp ((m : ℝ) * hcEntropy)) := by
  rw [DualLawEntropy.conditionalCompletionLaw_entropy S center output hne,
    hpc, hpo, inactiveCount_plus S center hc, Nat.cast_pow, Real.log_pow]
  have he := conditionalMixEntropy_gibbs (inactiveCount S) hcEntropy hoEntropy m hm
  dsimp only [gibbsWeight]
  linarith only [he]

theorem minus_hidden (S : FlaggedTensor X Y Z) (p : Laws S) (s : DualWitness.State)
    (m : ℕ) (hm : 0 < m) (h0 : 0 < s.rho) (h1 : s.rho < 1)
    (hrho : s.rho = activeFraction S) (h : HiddenInvariant S p s) :
    HiddenInvariant (complete S .B m) (minusLaws S p m hm s.rho h0 h1)
      (DualWitness.minus m s) := by
  constructor
  · dsimp only [minusLaws, DualWitness.minus]
    rw [conditionalCompletionLaw_same_zero_entropy, h.B,
      activeCount_minus, Nat.cast_pow, Real.log_pow]
    ring
  · exact incident_minus_entropy S .A (by intro hne; cases hne) (p .B) (p .A) m hm
      s.rho s.hB s.hA h0 h1 hrho h.B h.A
  · exact incident_minus_entropy S .C (by intro hne; cases hne) (p .B) (p .C) m hm
      s.rho s.hB s.hC h0 h1 hrho h.B h.C

theorem plusA_hidden (S : FlaggedTensor X Y Z) (p : Laws S) (s : DualWitness.State)
    (m : ℕ) (hm : 0 < m) (h0 : 0 < s.rho) (h1 : s.rho < 1)
    (hrho : s.rho = activeFraction S) (h : HiddenInvariant S p s) :
    HiddenInvariant (complete S .A m)
      (plusALaws S p m hm s.rho s.hA s.hC h0 h1) (DualWitness.plusA m s) := by
  constructor
  · exact incident_plus_entropy S .A (by intro hne; cases hne) (p .A) (p .B) m hm
      s.rho s.hA s.hB h0 h1 hrho h.A h.B
  · dsimp only [plusALaws, DualWitness.plusA]
    rw [conditionalCompletionLaw_same_zero_entropy, h.A,
      inactiveCount_plus S .A (by intro hne; cases hne), Nat.cast_pow, Real.log_pow]
    ring
  · exact gibbs_entropy S .A .C (by intro hne; cases hne) (by intro hne; cases hne) (p .A) (p .C) m hm
      s.hA s.hC h.A h.C

theorem plusC_hidden (S : FlaggedTensor X Y Z) (p : Laws S) (s : DualWitness.State)
    (m : ℕ) (hm : 0 < m) (h0 : 0 < s.rho) (h1 : s.rho < 1)
    (hrho : s.rho = activeFraction S) (h : HiddenInvariant S p s) :
    HiddenInvariant (complete S .C m)
      (plusCLaws S p m hm s.rho s.hA s.hC h0 h1) (DualWitness.plusC m s) := by
  constructor
  · exact incident_plus_entropy S .C (by intro hne; cases hne) (p .C) (p .B) m hm
      s.rho s.hC s.hB h0 h1 hrho h.C h.B
  · exact gibbs_entropy S .C .A (by intro hne; cases hne) (by intro hne; cases hne) (p .C) (p .A) m hm
      s.hC s.hA h.C h.A
  · dsimp only [plusCLaws, DualWitness.plusC]
    rw [conditionalCompletionLaw_same_zero_entropy, h.C,
      inactiveCount_plus S .C (by intro hne; cases hne), Nat.cast_pow, Real.log_pow]
    ring

end MatrixMultiplication.DualHiddenRates

end

end OAI
