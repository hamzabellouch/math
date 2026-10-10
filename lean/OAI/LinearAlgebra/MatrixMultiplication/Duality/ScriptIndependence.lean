import OAI.LinearAlgebra.MatrixMultiplication.Duality.RootIndependence
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformInstances
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.BaseConditionalReaders

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionColorLaws DualCompletionLaws DualInformation TopologicalFlatten DualUniform

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

theorem minusLaws_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : Laws S) (m : ℕ) (hm : 0 < m) (rho : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (h : ProgramLawsIndependent S r p) :
    ProgramLawsIndependent (complete S .B m) (ReadableTensor.raise S r .B m)
      (minusLaws S p m hm rho hrho0 hrho1) := by
  intro c n hn
  cases c
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .B .B (p .B) (p .B) 0 (le_refl 0) zero_lt_one (Or.inr rfl) hm
      (by intro hh; simp [ownerPair] at hh) (h .B) (h .B) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .B .A (p .B) (p .A) rho hrho0.le hrho1 (Or.inl (by intro he; cases he)) hm
      (by intro hh; simp [ownerPair] at hh) (h .B) (h .A) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .B .C (p .B) (p .C) rho hrho0.le hrho1 (Or.inl (by intro he; cases he)) hm
      (by intro hh; simp [ownerPair] at hh) (h .B) (h .C) n hn

theorem plusALaws_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : Laws S) (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (h : ProgramLawsIndependent S r p)
    (hu : UniformLaws S p) :
    ProgramLawsIndependent (complete S .A m) (ReadableTensor.raise S r .A m)
      (plusALaws S p m hm rho hA hC hrho0 hrho1) := by
  intro c n hn
  cases c
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .A .B (p .A) (p .B) (1-rho) (sub_nonneg.mpr hrho1.le) (sub_lt_self 1 hrho0)
      (Or.inl (by intro he; cases he)) hm (by intro hh; simp [ownerPair] at hh) (h .A) (h .B) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .A .A (p .A) (p .A) 0 (le_refl 0) zero_lt_one (Or.inr rfl) hm
      (by intro hh; simp [ownerPair] at hh) (h .A) (h .A) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .A .C (p .A) (p .C) (gibbsWeight hA hC)
      (gibbsWeight_nonneg hA hC) (gibbsWeight_lt_one hA hC) (Or.inl (by intro he; cases he)) hm
      (fun _ x => (hu.A x).trans (hu.C x).symm) (h .A) (h .C) n hn

theorem plusCLaws_independent (S : FlaggedTensor X Y Z) (r : ReadableTensor S)
    (p : Laws S) (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (h : ProgramLawsIndependent S r p)
    (hu : UniformLaws S p) :
    ProgramLawsIndependent (complete S .C m) (ReadableTensor.raise S r .C m)
      (plusCLaws S p m hm rho hA hC hrho0 hrho1) := by
  intro c n hn
  cases c
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .C .B (p .C) (p .B) (1-rho) (sub_nonneg.mpr hrho1.le) (sub_lt_self 1 hrho0)
      (Or.inl (by intro he; cases he)) hm (by intro hh; simp [ownerPair] at hh) (h .C) (h .B) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .C .A (p .C) (p .A) (gibbsWeight hC hA)
      (gibbsWeight_nonneg hC hA) (gibbsWeight_lt_one hC hA) (Or.inl (by intro he; cases he)) hm
      (fun _ x => (hu.C x).trans (hu.A x).symm) (h .C) (h .A) n hn
  · exact conditionalCompletionLaw_program_factorization S r.program r.context_eq r.view_eq
      .C .C (p .C) (p .C) 0 (le_refl 0) zero_lt_one (Or.inr rfl) hm
      (by intro hh; simp [ownerPair] at hh) (h .C) (h .C) n hn

abbrev dualReadable (s : Script) :=
  ReadableTensor.script BaseTwo.flagged BaseConditionalReaders.baseTwoReadable s

theorem base_independent : ProgramLawsIndependent BaseTwo.flagged
    BaseConditionalReaders.baseTwoReadable baseLaws := by
  intro c n
  exact Fin.elim0 n

theorem laws2_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script2)
    (dualReadable script2) laws2 :=
  minusLaws_independent _ _ _ _ _ _ _ _ base_independent

theorem laws4_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script4)
    (dualReadable script4) laws4 :=
  plusALaws_independent _ _ _ _ _ _ _ _ _ _ laws2_independent laws2_uniform

theorem laws8_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script8)
    (dualReadable script8) laws8 :=
  plusCLaws_independent _ _ _ _ _ _ _ _ _ _ laws4_independent laws4_uniform

theorem laws24_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script24)
    (dualReadable script24) laws24 :=
  minusLaws_independent _ _ _ _ _ _ _ _ laws8_independent

theorem laws48_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script48)
    (dualReadable script48) laws48 :=
  plusCLaws_independent _ _ _ _ _ _ _ _ _ _ laws24_independent laws24_uniform

theorem laws96_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged script96)
    (dualReadable script96) laws96 :=
  minusLaws_independent _ _ _ _ _ _ _ _ laws48_independent

theorem laws288_independent : ProgramLawsIndependent (Script.tensor BaseTwo.flagged Script.dual)
    (dualReadable Script.dual) laws288 :=
  plusALaws_independent _ _ _ _ _ _ _ _ _ _ laws96_independent laws96_uniform

end MatrixMultiplication.DualProgramIndependence

end

end OAI
