import OAI.LinearAlgebra.MatrixMultiplication.Duality.CompletionLaws
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformUpdates
import OAI.LinearAlgebra.MatrixMultiplication.Duality.UniformMixtures
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Partitions

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniform

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws DualUniformConditioning DualUniformUpdates
open DualUniformMixtures CompletionPartitions
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

structure UniformLaws (S : FlaggedTensor X Y Z) (p : Laws S) : Prop where
  B : UniformCoordinate (p .B) (fun a => a.val.val.1) S.flagB
  A : UniformCoordinate (p .A) (fun a => a.val.val.1) (fun x => ¬ S.flagB x)
  C : UniformCoordinate (p .C) (fun a => a.val.val.1) (fun x => ¬ S.flagB x)

theorem UniformLaws.color (S : FlaggedTensor X Y Z) (p : Laws S)
    (h : UniformLaws S p) (c : Color) :
    UniformCoordinate (p c) (fun a => a.val.val.1)
      (fun x => if c = .B then S.flagB x else ¬ S.flagB x) := by
  cases c
  · simpa using h.B
  · simpa using h.A
  · simpa using h.C

theorem UniformLaws.entropy_B (S : FlaggedTensor X Y Z) (p : Laws S)
    (h : UniformLaws S p) :
    finiteEntropy ((p .B).map (fun a => a.val.val.1)).mass = Real.log (activeCount S) :=
  uniform_coordinate_entropy (p .B) _ _ h.B

theorem UniformLaws.entropy_A (S : FlaggedTensor X Y Z) (p : Laws S)
    (h : UniformLaws S p) :
    finiteEntropy ((p .A).map (fun a => a.val.val.1)).mass = Real.log (inactiveCount S) :=
  uniform_coordinate_entropy (p .A) _ _ h.A

theorem UniformLaws.entropy_C (S : FlaggedTensor X Y Z) (p : Laws S)
    (h : UniformLaws S p) :
    finiteEntropy ((p .C).map (fun a => a.val.val.1)).mass = Real.log (inactiveCount S) :=
  uniform_coordinate_entropy (p .C) _ _ h.C

theorem conditionalCompletionLaw_uniform_common
    (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (P : X → Prop)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) P)
    (ho : UniformCoordinate po (fun a => a.val.val.1) P) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1) (fun x => ∀ i, P (x i)) :=
  conditionalCompletionLaw_uniform_independent S center output pc po m hm α hα hα' P
    (colorMix_uniform_common S center output pc po α hα hα'.le P hc ho)
    (colorMix_independent_uniform S center output pc po α hα hα'.le P hc ho)

private theorem inactive_uniform_update
    (S : FlaggedTensor X Y Z) (center output : Color) (hcenter : center ≠ .B)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1)
    (hc : UniformCoordinate pc (fun a => a.val.val.1) (fun x => ¬ S.flagB x))
    (ho : UniformCoordinate po (fun a => a.val.val.1) (fun x => ¬ S.flagB x)) :
    UniformCoordinate
      (conditionalCompletionLaw S center output pc po m hm α hα hα')
      (fun a => a.val.val.1) (fun x => ¬ (complete S center m).flagB x) := by
  apply uniform_coordinate_pred_congr _ _ (fun x => ∀ i, ¬ S.flagB (x i))
  · intro x
    change (∀ i, ¬ S.flagB (x i)) ↔ ¬ raisedFlag center .B (fun i => S.flagB (x i))
    simp [raisedFlag, hcenter]
  · exact conditionalCompletionLaw_uniform_common S center output pc po m hm α hα hα'
      (fun x => ¬ S.flagB x) hc ho

theorem minusLaws_uniform (S : FlaggedTensor X Y Z) (p : Laws S)
    (m : ℕ) (hm : 0 < m) (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (h : UniformLaws S p) (hrho : rho = activeFraction S) :
    UniformLaws (complete S .B m) (minusLaws S p m hm rho hrho0 hrho1) := by
  constructor
  · exact conditionalCompletionLaw_uniform_common S .B .B (p .B) (p .B) m hm 0
      (by norm_num) (by norm_num) S.flagB h.B h.B
  · have hu := conditionalCompletionLaw_uniform_incident S .B .A (Or.inl rfl)
      (p .B) (p .A) m hm rho hrho0.le hrho1
      (colorMix_uniform_complement S .B .A (p .B) (p .A) rho hrho0.le hrho1.le
        S.flagB h.B h.A hrho)
    simpa only [minusLaws, reduceCtorEq, ite_false] using hu
  · have hu := conditionalCompletionLaw_uniform_incident S .B .C (Or.inl rfl)
      (p .B) (p .C) m hm rho hrho0.le hrho1
      (colorMix_uniform_complement S .B .C (p .B) (p .C) rho hrho0.le hrho1.le
        S.flagB h.B h.C hrho)
    simpa only [minusLaws, reduceCtorEq, ite_false] using hu

theorem plusALaws_uniform (S : FlaggedTensor X Y Z) (p : Laws S)
    (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (h : UniformLaws S p) (hrho : rho = activeFraction S) :
    UniformLaws (complete S .A m) (plusALaws S p m hm rho hA hC hrho0 hrho1) := by
  constructor
  · have hu := conditionalCompletionLaw_uniform_incident S .A .B (Or.inr rfl)
      (p .A) (p .B) m hm (1-rho) (sub_nonneg.mpr hrho1.le) (by linarith)
      (colorMix_uniform_complement_reverse S .A .B (p .A) (p .B) rho
        (sub_nonneg.mpr hrho1.le) (by linarith) S.flagB h.A h.B hrho)
    simpa only [plusALaws, ite_eq_left rfl, ite_true] using hu
  · exact inactive_uniform_update S .A .A (by intro h; cases h) (p .A) (p .A) m hm 0
      (by norm_num) (by norm_num) h.A h.A
  · exact inactive_uniform_update S .A .C (by intro h; cases h) (p .A) (p .C) m hm
      (gibbsWeight hA hC) (gibbsWeight_nonneg hA hC) (gibbsWeight_lt_one hA hC) h.A h.C

theorem plusCLaws_uniform (S : FlaggedTensor X Y Z) (p : Laws S)
    (m : ℕ) (hm : 0 < m) (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (h : UniformLaws S p) (hrho : rho = activeFraction S) :
    UniformLaws (complete S .C m) (plusCLaws S p m hm rho hA hC hrho0 hrho1) := by
  constructor
  · have hu := conditionalCompletionLaw_uniform_incident S .C .B (Or.inr rfl)
      (p .C) (p .B) m hm (1-rho) (sub_nonneg.mpr hrho1.le) (by linarith)
      (colorMix_uniform_complement_reverse S .C .B (p .C) (p .B) rho
        (sub_nonneg.mpr hrho1.le) (by linarith) S.flagB h.C h.B hrho)
    simpa only [plusCLaws, ite_eq_left rfl, ite_true] using hu
  · exact inactive_uniform_update S .C .A (by intro h; cases h) (p .C) (p .A) m hm
      (gibbsWeight hC hA) (gibbsWeight_nonneg hC hA) (gibbsWeight_lt_one hC hA) h.C h.A
  · exact inactive_uniform_update S .C .C (by intro h; cases h) (p .C) (p .C) m hm 0
      (by norm_num) (by norm_num) h.C h.C

private theorem pure_map_mass {A U : Type*} [Fintype A] [Fintype U]
    (a : A) (f : A → U) (x : U) :
    ((FiniteLaw.pure a).map f).mass x = if f a = x then 1 else 0 := by
  rw [FiniteLaw.map_mass, Finset.sum_eq_single a]
  · simp [FiniteLaw.pure]
  · intro b _ hb
    simp [FiniteLaw.pure, hb]
  · simp

theorem baseLaws_uniform : UniformLaws BaseTwo.flagged baseLaws := by
  have hc : Fintype.card {x // BaseTwo.flagged.flagB x} = 1 := by
    exact @Fintype.card_subtype_eq (Fin 2) 1
      (inferInstanceAs (Fintype {x // BaseTwo.flagged.flagB x}))
  constructor <;> intro x <;> rw [baseLaws, pure_map_mass] <;>
    fin_cases x <;>
    norm_num [baseLeaf, BaseTwo.flagged, BaseTwo.flagB, Fintype.card_subtype_compl]
  all_goals rw [hc]

end MatrixMultiplication.DualUniform

end

end OAI
