import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactRationalCoordinates
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactHeightScheduleProgram
import OAI.Computability.QuantumFactoring.BitStackListOps

namespace OAI

/-! Literal polynomial-time rational coordinates for a fixed nine-link
contact path. The height program is followed by four dyadic root evaluations
and the fixed finite prefix sums. -/

namespace ContinuumCoulomb.ContactHeightEvaluation
open scoped BigOperators
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque stepXProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => stepX x.1 x.2 k) := by
  by_cases hs : k = 2 ∨ k = 3 ∨ k = 5 ∨ k = 6
  · exact (rootProgram k).congrFun (by intro x; simp only [stepX, ite_eq_left hs])
  · exact (lengthProgram k).congrFun (by intro x; simp only [stepX, ite_eq_right hs])

noncomputable opaque stepYProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => stepY x.2 k) := by
  by_cases hs : k = 2 ∨ k = 3
  · exact heightProgram.congrFun (by intro x; simp only [stepY, ite_eq_left hs])
  · by_cases hs' : k = 5 ∨ k = 6
    · exact (Procedure.ratNeg.comp heightProgram).congrFun (by
        intro x
        simp only [Function.comp_apply, stepY, ite_eq_right hs, ite_eq_left hs'])
    · exact (Procedure.constant inputCode ratCode 0).congrFun (by
        intro x
        simp only [stepY, ite_eq_right hs, ite_eq_right hs'])

noncomputable def prefixXProgram : (k : ℕ) → Procedure inputCode ratCode
    (fun x => ∑ j ∈ Finset.range k, stepX x.1 x.2 j)
  | 0 => (Procedure.constant inputCode ratCode 0).congrFun (by intro x; simp)
  | k + 1 => (Procedure.ratAdd.comp ((prefixXProgram k).pair (stepXProgram k))).congrFun
      (by intro x; simp only [Function.comp_apply, Finset.sum_range_succ])

noncomputable def prefixYProgram : (k : ℕ) → Procedure inputCode ratCode
    (fun x => ∑ j ∈ Finset.range k, stepY x.2 j)
  | 0 => (Procedure.constant inputCode ratCode 0).congrFun (by intro x; simp)
  | k + 1 => (Procedure.ratAdd.comp ((prefixYProgram k).pair (stepYProgram k))).congrFun
      (by intro x; simp only [Function.comp_apply, Finset.sum_range_succ])

noncomputable opaque coordinateInputProgram : Procedure environmentCode inputCode
    (fun e => (e, scheduledValue e)) :=
  (Procedure.identity environmentCode).pair scheduledProgram

noncomputable opaque vertexProgram (k : ℕ) : Procedure environmentCode
    (prodCode ratCode ratCode) (fun e => vertex e k) :=
  (((prefixXProgram k).pair (prefixYProgram k)).comp coordinateInputProgram).congrFun
    (by intro e; rfl)

noncomputable def vertexListProgram : (k : ℕ) → Procedure environmentCode
    (listCode (prodCode ratCode ratCode)) (fun e => (List.range k).map (vertex e))
  | 0 => (Procedure.constant environmentCode (listCode (prodCode ratCode ratCode)) []).congrFun
      (by intro e; rfl)
  | k + 1 => by
      let singleton := (Procedure.listCons (prodCode ratCode ratCode)).comp
        ((vertexProgram k).pair
          (Procedure.constant environmentCode (listCode (prodCode ratCode ratCode)) []))
      exact ((Procedure.listAppend (prodCode ratCode ratCode) (0, 0)).comp
        ((vertexListProgram k).pair singleton)).congrFun (by
          intro e
          simp only [Function.comp_apply, List.range_succ, List.map_append,
            List.map_cons, List.map_nil])

noncomputable def vertexListCertificate : Turing.TM2ComputableInPolyTime
    environmentCode (listCode (prodCode ratCode ratCode))
      (fun e => (List.range 10).map (vertex e)) := (vertexListProgram 10).toTM2

end ContinuumCoulomb.ContactHeightEvaluation

end OAI
