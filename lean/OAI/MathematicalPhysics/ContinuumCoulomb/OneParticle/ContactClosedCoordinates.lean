import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactVertexProgram

namespace OAI

/-! The rational path keeps both original endpoints exact. Replacing its
last approximate prefix sum by the prescribed span improves its distance
to the exact reference path and does not change the polynomial program. -/

noncomputable section
namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

def closedVertex (e : Environment) (k : ℕ) : ℚ × ℚ :=
  if k = 9 then (e.2.2, 0) else vertex e k

def closedVertexPoint (e : Environment) (k : ℕ) : ContactPoint :=
  contactPoint (closedVertex e k).1 (closedVertex e k).2

theorem closedVertex_start (e : Environment) : closedVertex e 0 = (0, 0) := by
  simp [closedVertex, vertex]

theorem closedVertex_end (e : Environment) : closedVertex e 9 = (e.2.2, 0) := by
  simp [closedVertex]

theorem closedVertex_error (e : Environment) (h₀ : ℝ)
    (hl : ∀ k < 9, 1 - contactLengthTolerance ≤ (lengthAt e k : ℝ))
    (hl' : ∀ k < 9, (lengthAt e k : ℝ) ≤ 1 + contactLengthTolerance)
    (hh₀ : h₀ ∈ Set.Icc (2 / 5) (3 / 4))
    (hroot : adjustedContactSpan (fun k => (lengthAt e k : ℝ)) h₀ = (e.2.2 : ℝ))
    {k : ℕ} (hk : k ≤ 9) :
    dist (closedVertexPoint e k) (adjustedContactVertex (fun j => (lengthAt e j : ℝ)) h₀ k) ≤
      36 * ((e.1 : ℝ) + 1)⁻¹ := by
  by_cases hk9 : k = 9
  · subst k
    rw [adjustedContactVertex_end, hroot]
    simp only [closedVertexPoint, closedVertex_end, Rat.cast_zero, dist_self]
    positivity
  · simpa only [closedVertexPoint, closedVertex, ite_eq_right hk9, vertexPoint] using
      vertex_error e h₀ hl hl' hh₀ hroot hk

noncomputable opaque closedVertexProgram (k : ℕ) : Procedure environmentCode
    (prodCode ratCode ratCode) (fun e => closedVertex e k) := by
  by_cases hk : k = 9
  · let data := Procedure.second unaryCode (prodCode (listCode ratCode) ratCode)
    let target := (Procedure.second (listCode ratCode) ratCode).comp data
    exact (target.pair (Procedure.constant environmentCode ratCode 0)).congrFun (by
      intro e
      simp only [closedVertex, ite_eq_left hk, Function.comp_apply])
  · exact (vertexProgram k).congrFun (by
      intro e
      simp only [closedVertex, ite_eq_right hk])

noncomputable def closedVertexListProgram : (k : ℕ) → Procedure environmentCode
    (listCode (prodCode ratCode ratCode)) (fun e => (List.range k).map (closedVertex e))
  | 0 => (Procedure.constant environmentCode (listCode (prodCode ratCode ratCode)) []).congrFun
      (by intro e; rfl)
  | k + 1 => by
      let singleton := (Procedure.listCons (prodCode ratCode ratCode)).comp
        ((closedVertexProgram k).pair
          (Procedure.constant environmentCode (listCode (prodCode ratCode ratCode)) []))
      exact ((Procedure.listAppend (prodCode ratCode ratCode) (0, 0)).comp
        ((closedVertexListProgram k).pair singleton)).congrFun (by
          intro e
          simp only [Function.comp_apply, List.range_succ, List.map_append,
            List.map_cons, List.map_nil])

noncomputable def closedVertexListCertificate : Turing.TM2ComputableInPolyTime
    environmentCode (listCode (prodCode ratCode ratCode))
      (fun e => (List.range 10).map (closedVertex e)) := (closedVertexListProgram 10).toTM2

end ContinuumCoulomb.ContactHeightEvaluation

end

end OAI
