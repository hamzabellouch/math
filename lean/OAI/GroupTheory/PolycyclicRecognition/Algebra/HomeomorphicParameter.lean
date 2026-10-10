import Mathlib.Topology.OpenPartialHomeomorph.Composition

namespace OAI

/-! # Transporting local parameters across a homeomorphism -/

noncomputable section
namespace PolycyclicRecognition

variable {V X Y : Type*} [TopologicalSpace V] [TopologicalSpace X] [TopologicalSpace Y]
  [Zero V] [One X] [One Y]

omit [TopologicalSpace V] in
theorem parameter_zero_of_coordinates (e : X ≃ₜ Y) (he : e 1 = 1)
    (P : V → X) (Q : V → Y) (h : ∀ v, e (P v) = Q v) (hQ : Q 0 = 1) : P 0 = 1 :=
  e.injective ((h 0).trans (hQ.trans he.symm))

theorem exists_parameter_of_coordinate_homeomorph (e : X ≃ₜ Y) (he : e 1 = 1)
    (P : V → X) (Q : V → Y) (h : ∀ v, e (P v) = Q v) (hQ : Q 0 = 1)
    (hl : ∃ q : OpenPartialHomeomorph V Y,
      (0 : V) ∈ q.source ∧ q 0 = Q 0 ∧ ∀ v ∈ q.source, q v = Q v) :
    ∃ p : OpenPartialHomeomorph V X,
      (0 : V) ∈ p.source ∧ p 0 = 1 ∧ ∀ v ∈ p.source, p v = P v := by
  obtain ⟨q,hq,hq0,hqP⟩ := hl
  let p := q.trans e.symm.toOpenPartialHomeomorph
  have hp : (0 : V) ∈ p.source := ⟨hq,Set.mem_univ _⟩
  have hP (v : V) (hv : v ∈ p.source) : p v = P v := by
    apply e.injective
    change e (e.symm (q v)) = _
    rw [e.apply_symm_apply,hqP v hv.1,h]
  exact ⟨p,hp,(hP 0 hp).trans (parameter_zero_of_coordinates e he P Q h hQ),hP⟩

end PolycyclicRecognition

end

end OAI
