import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalProductRepresentation
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Basic

namespace OAI

/-! # Continuous representation descent across an open normal product -/

noncomputable section
namespace PolycyclicRecognition

variable {N D G A : Type*} [Group N] [Group D] [Group G] [Group A]
  [TopologicalSpace N] [TopologicalSpace D] [TopologicalSpace G] [TopologicalSpace A]
  [ContinuousMul G] [ContinuousMul A]

/-- An open surjective factor product is a quotient map, so algebraic
representation descent preserves continuity. -/
theorem exists_continuous_representation_of_open_factor_maps
    (φ : D →* MulAut N) (iN : N →* G) (iD : D →* G)
    (hiN : Continuous iN) (hiD : Continuous iD)
    (hbase : ∀ d, iN.comp (φ d).toMonoidHom =
      (MulAut.conj (iD d)).toMonoidHom.comp iN)
    (hs : Function.Surjective (fun p : N × D => iN p.1 * iD p.2))
    (ho : IsOpenMap (fun p : N × D => iN p.1 * iD p.2))
    (fN : N →* A) (fD : D →* A) (hfN : Continuous fN) (hfD : Continuous fD)
    (hconj : ∀ d n, fN (φ d n) = fD d * fN n * (fD d)⁻¹)
    (hagree : ∀ n d, iN n = iD d → fN n = fD d) :
    ∃ f : G →* A, Continuous f ∧ ∀ n d, f (iN n * iD d) = fN n * fD d := by
  obtain ⟨f,he⟩ := exists_representation_of_factor_maps φ iN iD hbase
    (fun g => by obtain ⟨⟨n,d⟩,h⟩ := hs g; exact ⟨n,d,h⟩) fN fD hconj hagree
  have hq := ho.isQuotientMap
    ((hiN.comp continuous_fst).mul (hiD.comp continuous_snd)) hs
  refine ⟨f,hq.continuous_iff.mpr ?_,he⟩
  have heq : f ∘ (fun p : N × D => iN p.1 * iD p.2) =
      (fun p : N × D => fN p.1 * fD p.2) := funext fun p => he p.1 p.2
  rw [heq]
  exact (hfN.comp continuous_fst).mul (hfD.comp continuous_snd)

end PolycyclicRecognition

end

end OAI
