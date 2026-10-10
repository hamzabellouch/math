import Mathlib
import OAI.Geometry.HyperbolicGroups.PictureDual
import OAI.Geometry.HyperbolicGroups.PictureUnderlyingGraph
import OAI.Geometry.HyperbolicGroups.PictureFullSeparator

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
universe u
open Equiv Equiv.Perm PlanarRecursion
attribute [local instance] Classical.propDecidable

/-- Dual form of the proved genus-zero partition theorem, with literal
selected face classes and the original map's unordered edge-copy cuts. -/
theorem uniform_genusZero_face_partition (d : ℕ) (eta : ℝ) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (D : Type u) [Fintype D] [DecidableEq D] (M : PictureMap D),
      M.GenusZero → ∀ U : Finset (Quotient (SameCycle.setoid M.face)),
      (∀ v ∈ U, Nat.card {x : D // Quotient.mk (SameCycle.setoid M.face) x = v} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : Quotient (SameCycle.setoid M.face) → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Fintype.card (RelativeCutContact M
          (fun x => Quotient.mk (SameCycle.setoid M.face) x ∈ U)
          (part ∘ Quotient.mk (SameCycle.setoid M.face))) : ℝ) ≤ eta * U.card := by
  obtain ⟨K,hK,hh⟩ := uniform_genusZero_cut_partition d eta heta
  refine ⟨K,hK,?_⟩
  intro D _ _ M hG
  let Q (v : Perm D) : Prop :=
    ∀ U : Finset (Quotient (SameCycle.setoid v)),
      (∀ f ∈ U, Nat.card {x : D // Quotient.mk (SameCycle.setoid v) x = f} ≤ d) →
      ∃ (I : Type) (_ : Fintype I) (part : Quotient (SameCycle.setoid v) → I),
        (∀ i, (U.filter (fun x => part x = i)).card ≤ K) ∧
        (Nat.card {x : D // Quotient.mk (SameCycle.setoid v) x ∈ U ∧
            Quotient.mk (SameCycle.setoid v) (M.edge x) ∈ U ∧
            part (Quotient.mk (SameCycle.setoid v) x) ≠
              part (Quotient.mk (SameCycle.setoid v) (M.edge x)) ∧
            M.number x < M.number (M.edge x)} : ℝ) ≤ eta * U.card
  have h := hh D M.dual (M.dual_genusZero hG)
  simp only [← Nat.card_eq_fintype_card] at h
  have hQ : Q M.dual.vertex := by
    simpa only [Q,PictureMap.GraphVertex,PictureMap.vertexClass,RelativeCutContact,
      Function.comp_apply,PictureMap.dual_edge,PictureMap.number] using h
  rw [M.dual_vertex] at hQ
  simpa only [Q,RelativeCutContact,Function.comp_apply,← Nat.card_eq_fintype_card] using hQ

end HyperbolicObstruction.PictureSwitch
end

end OAI
