import OAI.Analysis.JiangSu.Absorption.ConnectedUnitaryLift

namespace OAI

/-! Connected lifts of connected unitaries, retaining the component of the
identity needed when a central buffer is realized in a norm ultrapower. -/
noncomputable section
open scoped CStarAlgebra

namespace CStarConnectedLift
variable {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]

/-- The exponential-product lift stays in the identity path component. -/
theorem connected_unitary_lift (q : C →⋆ₐ[ℂ] D) (hq : Function.Surjective q)
    (u : unitary D) (hu : Joined 1 u) :
    ∃ v : unitary C, Joined 1 v ∧ Unitary.map (starMonoidHom q) v = u := by
  obtain ⟨l, hl⟩ := Unitary.mem_pathComponentOne_iff.mp hu
  have he (a : selfAdjoint D) : ∃ v : unitary C,
      Joined 1 v ∧ Unitary.map (starMonoidHom q) v = selfAdjoint.expUnitary a := by
    obtain ⟨b, hb⟩ := selfAdjoint_lift q hq a
    refine ⟨selfAdjoint.expUnitary b, selfAdjoint.joined_one_expUnitary b, ?_⟩
    rw [map_expUnitary]
    congr 1
    exact Subtype.ext hb
  have hs : ∃ v : unitary C, Joined 1 v ∧
      Unitary.map (starMonoidHom q) v = (l.map selfAdjoint.expUnitary).prod := by
    clear hl
    induction l with
    | nil => exact ⟨1, Joined.refl 1, map_one _⟩
    | cons a l ih =>
      obtain ⟨v, hvj, hv⟩ := he a
      obtain ⟨w, hwj, hw⟩ := ih
      refine ⟨v * w, ?_, ?_⟩
      · simpa only [one_mul] using hvj.mul hwj
      · simp only [map_mul, hv, hw, List.map_cons, List.prod_cons]
  obtain ⟨v, hvj, hv⟩ := hs
  exact ⟨v, hvj, hv.trans hl⟩

end CStarConnectedLift

end

end OAI
