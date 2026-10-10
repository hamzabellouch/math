import OAI.Analysis.Pureness.Stabilization.MatrixParityClasses

namespace OAI
noncomputable section
open scoped NNReal CStarAlgebra
namespace CuntzTrace
variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure PositiveCore where
  carrier : Set (Positive A)
  approximate : ∀ (a : Positive A) (ε : ℝ), 0 < ε → ∃ b ∈ carrier, ‖a.1-b.1‖ < ε
  cut_mem : ∀ b ∈ carrier, ∀ ε : ℝ≥0, Positive.cut ε b ∈ carrier

variable {A}
def matrixPositiveCore : PositiveCore (MatrixLimit A) where
  carrier := {a | ∃ (n : ℕ) (M : Positive (FinMatrix A n)), Positive.map (matrixLimitStage n) M = a}
  approximate a ε hε := by
    obtain ⟨n,M,hM⟩ := matrixLimit_positive_approximation a hε
    exact ⟨_,⟨n,M,rfl⟩,hM⟩
  cut_mem := by
    rintro _ ⟨n,M,rfl⟩ ε
    exact ⟨n,Positive.cut ε M,Positive.map_cut _ _ _⟩

variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def PositiveCore.prod (S : PositiveCore A) (T : PositiveCore B) : PositiveCore (A × B) where
  carrier := {a | Positive.map (NonUnitalStarAlgHom.fst ℂ A B) a ∈ S.carrier ∧
    Positive.map (NonUnitalStarAlgHom.snd ℂ A B) a ∈ T.carrier}
  approximate a ε hε := by
    obtain ⟨b,hb,hab⟩ := S.approximate (Positive.map (NonUnitalStarAlgHom.fst ℂ A B) a) ε hε
    obtain ⟨c,hc,hac⟩ := T.approximate (Positive.map (NonUnitalStarAlgHom.snd ℂ A B) a) ε hε
    refine ⟨⟨(b.1,c.1),b.2,c.2⟩,⟨hb,hc⟩,?_⟩
    exact max_lt hab hac
  cut_mem a ha ε := by
    change Positive.map _ _ ∈ _ ∧ Positive.map _ _ ∈ _
    rw [Positive.map_cut,Positive.map_cut]
    exact ⟨S.cut_mem _ ha.1 ε,T.cut_mem _ ha.2 ε⟩

theorem PositiveCore.maps_eq (S : PositiveCore A) (f g : A →⋆ₙₐ[ℂ] B)
    (h : ∀ a ∈ S.carrier, CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a))
    (a : Positive A) : CuntzClass.mk (Positive.map f a) = CuntzClass.mk (Positive.map g a) :=
  cuntzClass_maps_eq_of_dense f g S.carrier S.approximate S.cut_mem h a

theorem matrixPositiveCore_common (a b : Positive (MatrixLimit A))
    (ha : a ∈ matrixPositiveCore.carrier) (hb : b ∈ matrixPositiveCore.carrier) :
    ∃ (n : ℕ) (M N : Positive (FinMatrix A n)),
      Positive.map (matrixLimitStage n) M = a ∧ Positive.map (matrixLimitStage n) N = b := by
  obtain ⟨n,M,rfl⟩ := ha
  obtain ⟨m,N,rfl⟩ := hb
  refine ⟨max n m,Positive.map (matrixInclusion (le_max_left n m)) M,
    Positive.map (matrixInclusion (le_max_right n m)) N,?_,?_⟩ <;>
    apply Subtype.ext <;> exact matrixLimitStage_compatible _ _
end CuntzTrace

end

end OAI
