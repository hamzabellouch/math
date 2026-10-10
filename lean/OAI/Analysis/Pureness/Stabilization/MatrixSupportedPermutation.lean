import OAI.Analysis.Pureness.Stabilization.MatrixPermutation

namespace OAI
noncomputable section
open scoped CStarAlgebra
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A]

theorem matrix_supported_permutation {ι : Type*} [Finite ι] {n : ℕ}
    (f g : ι ↪ Fin n) (M N : FinMatrix A n)
    (hentries : ∀ i j, M (f i) (f j) = N (g i) (g j))
    (hM : ∀ i j, i ∉ Set.range f ∨ j ∉ Set.range f → M i j = 0)
    (hN : ∀ i j, i ∉ Set.range g ∨ j ∉ Set.range g → N i j = 0) :
    ∃ e : Equiv.Perm (Fin n), matrixPermute e M = N := by
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  refine ⟨e,?_⟩
  apply CStarMatrix.ext; intro i j
  obtain ⟨p,rfl⟩ := e.surjective i
  obtain ⟨q,rfl⟩ := e.surjective j
  rw [matrixPermute_entry]
  have hout (p : Fin n) (hp : p ∉ Set.range f) : e p ∉ Set.range g := by
    rintro ⟨i,hi⟩
    exact hp ⟨i,e.injective ((he i).trans hi)⟩
  by_cases hp : p ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hp
    by_cases hq : q ∈ Set.range f
    · obtain ⟨b,rfl⟩ := hq
      rw [he,he,hentries]
    · rw [hM _ _ (Or.inr hq),hN _ _ (Or.inr (hout q hq))]
  · rw [hM _ _ (Or.inl hp),hN _ _ (Or.inl (hout p hp))]

variable [PartialOrder A] [StarOrderedRing A]

theorem matrix_supported_cuntzClass {ι : Type*} [Finite ι] {n : ℕ}
    (f g : ι ↪ Fin n) (a b : Positive (FinMatrix A n))
    (hentries : ∀ i j, a.1 (f i) (f j) = b.1 (g i) (g j))
    (ha : ∀ i j, i ∉ Set.range f ∨ j ∉ Set.range f → a.1 i j = 0)
    (hb : ∀ i j, i ∉ Set.range g ∨ j ∉ Set.range g → b.1 i j = 0) :
    CuntzClass.mk a = CuntzClass.mk b := by
  obtain ⟨e,he⟩ := matrix_supported_permutation f g a.1 b.1 hentries ha hb
  have h : Positive.map (matrixPermute e) a = b := Subtype.ext he
  rw [← h,matrixPermute_cuntzClass]
end CuntzTrace

end

end OAI
