import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequentialRepresentationDescent

namespace OAI

/-! # Projectivity of a sequential colimit with split transition maps

This is used for countable algebras of integer-valued step functions. Finite
partition refinements give split inclusions of free modules; their actual
colimit is projective. The splitting is constructed by compatible lifts.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram
variable (D : SequentialRepresentationDiagram G)
variable (r : ∀ i, D.obj (i + 1) ⟶ D.obj i)
variable (hr : ∀ i, D.map i (i + 1) (Nat.le_succ i) ≫ r i = 𝟙 _)

/-- Correct arbitrary lifts by the retraction so that successive lifts agree. -/
def compatibleProjectiveLift [∀ i, Projective (D.obj i)]
    {E X : Rep.{0} ℤ G} (e : E ⟶ X) [Epi e] (f : ∀ i, D.obj i ⟶ X) :
    ∀ i, D.obj i ⟶ E
  | 0 => Projective.factorThru (f 0) e
  | i + 1 => r i ≫ compatibleProjectiveLift e f i +
      (𝟙 _ - r i ≫ D.map i (i + 1) (Nat.le_succ i)) ≫
        Projective.factorThru (f (i + 1)) e

theorem compatibleProjectiveLift_comp [∀ i, Projective (D.obj i)]
    {E X : Rep.{0} ℤ G} (e : E ⟶ X) [Epi e] (f : ∀ i, D.obj i ⟶ X)
    (hf : ∀ i, D.map i (i + 1) (Nat.le_succ i) ≫ f (i + 1) = f i) (i : ℕ) :
    compatibleProjectiveLift D r e f i ≫ e = f i := by
  induction i with
  | zero => exact Projective.factorThru_comp _ _
  | succ i ih =>
    rw [compatibleProjectiveLift, Preadditive.add_comp, Category.assoc,
      ih, Category.assoc, Projective.factorThru_comp,
      Preadditive.sub_comp, Category.id_comp, Category.assoc, hf i]
    abel

include hr in
theorem compatibleProjectiveLift_step [∀ i, Projective (D.obj i)]
    {E X : Rep.{0} ℤ G} (e : E ⟶ X) [Epi e] (f : ∀ i, D.obj i ⟶ X) (i : ℕ) :
    D.map i (i + 1) (Nat.le_succ i) ≫ compatibleProjectiveLift D r e f (i + 1) =
      compatibleProjectiveLift D r e f i := by
  rw [compatibleProjectiveLift, Preadditive.comp_add, ← Category.assoc, hr i,
    Category.id_comp, ← Category.assoc, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, hr i, Category.id_comp, sub_self, zero_comp, add_zero]

include hr in
theorem split_colimit_projective {A : Rep.{0} ℤ G} (c : D.ColimitCocone A)
    [∀ i, Projective (D.obj i)] : Projective A where
  factors {E X} f e := by
    intro he
    let u := compatibleProjectiveLift D r e (fun i => c.ι i ≫ f)
    have hu : ∀ i j (h : i ≤ j), D.map i j h ≫ u j = u i := by
      intro i j h
      induction h with
      | refl => rw [D.map_id, Category.id_comp]
      | @step j h ih =>
        rw [← D.map_comp i j (j + 1) h (Nat.le_succ j), Category.assoc]
        change D.map i j h ≫
          (D.map j (j + 1) (Nat.le_succ j) ≫
            compatibleProjectiveLift D r e (fun i => c.ι i ≫ f) (j + 1)) = _
        rw [compatibleProjectiveLift_step D r hr]
        exact ih
    refine ⟨c.desc E u hu, ?_⟩
    apply c.hom_ext
    intro i
    rw [← Category.assoc, c.ι_desc E u hu i]
    exact compatibleProjectiveLift_comp D r e (fun i => c.ι i ≫ f)
      (fun i => by rw [← Category.assoc, c.comm]) i

end SequentialRepresentationDiagram
end PolycyclicRecognition

end

end OAI
