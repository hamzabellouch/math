import OAI.Algebra.Finitistic.Rectification.VertexZeroTotal

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace LittleFinitistic.FirstVertex
open ExternalTensor.Section4
section General
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
def biprodInlIso {X Y : D} (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  hom_inv_id := by simp
  inv_hom_id := by
    apply biprod.hom_ext
    · simp
    · exact hY.eq_of_tgt _ _

theorem mapped_inl_isIso (F : C ⥤ D) [F.Additive] (X Y : C) (hY : IsZero (F.obj Y)) :
    IsIso (F.map (biprod.inl : X ⟶ X ⊞ Y)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts F
  rw [← isIso_comp_right_iff _ (F.mapBiprod X Y).hom]
  have he : F.map (biprod.inl : X ⟶ X ⊞ Y) ≫ (F.mapBiprod X Y).hom = biprod.inl := by
    apply biprod.hom_ext
    · erw [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
        ← Functor.map_comp, biprod.inl_fst, F.map_id, biprod.inl_fst]
    · erw [Functor.mapBiprod_hom, Category.assoc, biprod.lift_snd,
        ← Functor.map_comp, biprod.inl_snd, F.map_zero, biprod.inl_snd]
  rw [he]
  exact (biprodInlIso hY).isIso_hom
end General

universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
local notation "B" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
abbrev vertexComplex := (VertexZeroTotal.vertexFunctor P).mapHomologicalComplex (.up ℤ)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

/-- The original first induced column includes into the actual zero column. -/
def columnInclusion : (columnComplex k B (s).e₀).obj D₀ ⟶ L0Prime s D₀ D₁ D₂ f g := biprod.inl

theorem columnInclusion_isIso :
    IsIso ((vertexComplex P).map (columnInclusion P D₀ D₁ D₂ f g)) := by
  have := preservesBinaryBiproducts_of_preservesBiproducts (vertexComplex P)
  apply mapped_inl_isIso
  apply ((vertexComplex P).mapBiprod _ _).isZero_iff.mpr
  rw [biprod_isZero_iff]
  exact ⟨VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 0 1 (by decide) D₁,
    VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 0 2 (by decide) D₂⟩

/-- The manuscript's original first-vertex insertion into the constructed total. -/
def iota : D₀ ⟶ (vertexComplex P).obj (InducedRectification.total s D₀ D₁ D₂ f g H) :=
  (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 0 D₀).hom ≫
    (vertexComplex P).map (columnInclusion P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H)

/-- At the first vertex the original insertion is already a chain isomorphism. -/
theorem iota_isIso : IsIso (iota P D₀ D₁ D₂ f g H) := by
  have := columnInclusion_isIso P D₀ D₁ D₂ f g
  have := VertexZeroTotal.inclusion_isIso P D₀ D₁ D₂ f g H
  let e : D₀ ≅ (vertexComplex P).obj ((columnComplex k B (s).e₀).obj D₀) :=
    VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 0 D₀
  change IsIso (e.hom ≫ (vertexComplex P).map (columnInclusion P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H))
  infer_instance
end LittleFinitistic.FirstVertex

end

end OAI
