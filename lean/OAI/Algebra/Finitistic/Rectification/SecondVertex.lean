import OAI.Algebra.Finitistic.Rectification.GradedVertexAcyclic
import OAI.Algebra.Finitistic.Rectification.FirstVertex

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SecondVertex
open ExternalTensor.Section4 ExternalTensor.Section4.SourceFiltration
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)
variable (D₀ D₁ D₂ : RightComplex (QuadraticEncoding.B P))
variable (f : Fin (d+1) → (D₀ ⟶ D₁)) (g : Fin (d+1) → (D₁ ⟶ D₂))
local notation "T" => QuadraticEncoding.B P
local notation "s" => ConcreteQuadraticDiagram.quadratic P
abbrev vertex := BimoduleVertex.functor k (QuadraticEncoding.B P)
  (ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) 1)
abbrev vertexComplex := (vertex P).mapHomologicalComplex (.up ℤ)

def intoF1 : (columnComplex k T (s).e₁).obj D₁ ⟶ Exactness.F1 s D₀ D₁ D₂ f g :=
  biprod.inl ≫ RectificationTotal.inclusion (p1 (Exactness.data s D₀ D₁ D₂ f g)) 0
    (h1 (Exactness.data s D₀ D₁ D₂ f g))

theorem intoF1_isIso : IsIso ((vertexComplex P).map (intoF1 P D₀ D₁ D₂ f g)) := by
  let F := vertex P
  let G := vertexComplex P
  have hz : IsZero (G.obj (Z (k := k) (B := T))) := by
    apply G.map_isZero
    apply ZeroColumnTotal.complex_zero
    intro n
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hv : IsZero (G.obj ((columnComplex k T (s).e₂).obj D₂)) :=
    VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 1 2 (by decide) D₂
  have hs : IsZero (G.obj (F1₁ (Exactness.data s D₀ D₁ D₂ f g))) := by
    apply (G.mapBiproduct _).isZero_iff.mpr
    exact sum_isZero _ (fun _ =>
      VertexColumnComplex.reverse_isZero (QuadraticEncoding.composition P) 1 2 (by decide) D₁)
  have hi := ZeroColumnTotal.mapped_inclusion_isIso
    (p1 (Exactness.data s D₀ D₁ D₂ f g)) 0 (h1 (Exactness.data s D₀ D₁ D₂ f g)) F
    (fun n => (HomologicalComplex.eval _ _ n).map_isZero hs)
    (fun n => (HomologicalComplex.eval _ _ n).map_isZero hz)
  have hj := FirstVertex.mapped_inl_isIso G
    ((columnComplex k T (s).e₁).obj D₁) ((columnComplex k T (s).e₂).obj D₂) hv
  let := hi
  let := hj
  dsimp [intoF1]
  erw [Functor.map_comp]
  exact (show IsIso (G.map (biprod.inl :
    (columnComplex k T (s).e₁).obj D₁ ⟶ F1₀ (Exactness.data s D₀ D₁ D₂ f g)) ≫
      G.map (RectificationTotal.inclusion (p1 (Exactness.data s D₀ D₁ D₂ f g)) 0
        (h1 (Exactness.data s D₀ D₁ D₂ f g)))) from by
    have : IsIso (G.map (biprod.inl :
      (columnComplex k T (s).e₁).obj D₁ ⟶ F1₀ (Exactness.data s D₀ D₁ D₂ f g))) := hj
    rw [isIso_comp_left_iff]
    exact hi)

variable (H : ∀ r, Homotopy (relationMap (ConcreteQuadraticDiagram.quadratic P) D₀ D₁ D₂ f g r) 0)

theorem filtration_inclusion_quasiIso :
    QuasiIso ((vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)) := by
  let S := Complex.source0 s D₀ D₁ D₂ f g H
  exact RectificationAcyclic.quasiIso_of_acyclic_quotient (S.map (vertexComplex P))
    (Complex.vertex_shortExact ((s).e₁) ((ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem 1) S
      (Complex.source0_shortExact s D₀ D₁ D₂ f g H))
    (GradedVertexAcyclic.grade0_vertex1_acyclic P D₀ D₁ D₂ f g)

def iota : D₁ ⟶ (vertexComplex P).obj (Exactness.P s D₀ D₁ D₂ f g H) :=
  (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 1 D₁).hom ≫
    (vertexComplex P).map (intoF1 P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H)

theorem iota_quasiIso : QuasiIso (iota P D₀ D₁ D₂ f g H) := by
  let := intoF1_isIso P D₀ D₁ D₂ f g
  let := filtration_inclusion_quasiIso P D₀ D₁ D₂ f g H
  let e : D₁ ≅ (vertexComplex P).obj ((columnComplex k T (s).e₁).obj D₁) :=
    VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 1 D₁
  change QuasiIso (e.hom ≫ (vertexComplex P).map (intoF1 P D₀ D₁ D₂ f g) ≫
    (vertexComplex P).map (Exactness.i1 s D₀ D₁ D₂ f g H))
  infer_instance

/-- The filtration route retains the original vertex-one summand insertion. -/
theorem intoF1_nested : intoF1 P D₀ D₁ D₂ f g ≫ Exactness.i1 s D₀ D₁ D₂ f g H =
    (Exactness.data s D₀ D₁ D₂ f g).in₁ ≫
      InducedRectification.inclusion s D₀ D₁ D₂ f g H := by
  exact (Category.assoc _ _ _).trans (congrArg
    (fun h => (biprod.inl : (columnComplex k T (s).e₁).obj D₁ ⟶
      F1₀ (Exactness.data s D₀ D₁ D₂ f g)) ≫ h)
    ((include1 (inducedData s D₀ D₁ D₂ f g) (nullHomotopy s D₀ D₁ D₂ f g H)).inclusion_totalMap))

theorem iota_original : iota P D₀ D₁ D₂ f g H =
    (VertexColumnComplex.diagonalComplexIso (QuadraticEncoding.composition P) 1 D₁).hom ≫
      (vertexComplex P).map ((Exactness.data s D₀ D₁ D₂ f g).in₁) ≫
      (vertexComplex P).map (InducedRectification.inclusion s D₀ D₁ D₂ f g H) := by
  dsimp only [iota]
  erw [← (vertexComplex P).map_comp (intoF1 P D₀ D₁ D₂ f g)
    (Exactness.i1 s D₀ D₁ D₂ f g H), intoF1_nested, Functor.map_comp]
  rfl
end LittleFinitistic.SecondVertex

end

end OAI
