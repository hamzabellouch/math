import OAI.Algebra.Finitistic.Rectification.VertexProjectives
import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding
import OAI.Algebra.Finitistic.Localization.TwoConeVerdier

namespace OAI
noncomputable section
open CategoryTheory Limits Category Pretriangulated
namespace LittleFinitistic.SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

open QuadraticEncoding
abbrev Proj := ProjectiveComplexes.Proj (B P)
abbrev K := ProjectiveComplexes.K (B P)

/-- The manuscript's specified vertex idempotent. -/
abbrev vertex (i : Fin 3) : B P := ThreeVertexAlgebra.vertex (QuadraticEncoding.composition P) i

theorem vertex_idem (i : Fin 3) : vertex P i * vertex P i = vertex P i :=
  (ThreeVertexAlgebra.directedSystem (QuadraticEncoding.composition P)).idem i

/-- E_i = e_i B as an actual finite projective right module. -/
def E (i : Fin 3) : Proj P := VertexProjectives.object (vertex P i) (vertex_idem P i)

theorem target01 (i : Fin (d+1)) : vertex P 1 * QuadraticEncoding.arrow01 P i =
    QuadraticEncoding.arrow01 P i := by
  ext <;> simp [vertex, ThreeVertexAlgebra.vertex, QuadraticEncoding.arrow01,
    ThreeVertexAlgebra.mul]

theorem target12 (i : Fin (d+1)) : vertex P 2 * QuadraticEncoding.arrow12 P i =
    QuadraticEncoding.arrow12 P i := by
  ext <;> simp [vertex, ThreeVertexAlgebra.vertex, QuadraticEncoding.arrow12,
    ThreeVertexAlgebra.mul]

/-- The actual right-module arrow maps, given by left multiplication. -/
def arrow01 (i : Fin (d+1)) : E P 0 ⟶ E P 1 :=
  VertexProjectives.arrow (vertex_idem P 0) (vertex_idem P 1)
    (QuadraticEncoding.arrow01 P i) (target01 P i)
def arrow12 (i : Fin (d+1)) : E P 1 ⟶ E P 2 :=
  VertexProjectives.arrow (vertex_idem P 1) (vertex_idem P 2)
    (QuadraticEncoding.arrow12 P i) (target12 P i)

/-- Regard a projective as a bounded complex concentrated in degree zero. -/
def stalk : Proj P ⥤ K P :=
  ObjectProperty.lift _
    (HomologicalComplex.single (Proj P) (.up ℤ) 0 ⋙ HomotopyCategory.quotient _ _)
    (fun _ => (BoundedHomotopy.bounded_quotient_obj_iff _ _).mpr
      ⟨0,0,inferInstance,inferInstance⟩)

def s : (stalk P).obj (E P 0) ⟶ (stalk P).obj (E P 1) := (stalk P).map (arrow01 P 0)
def s' : (stalk P).obj (E P 1) ⟶ (stalk P).obj (E P 2) := (stalk P).map (arrow12 P 0)

/-- The cone choices are made once, in K, before any evaluation module is chosen. -/
def cones : TwoConeVerdier.ConePair (K P) := by
  let H := distinguished_cocone_triangle (s P)
  let H' := distinguished_cocone_triangle (s' P)
  exact ⟨Triangle.mk (s P) H.choose_spec.choose H.choose_spec.choose_spec.choose,
    Triangle.mk (s' P) H'.choose_spec.choose H'.choose_spec.choose_spec.choose,
    H.choose_spec.choose_spec.choose_spec, H'.choose_spec.choose_spec.choose_spec⟩

@[simp] theorem cones_first : (cones P).first.mor₁ = s P := rfl
@[simp] theorem cones_second : (cones P).second.mor₁ = s' P := rfl

/-- Exactly the thick closure of Cone(s), Cone(s'). -/
abbrev S : ObjectProperty (K P) := (cones P).S
abbrev Sigma : MorphismProperty (K P) := (cones P).Sigma
/-- Section 3's actual Verdier quotient K/S. -/
abbrev Q := (cones P).Q
abbrev q : K P ⥤ Q P := (cones P).q

/-- The actual, proved fraction and localization hypotheses needed by DiagramLifting. -/
theorem fraction_calculus : (Sigma P).HasRightCalculusOfFractions := inferInstance
theorem localization : (q P).IsLocalization (Sigma P) := inferInstance
theorem triangulated : IsTriangulated (Q P) := inferInstance

instance s_inverted : IsIso ((q P).map (s P)) :=
  inferInstanceAs (IsIso ((cones P).q.map (cones P).first.mor₁))
instance s'_inverted : IsIso ((q P).map (s' P)) :=
  inferInstanceAs (IsIso ((cones P).q.map (cones P).second.mor₁))

theorem zero_fraction {X Y : K P} (f : X ⟶ Y) (hf : (q P).map f = 0) :
    ∃ (Z : K P) (v : Z ⟶ X), Sigma P v ∧ v ≫ f = 0 :=
  (cones P).zero_fraction f hf

end LittleFinitistic.SourceVerdier

end

end OAI
