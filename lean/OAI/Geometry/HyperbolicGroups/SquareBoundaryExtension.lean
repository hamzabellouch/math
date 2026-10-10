import Mathlib
import OAI.Geometry.HyperbolicGroups.ClosedCoverGluing
import OAI.Geometry.HyperbolicGroups.CubicalHomotopyExtension

namespace OAI

/-! Four actual edge homotopies extend a square homotopy, with their literal
boundary formulas retained. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.SquareBoundaryExtension
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X]

def endpoint (b : Bool) : I := if b then 1 else 0
def other (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

def face (q : Fin 2 × Bool) : Set (I × Cube.boundary (Fin 2)) :=
  {tx | tx.2.val q.1 = endpoint q.2}

lemma face_closed (q : Fin 2 × Bool) : IsClosed (face q) :=
  isClosed_eq ((continuous_apply q.1).comp (continuous_subtype_val.comp continuous_snd))
    continuous_const
lemma face_cover : ⋃ q, face q = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t,z⟩
  obtain ⟨i,hi|hi⟩ := z.property
  · exact Set.mem_iUnion.mpr ⟨(i,false),hi⟩
  · exact Set.mem_iUnion.mpr ⟨(i,true),hi⟩

structure Data where
  side : (Fin 2 × Bool) → C(I × I,X)
  corner : ∀ t b c, side (0,b) (t,endpoint c) = side (1,c) (t,endpoint b)

namespace Data
variable (D : Data (X := X))

def onFace (q : Fin 2 × Bool) : C(face q,X) where
  toFun tx := D.side q (tx.val.1,tx.val.2.val (other q.1))
  continuous_toFun := (D.side q).continuous.comp
    ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_apply (other q.1)).comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))))

lemma agree : ∀ i j x (hi : x ∈ face i) (hj : x ∈ face j),
    D.onFace i ⟨x,hi⟩ = D.onFace j ⟨x,hj⟩ := by
  rintro ⟨i,b⟩ ⟨j,c⟩ ⟨t,z⟩ hi hj
  change z.val i = endpoint b at hi
  change z.val j = endpoint c at hj
  change D.side (i,b) (t,z.val (other i)) = D.side (j,c) (t,z.val (other j))
  by_cases hij : i = j
  · subst j
    have hbc : b = c := by
      cases b <;> cases c <;> simp_all [endpoint]
    subst c
    rfl
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change D.side (0,b) (t,z.val 1) = D.side (1,c) (t,z.val 0)
      change z.val 0 = endpoint b at hi
      change z.val 1 = endpoint c at hj
      rw [hi,hj]
      exact D.corner t b c
    · change D.side (1,b) (t,z.val 0) = D.side (0,c) (t,z.val 1)
      change z.val 1 = endpoint b at hi
      change z.val 0 = endpoint c at hj
      rw [hi,hj]
      exact (D.corner t c b).symm
    · exact (hij rfl).elim

def boundary : C(I × Cube.boundary (Fin 2),X) :=
  ClosedCoverGluing.glue face D.onFace D.agree face_cover face_closed (locallyFinite_of_finite _)

lemma boundary_eq (q : Fin 2 × Bool) (t : I) (z : Cube.boundary (Fin 2))
    (hz : z.val q.1 = endpoint q.2) :
    D.boundary (t,z) = D.side q (t,z.val (other q.1)) :=
  ClosedCoverGluing.glue_eq _ _ _ _ _ _ q (t,z) hz

variable (f : C(Fin 2 → I,X))
  (hf : ∀ q (z : Fin 2 → I), z q.1 = endpoint q.2 →
    D.side q (0,z (other q.1)) = f z)

include hf in
lemma boundary_initial (z : Cube.boundary (Fin 2)) : D.boundary (0,z) = f z := by
  obtain ⟨i,hi|hi⟩ := z.property
  · rw [D.boundary_eq (i,false) 0 z hi]
    exact hf (i,false) z hi
  · rw [D.boundary_eq (i,true) 0 z hi]
    exact hf (i,true) z hi

/-- The complete square prism is extended, not merely its boundary class. -/
def extend : C(I × (Fin 2 → I),X) :=
  CubicalHomotopyExtension.extend f D.boundary (D.boundary_initial f hf)

lemma extend_initial (z : Fin 2 → I) : D.extend f hf (0,z) = f z :=
  CubicalHomotopyExtension.extend_bottom _ _ _ z
lemma extend_edge (q : Fin 2 × Bool) (t : I) (z : Fin 2 → I)
    (hz : z q.1 = endpoint q.2) :
    D.extend f hf (t,z) = D.side q (t,z (other q.1)) := by
  have hb : z ∈ Cube.boundary (Fin 2) := by
    refine ⟨q.1,?_⟩
    cases q.2 <;> simp_all [endpoint]
  exact (CubicalHomotopyExtension.extend_side _ _ _ t ⟨z,hb⟩).trans (D.boundary_eq q t ⟨z,hb⟩ hz)

end Data
end HyperbolicObstruction.SquareBoundaryExtension
end

end OAI
