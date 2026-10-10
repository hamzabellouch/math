import OAI.Geometry.HeilbronnTriangle.IntegralPlaneLattice
import OAI.Geometry.HeilbronnTriangle.IntegralPlaneReduction
import OAI.Geometry.HeilbronnTriangle.FiniteIndexPlane

namespace OAI


noncomputable section

namespace Problem355.EqualCoordinatePacking

open IntegralPlaneLattice

abbrev Vector := Fin 3 → ℤ

def embedding (x : Vector) (L : Submodule ℤ Vector) :
    integerPlaneIn x L →ₗ[ℤ] plane x :=
  (latticeIn x L).subtype.comp (kernelEquivIn x L).toLinearMap

theorem embedding_injective (x : Vector) (L : Submodule ℤ Vector) :
    Function.Injective (embedding x L) :=
  (Submodule.subtype_injective _).comp (kernelEquivIn x L).injective

@[simp] theorem embedding_coe (x : Vector) (L : Submodule ℤ Vector)
    (v : integerPlaneIn x L) :
    ((embedding x L v : plane x) : Ambient) = castVec v := rfl

def equalLattice (q : ℕ) [Fact q.Prime] (x : Vector)
    (L : Submodule ℤ Vector) (i j : Fin 3) : Submodule ℤ (plane x) :=
  ((PlaneFunctional.equalCoordinateSubgroup q (integerPlaneIn x L).toAddSubgroup i j).map
    (embedding x L).toAddMonoidHom).toIntSubmodule

theorem equalLattice_le (q : ℕ) [Fact q.Prime] (x : Vector)
    (L : Submodule ℤ Vector) (i j : Fin 3) :
    equalLattice q x L i j ≤ latticeIn x L := by
  rintro v ⟨w, hw, rfl⟩
  exact (kernelEquivIn x L w).property

theorem equalLattice_relIndex (q : ℕ) [Fact q.Prime]
    (x z : Vector) (hz : dotProduct x z = 1)
    (L : Submodule ℤ Vector) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hL : ∀ v : Vector, E • v ∈ L) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j) :
    (equalLattice q x L i j).toAddSubgroup.relIndex (latticeIn x L).toAddSubgroup = q := by
  have htop : (⊤ : AddSubgroup (integerPlaneIn x L)).map
      (embedding x L).toAddMonoidHom = (latticeIn x L).toAddSubgroup := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (kernelEquivIn x L w).property
    · intro hv
      refine ⟨(kernelEquivIn x L).symm ⟨v, hv⟩, trivial, ?_⟩
      exact congrArg (fun w : latticeIn x L => (w : plane x))
        ((kernelEquivIn x L).apply_symm_apply ⟨v, hv⟩)
  change ((PlaneFunctional.equalCoordinateSubgroup q
    (integerPlaneIn x L).toAddSubgroup i j).map (embedding x L).toAddMonoidHom).relIndex
      (latticeIn x L).toAddSubgroup = q
  rw [← htop, AddSubgroup.relIndex_map_map_of_injective _ _ (embedding_injective x L),
    AddSubgroup.relIndex_top_right]
  exact IntegralPlaneReduction.equalCoordinate_index q L x z hz E hE hL i j hij hspan

def row (q : ℕ) [Fact q.Prime] (x : Vector) (L : Submodule ℤ Vector)
    (i j : Fin 3) (v : integerPlaneIn x L)
    (hv : ((v : Vector) i : ZMod q) = ((v : Vector) j : ZMod q)) :
    equalLattice q x L i j :=
  ⟨embedding x L v, ⟨v,
    (PlaneFunctional.mem_equalCoordinateSubgroup q
      (integerPlaneIn x L).toAddSubgroup i j v).mpr hv, rfl⟩⟩

theorem matrices_card_le (q : ℕ) [Fact q.Prime]
    (x z : Vector) (hz : dotProduct x z = 1)
    (L : Submodule ℤ Vector) (E : ℤ) (hE : IsUnit (E : ZMod q))
    (hL : ∀ v : Vector, E • v ∈ L) (i j : Fin 3) (hij : i ≠ j)
    (hspan : ¬ ∃ a : ZMod q, (fun k => (x k : ZMod q)) =
      a • PlaneFunctional.coordinateDifference i j)
    (A : Finset (Fin 3 → Vector)) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ a ∈ A, ∀ k, a k ∈ integerPlaneIn x L)
    (hcoord : ∀ a ∈ A, ∀ k, (a k i : ZMod q) = (a k j : ZMod q))
    (hnorm : ∀ a ∈ A, ∀ k, ‖castVec (a k)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ k l : Fin 3,
      LinearIndependent ℝ ![castVec (a k), castVec (a l)]) :
    (A.card : ℝ) ≤
      (9 * Real.pi * R ^ 2 / ((q : ℝ) * ZLattice.covolume (latticeIn x L))) ^ 3 := by
  classical
  have hEne : E ≠ 0 := by
    intro he
    have hu := hE.ne_zero
    simp [he] at hu
  let : IsZLattice ℝ (latticeIn x L) := latticeIn_isZLattice x z hz L E hEne hL
  let T : {a // a ∈ A} → Fin 3 → equalLattice q x L i j := fun a k =>
    row q x L i j ⟨a.val k, hrow a.val a.property k⟩ (hcoord a.val a.property k)
  have hTinj : Function.Injective T := by
    intro a b hab
    apply Subtype.ext
    funext k t
    have he := congrArg
      (fun v : equalLattice q x L i j => ((v : plane x) : Ambient) t)
      (congrFun hab k)
    change (a.val k t : ℝ) = (b.val k t : ℝ) at he
    exact_mod_cast he
  have hcard : (A.attach.image T).card = A.card := by
    rw [Finset.card_image_of_injective _ hTinj, Finset.card_attach]
  have hbound := FiniteIndexPlane.spanning_triples_card_le
    (plane_finrank x z hz) (equalLattice q x L i j) (latticeIn x L)
    (equalLattice_le q x L i j) q (Fact.out : q.Prime).pos
    (equalLattice_relIndex q x z hz L E hE hL i j hij hspan)
    (A.attach.image T) R hR
    (by
      intro b hb k
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      exact hnorm a.val a.property k)
    (by
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨k, l, hkl⟩ := hpair a.val a.property
      refine ⟨k, l, LinearIndependent.of_comp (plane x).subtype ?_⟩
      convert hkl using 1
      ext t
      fin_cases t <;> rfl)
  rwa [hcard] at hbound

end Problem355.EqualCoordinatePacking

end

end OAI
