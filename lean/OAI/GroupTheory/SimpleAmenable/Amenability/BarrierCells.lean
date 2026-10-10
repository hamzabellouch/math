import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteArrangementGerms
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FiniteSlotRefinement

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierCells
open Classical Set

noncomputable def arrangementAtom {ι : Type*} [Fintype ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (σ : ι → Bool) : polygonAlgebra a :=
  Finset.univ.inf (fun i => if σ i then ⟨halfPlane a (j i) (c i),halfPlane_mem _ _ _⟩
    else (⟨halfPlane a (j i) (c i),halfPlane_mem _ _ _⟩ : polygonAlgebra a)ᶜ)

theorem mem_arrangementAtom {ι : Type*} [Fintype ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (σ : ι → Bool) (p : GenericSquare a) :
    p∈(arrangementAtom a j c σ).val ↔ p.val∈strictLineCell a j (ordinary ∘ c) σ := by
  rw [arrangementAtom,polygon_mem_finset_inf]
  simp only [Finset.mem_univ,true_implies,strictLineCell,Set.mem_ofPred_eq,Function.comp_apply]
  apply forall_congr'
  intro i
  cases σ i
  · change (¬cutForm a (j i) p.val<ordinary (c i)) ↔ ordinary (c i)<cutForm a (j i) p.val
    exact ⟨fun h => lt_of_le_of_ne (le_of_not_gt h) (p.property.2.2 (j i) (c i)).symm,
      fun h => not_lt.mpr h.le⟩
  · rfl

noncomputable def arrangementPattern {ι : Type*} (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (p : GenericSquare a) : ι → Bool :=
  fun i => decide (cutForm a (j i) p.val<ordinary (c i))

theorem mem_arrangementPattern {ι : Type*} [Fintype ι] (a : ℕ)
    (j : ι → Fin 4) (c : ι → CutRing) (p : GenericSquare a) :
    p∈(arrangementAtom a j c (arrangementPattern a j c p)).val := by
  rw [mem_arrangementAtom]
  intro i
  by_cases h : cutForm a (j i) p.val<ordinary (c i)
  · simp [arrangementPattern,h]
  · simpa [arrangementPattern,h] using
      lt_of_le_of_ne (le_of_not_gt h) (p.property.2.2 (j i) (c i)).symm

theorem strictLineCell_convex {ι : Type*} (a : ℕ)
    (j : ι → Fin 4) (c : ι → ℝ) (σ : ι → Bool) :
    Convex ℝ (strictLineCell a j c σ) := by
  have hlin (i : ι) : IsLinearMap ℝ (cutForm a (j i)) :=
    ⟨cutForm_add a (j i),fun t p => cutForm_smul a (j i) t p⟩
  simp only [strictLineCell,Set.ofPred_forall]
  apply convex_iInter
  intro i
  cases σ i
  · exact convex_halfSpace_gt (hlin i) (c i)
  · exact convex_halfSpace_lt (hlin i) (c i)

def squareInterior : Set (ℝ×ℝ) := Ioo 0 1 ×ˢ Ioo 0 1

theorem generic_mem_squareInterior {a : ℕ} (p : GenericSquare a) : p.val∈squareInterior :=
  ⟨⟨(generic_coordinates_pos p).1,p.property.1.2⟩,
    ⟨(generic_coordinates_pos p).2,p.property.2.1.2⟩⟩

def barrierRegion (B : Set (ℝ×ℝ)) : Set (ℝ×ℝ) := squareInterior \ B

def SupportedBarriers {ι : Type*} (a : ℕ) (j : ι → Fin 4) (c : ι → CutRing)
    (B : Set (ℝ×ℝ)) : Prop :=
  ∀p∈B,∃i,cutForm a (j i) p=ordinary (c i)

theorem generic_mem_barrierRegion {ι : Type*} {a : ℕ} {j : ι → Fin 4}
    {c : ι → CutRing} {B : Set (ℝ×ℝ)} (hB : SupportedBarriers a j c B)
    (p : GenericSquare a) : p.val∈barrierRegion B := by
  refine ⟨generic_mem_squareInterior p,?_⟩
  intro hp
  obtain ⟨i,hi⟩ := hB p.val hp
  exact p.property.2.2 (j i) (c i) hi

theorem arrangementAtom_same_component {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (σ : ι → Bool) (p q : GenericSquare a)
    (hp : p∈(arrangementAtom a j c σ).val) (hq : q∈(arrangementAtom a j c σ).val) :
    q.val∈connectedComponentIn (barrierRegion B) p.val := by
  let C := squareInterior ∩ strictLineCell a j (ordinary ∘ c) σ
  have hC : Convex ℝ C := ((convex_Ioo (0:ℝ) 1).prod (convex_Ioo (0:ℝ) 1)).inter
    (strictLineCell_convex a j (ordinary ∘ c) σ)
  have hpC : p.val∈C := ⟨generic_mem_squareInterior p,(mem_arrangementAtom _ _ _ _ _).mp hp⟩
  have hqC : q.val∈C := ⟨generic_mem_squareInterior q,(mem_arrangementAtom _ _ _ _ _).mp hq⟩
  have hCB : C⊆barrierRegion B := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxB
    obtain ⟨i,hi⟩ := hB x hxB
    have hc := hx.2 i
    cases hσ : σ i <;> simp only [hσ,Bool.false_eq_true,ite_false,ite_true,Function.comp_apply] at hc
    · exact (ne_of_gt hc) hi
    · exact (ne_of_lt hc) hi
  exact hC.isPreconnected.subset_connectedComponentIn hpC hCB hqC

noncomputable def barrierComponentCell {a : ℕ} (B : Set (ℝ×ℝ)) (x : ℝ×ℝ) :
    Set (GenericSquare a) := {p | p.val∈connectedComponentIn (barrierRegion B) x}

theorem barrierComponentCell_polygon {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (x : ℝ×ℝ) :
    barrierComponentCell (a:=a) B x∈polygonAlgebra a := by
  let T := (Finset.univ : Finset (ι → Bool)).filter (fun σ => ∃p : GenericSquare a,
    p∈(arrangementAtom a j c σ).val ∧ p∈barrierComponentCell B x)
  let P : polygonAlgebra a := T.sup (arrangementAtom a j c)
  have hmem (p : GenericSquare a) : p∈P.val ↔ ∃σ∈T,p∈(arrangementAtom a j c σ).val := by
    dsimp [P]
    induction T using Finset.induction_on with
    | empty => simp
    | @insert σ T hσ ih =>
      rw [Finset.sup_insert]
      change (p∈(arrangementAtom a j c σ).val ∨ p∈(T.sup (arrangementAtom a j c)).val) ↔ _
      rw [ih]
      simp only [Finset.mem_insert,exists_eq_or_imp]
  have he : P.val=barrierComponentCell B x := by
    ext p
    rw [hmem]
    constructor
    · rintro ⟨σ,hσ,hp⟩
      obtain ⟨q,hq,hqx⟩ := (Finset.mem_filter.mp hσ).2
      have hqp := arrangementAtom_same_component hB σ q p hq hp
      change p.val∈connectedComponentIn (barrierRegion B) x
      rw [connectedComponentIn_eq hqx]
      exact hqp
    · intro hp
      refine ⟨arrangementPattern a j c p,?_,mem_arrangementPattern a j c p⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,mem_arrangementPattern a j c p,hp⟩
  exact he ▸ P.property

end BarrierCells

section BarrierPartitions
open Classical Set

structure FinitePolygonPartition (a : ℕ) where
  cells : Finset (polygonAlgebra a)
  nonempty : ∀C∈cells,C.val.Nonempty
  cover : ∀p : GenericSquare a,∃! C,C∈cells ∧ p∈C.val

noncomputable def barrierPolygonAt {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (p : GenericSquare a) : polygonAlgebra a :=
  ⟨barrierComponentCell B p.val,barrierComponentCell_polygon hB p.val⟩

theorem barrierPolygonAt_eq_of_pattern {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) {p q : GenericSquare a}
    (h : arrangementPattern a j c p=arrangementPattern a j c q) :
    barrierPolygonAt hB p=barrierPolygonAt hB q := by
  have hp := mem_arrangementPattern a j c p
  rw [h] at hp
  have hq := mem_arrangementPattern a j c q
  have hh := connectedComponentIn_eq (arrangementAtom_same_component hB _ p q hp hq)
  apply Subtype.ext
  change {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) p.val}=
    {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) q.val}
  rw [hh]

theorem barrierPolygonAt_finite_range {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) : (Set.range (barrierPolygonAt hB)).Finite := by
  let f (σ : ι → Bool) : polygonAlgebra a :=
    if h : ∃p : GenericSquare a,arrangementPattern a j c p=σ then
      barrierPolygonAt hB h.choose else ⊥
  apply (Set.finite_range f).subset
  rintro C ⟨p,rfl⟩
  refine ⟨arrangementPattern a j c p,?_⟩
  have h : ∃q : GenericSquare a,arrangementPattern a j c q=arrangementPattern a j c p := ⟨p,rfl⟩
  simp only [f,dite_eq_left h]
  exact barrierPolygonAt_eq_of_pattern hB h.choose_spec

noncomputable def finiteBarrierPartition {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) : FinitePolygonPartition a where
  cells := (barrierPolygonAt_finite_range hB).toFinset
  nonempty := by
    intro C hC
    obtain ⟨p,rfl⟩ := (Set.Finite.mem_toFinset _).mp hC
    exact ⟨p,mem_connectedComponentIn (generic_mem_barrierRegion hB p)⟩
  cover := by
    intro p
    refine ⟨barrierPolygonAt hB p,⟨?_,?_⟩,?_⟩
    · exact (Set.Finite.mem_toFinset _).mpr ⟨p,rfl⟩
    · exact mem_connectedComponentIn (generic_mem_barrierRegion hB p)
    · intro C hC
      obtain ⟨q,rfl⟩ := (Set.Finite.mem_toFinset _).mp hC.1
      apply Subtype.ext
      change {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) q.val}=
        {r : GenericSquare a | r.val∈connectedComponentIn (barrierRegion B) p.val}
      rw [connectedComponentIn_eq hC.2]

theorem mem_finiteBarrierPartition {ι : Type*} [Fintype ι] {a : ℕ}
    {j : ι → Fin 4} {c : ι → CutRing} {B : Set (ℝ×ℝ)}
    (hB : SupportedBarriers a j c B) (C : polygonAlgebra a) :
    C∈(finiteBarrierPartition hB).cells ↔ ∃p : GenericSquare a,
      C.val=barrierComponentCell B p.val := by
  change C∈(barrierPolygonAt_finite_range hB).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨p,rfl⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,Subtype.ext hp.symm⟩

end BarrierPartitions

end SimpleAmenable
end
end

end OAI
