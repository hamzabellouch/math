import OAI.Combinatorics.PolynomialVacuum.Cylinder.SystemTranslation
import OAI.Combinatorics.PolynomialVacuum.Pairing.FiniteGluing
import OAI.Combinatorics.PolynomialVacuum.Pairing.MarkedRows

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra

noncomputable def finiteSeparatorSystems (n : ℕ) (E : Finset (Edge (2*n))) : Finset (System n) :=
  (boundedPolygons E).powerset.subtype (AllowedSystem n)

@[simp] theorem mem_finiteSeparatorSystems (n : ℕ) (E : Finset (Edge (2*n))) (S : System n) :
    S∈finiteSeparatorSystems n E ↔ ∀P∈S.val,P.val⊆E := by
  simp only [finiteSeparatorSystems,Finset.mem_subtype,Finset.mem_powerset]
  exact ⟨fun h P hP=>(mem_boundedPolygons E P).mp (h hP),
    fun h P hP=>(mem_boundedPolygons E P).mpr (h P hP)⟩

theorem bounded_separator_sum (n : ℕ) (E : Finset (Edge (2*n))) (η : ℂ) :
    (∑S : BoundedSystem E,if ∀P∈S.val.val,Separates P (0,0) ((n : ZMod (2*n)),0) then
      η^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0)=
      ∑S∈finiteSeparatorSystems n E,systemWeight η S := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun S hS=>(⟨S.val.val,(Finset.mem_filter.mp hS).2,S.val.property⟩ : System n))
  · intro S hS
    exact (mem_finiteSeparatorSystems _ _ _).mpr S.property
  · intro S hS T hT hST
    exact Subtype.ext (Subtype.ext (congrArg (fun S : System n=>S.val) hST))
  · intro S hS
    refine ⟨⟨⟨S.val,S.property.2⟩,(mem_finiteSeparatorSystems _ _ _).mp hS⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.property.1⟩
    · rfl
  · intro S hS
    rfl

theorem neg_half_circumference (n : ℕ) : -(n : ZMod (2*n))=(n : ZMod (2*n)) := by
  apply neg_eq_iff_add_eq_zero.mpr
  rw [← Nat.cast_add]
  have h : n+n=2*n := by omega
  rw [h,ZMod.natCast_self]

 theorem centered_partition_identity (n : ℕ) [NeZero (2*n)] (hn : 1≤n) (H : ℕ) (κ : ℂ) (hκ : κ≠0) :
    finitePhysicalContraction (2*n-1) n H κ=
      ∑S∈finiteSeparatorSystems n (centeredEdges (2*n) H),systemWeight (κ+κ⁻¹) S := by
  have hw : 2*n-1+1=2*n := by omega
  have hg:=physical_finite_gluing (2*n-1) (H+(H+1)) H n (by omega) (by omega) κ hκ
  have hg' := (finitePhysicalContraction_rows (2*n-1) n H κ).trans hg
  let Z (M : ℕ) (hM : 0<M) : ℂ := by
    haveI : NeZero M:=⟨by omega⟩
    exact ∑S : BoundedSystem (internalEdges (bandSites M (H+(H+1)))),
      if ∀P∈S.val.val,Separates P (0,H) (-(n : ZMod M),H) then
        (κ+κ⁻¹)^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0
  have hz : Z (2*n-1+1) (by omega)=Z (2*n) (by omega) := by
    congr 1; omega
  change finitePhysicalContraction (2*n-1) n H κ=Z (2*n-1+1) (by omega) at hg'
  rw [hz] at hg'
  change finitePhysicalContraction (2*n-1) n H κ=
    ∑S : BoundedSystem (internalEdges (bandSites (2*n) (H+(H+1)))),
      if ∀P∈S.val.val,Separates P (0,H) (-(n : ZMod (2*n)),H) then
        (κ+κ⁻¹)^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0 at hg'
  rw [hg',← bounded_separator_sum]
  let f : BoundedSystem (centeredEdges (2*n) H) → ℂ := fun S =>
    if ∀P∈S.val.val,Separates P (0,0) ((n : ZMod (2*n)),0) then
      (κ+κ⁻¹)^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0
  have he := (verticalBoundedEquiv (-(H : ℤ)) (internalEdges (bandSites (2*n) (H+(H+1))))).sum_comp f
  change _ = ∑S : BoundedSystem (centeredEdges (2*n) H),f S
  refine Eq.trans ?_ he
  apply Finset.sum_congr rfl
  intro S _
  change (if ∀P∈S.val.val,Separates P (0,H) (-(n : ZMod (2*n)),H) then
    (κ+κ⁻¹)^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0)=
    if ∀P∈(verticalSystem (-(H : ℤ)) S.val).val,Separates P (0,0) ((n : ZMod (2*n)),0) then
      (κ+κ⁻¹)^(verticalSystem (-(H : ℤ)) S.val).val.card*
        xStar^(∑P∈(verticalSystem (-(H : ℤ)) S.val).val,P.vertices.card) else 0
  have hs:=verticalSystem_separates (-(H : ℤ)) S.val (0,H) (-(n : ZMod (2*n)),H)
  simp only [verticalFace,add_neg_cancel,neg_half_circumference] at hs
  simp only [hs,verticalSystem_card,verticalSystem_length,neg_half_circumference]

 theorem finiteSeparatorSystems_mono {n : ℕ} {E F : Finset (Edge (2*n))} (hEF : E⊆F) :
    finiteSeparatorSystems n E⊆finiteSeparatorSystems n F := by
  intro S hS
  rw [mem_finiteSeparatorSystems] at hS ⊢
  exact fun P hP=>(hS P hP).trans hEF

 theorem eventually_mem_finiteSeparatorSystems (n : ℕ) [NeZero (2*n)] (S : System n) :
    ∀ᶠ H : ℕ in Filter.atTop,S∈finiteSeparatorSystems n (centeredEdges (2*n) H) := by
  simp only [mem_finiteSeparatorSystems]
  rw [Filter.eventually_all_finset]
  intro P hP
  change ∀ᶠ H : ℕ in Filter.atTop,∀e∈P.val,e∈centeredEdges (2*n) H
  rw [Filter.eventually_all_finset]
  exact fun e _=>eventually_mem_centeredEdges e

end PolynomialVacuumCylinder

end OAI
