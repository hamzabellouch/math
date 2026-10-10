import OAI.Combinatorics.PolynomialVacuum.Cylinder.FlowPhase

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ}

abbrev BoundedPolygon (E : Finset (Edge M)) := {P : Polygon M // P.val⊆E}
instance boundedPolygon_finite (E : Finset (Edge M)) : Finite (BoundedPolygon E) := by
  let f : BoundedPolygon E → {s // s∈E.powerset}:=fun P => ⟨P.val.val,Finset.mem_powerset.mpr P.property⟩
  apply Finite.of_injective f
  intro P Q h
  have hh := congrArg (fun x : {s // s∈E.powerset} => x.val) h
  exact Subtype.ext (Subtype.ext hh)
noncomputable instance (E : Finset (Edge M)) : Fintype (BoundedPolygon E) := Fintype.ofFinite _
noncomputable def boundedPolygons (E : Finset (Edge M)) : Finset (Polygon M) :=
  Finset.univ.image (fun P : BoundedPolygon E => P.val)
@[simp] theorem mem_boundedPolygons (E : Finset (Edge M)) (P : Polygon M) :
    P∈boundedPolygons E ↔ P.val⊆E := by
  simp only [boundedPolygons,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨Q,rfl⟩; exact Q.property
  · intro h; exact ⟨⟨P,h⟩,rfl⟩

abbrev BoundedSystem (E : Finset (Edge M)) :=
  {S : DisjointSystem M // ∀P∈S.val,P.val⊆E}
instance boundedSystem_finite (E : Finset (Edge M)) : Finite (BoundedSystem E) := by
  let f : BoundedSystem E → {s // s∈(boundedPolygons E).powerset}:=fun S =>
    ⟨S.val.val,Finset.mem_powerset.mpr (fun P hP => (mem_boundedPolygons E P).mpr (S.property P hP))⟩
  apply Finite.of_injective f
  intro S T h
  have hh := congrArg (fun x : {s // s∈(boundedPolygons E).powerset} => x.val) h
  exact Subtype.ext (Subtype.ext hh)
noncomputable instance (E : Finset (Edge M)) : Fintype (BoundedSystem E) := Fintype.ofFinite _

abbrev BoundedOrientation (E : Finset (Edge M)) :=
  {A : OrientedSystem M // ∀P∈A.1.val,P.val⊆E}
abbrev BoundedFlow (E : Finset (Edge M)) := {r : LegalFlow M // r.val.support⊆E}

noncomputable def boundedOrientationSigma (E : Finset (Edge M)) :
    BoundedOrientation E ≃ ((S : BoundedSystem E) × ({P // P∈S.val.val} → Bool)) where
  toFun A:=⟨⟨A.val.1,A.property⟩,A.val.2⟩
  invFun A:=⟨⟨A.1.val,A.2⟩,A.1.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

noncomputable instance (E : Finset (Edge M)) : Fintype (BoundedOrientation E) :=
  Fintype.ofEquiv _ (boundedOrientationSigma E).symm

noncomputable def boundedOrientationEquiv (E : Finset (Edge M)) :
    BoundedOrientation E ≃ BoundedFlow E :=
  orientedSystemEquiv.subtypeEquiv (by
    intro A
    change (∀P∈A.1.val,P.val⊆E) ↔ (systemCurrent A.1.val (extendedOrientation A.1 A.2)).support⊆E
    rw [systemCurrent_support _ _ A.1.property]
    exact Finset.biUnion_subset.symm)
noncomputable instance (E : Finset (Edge M)) : Fintype (BoundedFlow E) :=
  Fintype.ofEquiv _ (boundedOrientationEquiv E)

 

theorem finite_current_partition [NeZero M] (E : Finset (Edge M))
    (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    (∑ r : BoundedFlow E,currentWeight r.val.val a b κ)=
    ∑ S : BoundedSystem E,if ∀P∈S.val.val,Separates P a b then
      (κ+κ⁻¹)^S.val.val.card*xStar^(∑P∈S.val.val,P.vertices.card) else 0 := by
  rw [← (boundedOrientationEquiv E).sum_comp]
  rw [← (boundedOrientationSigma E).symm.sum_comp]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro S _
  change (∑ o : {P // P∈S.val.val} → Bool,
    currentWeight (systemCurrent S.val.val (extendedOrientation S.val o)) a b κ)=_
  simp_rw [currentWeight_system _ _ S.val.property a b κ hκ]
  have he (o : {P // P∈S.val.val} → Bool) :
      (∏P∈S.val.val,orientedPolygonWeight P a b κ (extendedOrientation S.val o P))=
      ∏P : {P // P∈S.val.val},orientedPolygonWeight P.val a b κ (o P) := by
    rw [← Finset.prod_attach S.val.val (fun P => orientedPolygonWeight P a b κ (extendedOrientation S.val o P))]
    apply Finset.prod_congr rfl
    intro P _
    simp [extendedOrientation,P.property]
  simp_rw [he]
  exact polygon_system_orientation_sum S.val.val a b κ hκ

end PolynomialVacuumCylinder

end OAI
