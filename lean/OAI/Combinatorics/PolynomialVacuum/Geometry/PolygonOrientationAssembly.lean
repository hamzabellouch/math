import OAI.Combinatorics.PolynomialVacuum.Cylinder.ThreeSeams

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ}

noncomputable def liftVertex (v : Vertex M) : PlaneVertex :=
  match v with
  | .up i j => .up i.cast j
  | .down i j => .down i.cast j
noncomputable def liftGerm (g : Germ M) : PlaneGerm := (liftVertex g.1,g.2)
@[simp] theorem project_liftVertex (v : Vertex M) : projectVertex M (liftVertex v)=v := by
  cases v <;> simp [liftVertex,projectVertex]
@[simp] theorem project_liftGerm (g : Germ M) : projectGerm M (liftGerm g)=g := by
  simp [liftGerm,projectGerm]

noncomputable def polygonGerm (P : Polygon M) : Germ M := P.property.choose
noncomputable def polygonWord (P : Polygon M) : List Bool := P.property.choose_spec.choose

theorem polygon_witness (P : Polygon M) : polygonWord P≠[] ∧
    (traced (polygonGerm P) (polygonWord P)).Nodup ∧
    terminalGerm (polygonGerm P) (polygonWord P)=polygonGerm P ∧
    tracedEdges (polygonGerm P) (polygonWord P)=P.val := P.property.choose_spec.choose_spec

 
noncomputable def polygonPhase (P : Polygon M) (a b : Face M) (κ : ℂ) : ℂ :=
  let p := potential (wordFlow (polygonGerm P) (polygonWord P))
  threeSeamFactor κ (PolynomialVacuumBridge.Corridor.turnUnits (polygonWord P)) (p a) (p b)
    (topValue (wordFlow (polygonGerm P) (polygonWord P)))

theorem polygon_phase_sum [NeZero M] (P : Polygon M) (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    polygonPhase P a b κ+(polygonPhase P a b κ)⁻¹=if Separates P a b then κ+κ⁻¹ else 0 := by
  obtain ⟨hne,hN,hc,he⟩ := polygon_witness P
  have hs := simple_cylinder_orientation_sum (liftGerm (polygonGerm P)) (polygonWord P)
    hne (by simpa using hN) (by simpa using hc) a b κ hκ
  simp only [project_liftGerm,he] at hs
  unfold polygonPhase
  rw [hs]
  unfold Separates
  split_ifs <;> simp_all

noncomputable def orientedPolygonWeight (P : Polygon M) (a b : Face M) (κ : ℂ) (o : Bool) : ℂ :=
  xStar^P.vertices.card * if o then polygonPhase P a b κ else (polygonPhase P a b κ)⁻¹

theorem orientedPolygonWeight_sum [NeZero M] (P : Polygon M) (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    (∑ o : Bool,orientedPolygonWeight P a b κ o)=
      if Separates P a b then xStar^P.vertices.card*(κ+κ⁻¹) else 0 := by
  simp only [Fintype.sum_bool,orientedPolygonWeight,Bool.false_eq_true,ite_false,ite_true]
  rw [← mul_add,polygon_phase_sum P a b κ hκ]
  split_ifs <;> simp

 

theorem polygon_system_orientation_sum [NeZero M] (S : Finset (Polygon M))
    (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    (∑ o : {P // P∈S} → Bool, ∏ P : {P // P∈S},orientedPolygonWeight P.val a b κ (o P)) =
      if ∀ P∈S,Separates P a b then
        (κ+κ⁻¹)^S.card*xStar^(∑ P∈S,P.vertices.card) else 0 := by
  rw [← Fintype.prod_sum]
  simp_rw [orientedPolygonWeight_sum _ _ _ _ hκ]
  rw [Finset.prod_ite_zero]
  have he : (∀ P∈(Finset.univ : Finset {P // P∈S}),Separates P.val a b) =
      (∀ P∈S,Separates P a b) := by
    apply propext
    constructor
    · intro h P hP; exact h ⟨P,hP⟩ (Finset.mem_univ _)
    · intro h P _; exact h P.val P.property
  simp only [he]
  split_ifs with h
  · rw [Finset.prod_mul_distrib]
    have hp : (∏ P : {P // P∈S},xStar^P.val.vertices.card)=xStar^(∑ P∈S,P.vertices.card) := by
      change (∏ P∈S.attach,xStar^P.val.vertices.card)=_
      rw [Finset.prod_attach S (fun P : Polygon M => xStar^P.vertices.card),Finset.prod_pow_eq_pow_sum]
    rw [hp]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
    ring
  · rfl

end PolynomialVacuumCylinder

end OAI
