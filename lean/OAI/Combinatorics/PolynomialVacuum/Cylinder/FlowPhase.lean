import OAI.Combinatorics.PolynomialVacuum.Cylinder.ActiveWeight

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ}

noncomputable def potentialHom (a : Face M) : (Edge M →₀ ℤ) →+ ℤ where
  toFun r:=potential r a
  map_zero' := by
    have h : column (0 : Edge M →₀ ℤ) (a.1+1) 2=0 := by ext; rfl
    simp [potential,h]
  map_add' r s := by
    have h : column (r+s) (a.1+1) 2=column r (a.1+1) 2+column s (a.1+1) 2 := by ext; rfl
    simp [potential,h,add_comm]

noncomputable def topHom : (Edge M →₀ ℤ) →+ ℤ where
  toFun r:= -columnTotal r 1
  map_zero' := by
    have h : column (0 : Edge M →₀ ℤ) 1 2=0 := by ext; rfl
    simp [columnTotal,h]
  map_add' r s := by
    have h : column (r+s) 1 2=column r 1 2+column s 1 2 := by ext; rfl
    simp [columnTotal,h,Finsupp.sum_add_index,add_comm]

theorem topHom_apply (r : Edge M →₀ ℤ) : topHom r=topValue r := by
  unfold topValue
  rw [potential_top_eq _ _ _ (by omega)]
  simp only [zero_add]; rfl

@[simp] theorem loopTurnPhase_add (r s : ℤ) : loopTurnPhase (r+s)=loopTurnPhase r*loopTurnPhase s := by
  unfold loopTurnPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
@[simp] theorem loopTurnPhase_neg (r : ℤ) : loopTurnPhase (-r)=(loopTurnPhase r)⁻¹ := by
  unfold loopTurnPhase
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem threeSeamFactor_add (κ : ℂ) (hκ : κ≠0) (r a b u r' a' b' u' : ℤ) :
    threeSeamFactor κ (r+r') (a+a') (b+b') (u+u')=
      threeSeamFactor κ r a b u*threeSeamFactor κ r' a' b' u' := by
  have hz : zeta≠0 := by simp [zeta_eq_I]
  simp only [threeSeamFactor,loopTurnPhase_add,neg_add,
    show a+a'-(u+u')=(a-u)+(a'-u') by ring,
    show b+b'-(a+a')=(b-a)+(b'-a') by ring,
    zpow_add₀ hz,zpow_add₀ (inv_ne_zero hz),zpow_add₀ (div_ne_zero hκ hz)]
  ring

theorem threeSeamFactor_neg (κ : ℂ) (r a b u : ℤ) :
    threeSeamFactor κ (-r) (-a) (-b) (-u)=(threeSeamFactor κ r a b u)⁻¹ := by
  simp only [threeSeamFactor,loopTurnPhase_neg,
    show -a - -u= -(a-u) by ring,show -b - -a= -(b-a) by ring,
    zpow_neg,mul_inv_rev]
  ring

noncomputable def currentPhase (r : Edge M →₀ ℤ) (a b : Face M) (κ : ℂ) : ℂ :=
  threeSeamFactor κ (flowTurn r) (potentialHom a r) (potentialHom b r) (topHom r)

@[simp] theorem currentPhase_polygon (P : Polygon M) (a b : Face M) (κ : ℂ) :
    currentPhase (polygonCurrent P) a b κ=polygonPhase P a b κ := by
  unfold currentPhase
  rw [flowTurn_polygon,topHom_apply]
  rfl

@[simp] theorem currentPhase_neg (r : Edge M →₀ ℤ) (a b : Face M) (κ : ℂ) :
    currentPhase (-r) a b κ=(currentPhase r a b κ)⁻¹ := by
  simp only [currentPhase,flowTurn_neg,map_neg,threeSeamFactor_neg]

theorem currentPhase_system (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    currentPhase (systemCurrent S o) a b κ=
      ∏ P∈S,currentPhase (signedPolygonCurrent P (o P)) a b κ := by
  simp only [currentPhase,systemCurrent_turn S o hS]
  simp only [systemCurrent,map_sum]
  induction S using Finset.induction_on with
  | empty => simp [threeSeamFactor]
  | @insert P S hP ih =>
    simp only [Finset.sum_insert hP,Finset.prod_insert hP]
    rw [threeSeamFactor_add κ hκ,ih (hS.mono (by simp))]

noncomputable def currentWeight (r : Edge M →₀ ℤ) (a b : Face M) (κ : ℂ) : ℂ :=
  xStar^(activeSites r).card*currentPhase r a b κ

theorem currentWeight_system (S : Finset (Polygon M)) (o : Polygon M → Bool)
    (hS : (S : Set (Polygon M)).Pairwise (fun P Q => Disjoint P.vertices Q.vertices))
    (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    currentWeight (systemCurrent S o) a b κ=
      ∏ P∈S,orientedPolygonWeight P a b κ (o P) := by
  rw [currentWeight,systemCurrent_length S o hS,currentPhase_system S o hS a b κ hκ,
    ← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P hP
  cases ho : o P <;> simp [signedPolygonCurrent,orientedPolygonWeight]

end PolynomialVacuumCylinder

end OAI
