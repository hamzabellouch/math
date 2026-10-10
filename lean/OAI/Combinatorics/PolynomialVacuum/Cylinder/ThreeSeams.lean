import OAI.Combinatorics.PolynomialVacuum.Cylinder.Turning
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Separation
import OAI.Combinatorics.PolynomialVacuum.Algebra.Scalars

namespace OAI

namespace PolynomialVacuumCylinder
open PolynomialVacuumAlgebra Classical
variable {M : ℕ}

 
noncomputable def loopTurnPhase (r : ℤ) : ℂ :=
  Complex.exp (Complex.I*((r : ℂ)*Real.pi/12))

@[simp] theorem loopTurnPhase_zero : loopTurnPhase 0=1 := by simp [loopTurnPhase]
@[simp] theorem loopTurnPhase_six : loopTurnPhase 6=Complex.I := by
  unfold loopTurnPhase
  convert Complex.exp_pi_div_two_mul_I using 1; push_cast; ring_nf
@[simp] theorem loopTurnPhase_neg_six : loopTurnPhase (-6)= -Complex.I := by
  have he : Complex.I*(((-6 : ℤ) : ℂ)*Real.pi/12)= -(Complex.I*((6 : ℤ)*Real.pi/12)) := by push_cast; ring
  rw [loopTurnPhase,he,Complex.exp_neg]
  change (loopTurnPhase 6)⁻¹= -Complex.I
  rw [loopTurnPhase_six,Complex.inv_I]

@[simp] theorem zeta_eq_I : zeta=Complex.I := by
  rw [zeta,t,← pow_mul]
  exact q_pow_four

 

noncomputable def threeSeamFactor (κ : ℂ) (r a b u : ℤ) : ℂ :=
  loopTurnPhase r * zeta^(-a) * (zeta⁻¹)^(a-u) * (κ/zeta)^(b-a)

lemma threeSeam_sum (κ : ℂ) (hκ : κ≠0) (ε r a b u : ℤ)
    (hε : ε=1 ∨ ε = -1) (ha : a=0 ∨ a=ε) (hb : b=0 ∨ b=ε)
    (hr : (u=0 ∧ r=6*ε) ∨ (u=ε ∧ r=0)) :
    threeSeamFactor κ r a b u + (threeSeamFactor κ r a b u)⁻¹ =
      if a=b then 0 else κ+κ⁻¹ := by
  rcases hε with rfl | rfl <;>
    rcases ha with rfl | rfl <;>
    rcases hb with rfl | rfl <;>
    rcases hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    norm_num [threeSeamFactor,zpow_neg,Complex.inv_I,div_eq_mul_inv,mul_inv_rev,hκ] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq]

 

def seamCrossing (p : Face M → ℤ) : List (Face M) → ℤ
  | [] => 0
  | [_] => 0
  | a::b::s => p a-p b+seamCrossing p (b::s)

theorem seamCrossing_telescope (p : Face M → ℤ) (a : Face M) (s : List (Face M)) :
    seamCrossing p (a::s)=p a-p ((a::s).getLast (by simp)) := by
  induction s generalizing a with
  | nil => simp [seamCrossing]
  | cons b s ih =>
    simp only [seamCrossing,ih,List.getLast_cons_cons]
    omega

 

theorem simple_cylinder_orientation_sum [NeZero M] (g : PlaneGerm) (w : List Bool)
    (hne : w≠[]) (hN : (traced (projectGerm M g) w).Nodup)
    (hc : terminalGerm (projectGerm M g) w=projectGerm M g)
    (a b : Face M) (κ : ℂ) (hκ : κ≠0) :
    let p := potential (wordFlow (projectGerm M g) w)
    let F := threeSeamFactor κ (PolynomialVacuumBridge.Corridor.turnUnits w) (p a) (p b)
      (topValue (wordFlow (projectGerm M g) w))
    F+F⁻¹=if Relation.ReflTransGen (DualAdjacent (tracedEdges (projectGerm M g) w)) a b
      then 0 else κ+κ⁻¹ := by
  dsimp only
  obtain ⟨ε,d,hε,hv,hD,hcases⟩ := cylinder_turn_and_winding g w hne hN hc
  rw [cylinder_separation_iff _ w hne hN hc]
  have hr : (topValue (wordFlow (projectGerm M g) w)=0 ∧ PolynomialVacuumBridge.Corridor.turnUnits w=6*ε) ∨
      (topValue (wordFlow (projectGerm M g) w)=ε ∧ PolynomialVacuumBridge.Corridor.turnUnits w=0) :=
    hcases.imp (fun h => ⟨h.2.1,h.2.2⟩) (fun h => ⟨h.2.1,h.2.2⟩)
  have hs := threeSeam_sum κ hκ ε _ _ _ _ hε (hv a) (hv b) hr
  by_cases hab : potential (wordFlow (projectGerm M g) w) a = potential (wordFlow (projectGerm M g) w) b
  · simp only [hab,ite_true] at hs ⊢
    exact hs
  · simp only [hab,ite_false] at hs ⊢
    exact hs

end PolynomialVacuumCylinder

end OAI
