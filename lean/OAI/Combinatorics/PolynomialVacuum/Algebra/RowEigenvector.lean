import OAI.Combinatorics.PolynomialVacuum.Algebra.TraceClosing

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem homogeneousVector_depends (N : ℕ) : DependsBefore N (homogeneousVector N) := by
  intro s r h
  unfold homogeneousVector liftState liftPolyTensor
  congr 2
  funext j
  exact h j.val j.isLt

theorem trainDenominator_constant (c x : ℂ) (k N : ℕ) :
    trainDenominator c (fun _ => x) k N=exchangeDenominator c x^N := by
  induction N generalizing k with
  | zero => rfl
  | succ N ih => simp [trainDenominator,ih,pow_succ]

theorem front_trainDenominator (N : ℕ) (a : ℂ) :
    trainDenominator (T*a) (frontFirstData a) 1 N=exchangeDenominator (T*a) 1^N := by
  have hh : ∀ k, 1≤k → trainDenominator (T*a) (frontFirstData a) k N=
      exchangeDenominator (T*a) 1^N := by
    induction N with
    | zero => intros; rfl
    | succ N ih =>
      intro k hk
      simp [trainDenominator,frontFirstData,show k≠0 by omega,ih (k+1) (by omega),pow_succ]
  exact hh 1 le_rfl

 
theorem polynomialVacuum_tracedRow (N : ℕ) (a : ℂ) (hs : homogeneousFusion N a≠0)
    (hd : exchangeDenominator (T*a) a≠0) :
    tracedTrain N (T*a) (fun _ => 1) (homogeneousVector N)=
      exchangeDenominator (T*a) 1^N • homogeneousVector N := by
  funext s
  have he:=congrFun (polynomialVacuum_cupRow N a hs) (padCup N s)
  rw [cupRow_trace N a _ (homogeneousVector_depends N),front_trainDenominator] at he
  simp only [Pi.smul_apply,smul_eq_mul,cupLinear,LinearMap.coe_mk,AddHom.coe_mk,
    padCup_left,padCup_right,padCup_skip,cup,charge,add_zero,mul_zero,ite_true,zpow_zero,one_mul] at he
  apply mul_left_cancel₀ hd
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using he

private theorem four_ne_zero {x : ℂ} (h : x^4= -1) : x-1≠0 ∧ x+1≠0 := by
  constructor
  · intro hz
    have hx : x=1 := sub_eq_zero.mp hz
    rw [hx] at h
    norm_num at h
  · intro hz
    have hx : x= -1 := eq_neg_of_add_eq_zero_left hz
    rw [hx] at h
    norm_num at h

private theorem physical_auxiliary : T*(-zeta)=t := by
  dsimp [T,zeta,t]; vacuum_ring_finish

private theorem physical_fusion (N : ℕ) : homogeneousFusion N (-zeta)≠0 := by
  have hT : T^4= -1 := by dsimp [T,t]; vacuum_ring_finish
  have ha : -zeta≠0 := neg_ne_zero.mpr (pow_ne_zero _ t_ne_zero)
  have h1 : (t^5*(-zeta))^4= -1 := by dsimp [zeta,t]; vacuum_ring_finish
  have h2 : (1-t^6*(-zeta))=(2 : ℂ) := by dsimp [zeta,t]; vacuum_ring_finish
  apply mul_ne_zero (mul_ne_zero (by simpa [add_comm] using (four_ne_zero hT).2) ha)
  apply pow_ne_zero
  change (1-t^5*(-zeta))*(1-t^6*(-zeta))≠0
  rw [h2]
  exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (four_ne_zero h1).1))) (by norm_num)

private theorem physical_cup_denominator : exchangeDenominator (T*(-zeta)) (-zeta)≠0 := by
  have h1 : (t^2*T)^4= -1 := by dsimp [T,t]; vacuum_ring_finish
  have h2 : (T^2)^2= -1 := by dsimp [T,t]; vacuum_ring_finish
  have hn1 : t^2*T-1≠0 := (four_ne_zero h1).1
  have hn2 : T^2-1≠0 := by
    intro hz
    rw [sub_eq_zero.mp hz] at h2
    norm_num at h2
  have ha : -zeta≠0 := neg_ne_zero.mpr (pow_ne_zero _ t_ne_zero)
  have he : exchangeDenominator (T*(-zeta)) (-zeta)=(-zeta)^2*(t^2*T-1)*(T^2-1) := by
    unfold exchangeDenominator; ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hn1) hn2

theorem polynomialVacuum_honeycombRow (N : ℕ) :
    tracedTrain N t (fun _ => 1) (homogeneousVector N)=
      exchangeDenominator t 1^N • homogeneousVector N := by
  simpa only [physical_auxiliary] using
    polynomialVacuum_tracedRow N (-zeta) (physical_fusion N) physical_cup_denominator

end PolynomialVacuumAlgebra

end OAI
