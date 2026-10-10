import OAI.Combinatorics.PolynomialVacuum.Algebra.ScalingTensors
import OAI.Combinatorics.PolynomialVacuum.Algebra.FullCyclicity

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem scalingDiscrepancy_cup {n d : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (hh : ∀ s, (ψ s).IsHomogeneous d) (i : ℕ) (hi : i≤n)
    (X : ℕ → ℂ) (hX : X (i+1)=T*X i) :
    evalNatPolyTensor (scalingDiscrepancy Ψ (2*n+1+d)) X=0 := by
  have hs : (2:ℂ)*X (i+1)=T*(2*X i) := by rw [hX]; ring
  rw [eval_scalingDiscrepancy,hc i hi _ hs,hc i hi _ hX,naturalFusion_scale]
  funext s
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,cupLinear]
  change (2:ℂ)^(2*n+1)*naturalFusion n i X*(cup (s i,s (i+1))*liftState ψ (fun j => 2*skipTwo i X j) (skipTwo i s)) -
    (2:ℂ)^(2*n+1+d)*(naturalFusion n i X*(cup (s i,s (i+1))*liftState ψ (skipTwo i X) (skipTwo i s)))=0
  rw [liftState_homogeneous_scale ψ hh,pow_add]
  ring

theorem scalingDiscrepancy_degree {N d b : ℕ} (Ψ : State N) (s : ℕ → Spin) (j : Fin N)
    (h : (Ψ (fun a => s a.val)).degreeOf j≤b) :
    (scalingDiscrepancy Ψ d s).degreeOf j.val≤b := by
  have hd : (coordinatePolynomial Ψ s).degreeOf j.val≤b := by rw [coordinatePolynomial_degree]; exact h
  exact (degreeOf_sub_le _ _ _).trans (max_le ((degreeOf_scalePolynomial_le _ _ _).trans hd) (dconst_mul _ hd))

theorem scalingDiscrepancy_minusZero {N d : ℕ} (Ψ : State N) (hz : MinusZero Ψ)
    (s : ℕ → Spin) (j : Fin N) (hs : s j.val=Spin.minus) :
    killSite j.val (scalingDiscrepancy Ψ d s)=0 := by
  have h : killSite j.val (coordinatePolynomial Ψ s)=0 := by
    rw [coordinatePolynomial,killSite_rename_injective _ Fin.val_injective,hz _ _ hs,map_zero]
  simp only [scalingDiscrepancy,map_sub,map_mul,killSite_C,killSite_scalePolynomial,h,map_zero,mul_zero,sub_zero]

theorem homogeneous_of_scalingDiscrepancy {N d : ℕ} (Ψ : State N)
    (h : ∀ s, scalingDiscrepancy Ψ d s=0) (s : Fin N → Spin) :
    (Ψ s).IsHomogeneous d := by
  apply homogeneous_of_scale_two
  apply MvPolynomial.funext
  intro X
  have he := congrArg (eval (extendFinite 0 X)) (h (extendFinite Spin.zero s))
  simp only [scalingDiscrepancy,map_sub,map_zero,eval_scalePolynomial,map_mul,eval_C,
    eval_coordinatePolynomial,liftState,liftPolyTensor,extendFinite_fin] at he
  simpa only [eval_scalePolynomial,map_mul,eval_C] using sub_eq_zero.mp he

theorem homogDegree_step (n : ℕ) : (n+2).choose 2=2*n+1+n.choose 2 := by
  have h1 := Nat.choose_succ_succ n 1
  have h2 := Nat.choose_succ_succ (n+1) 1
  simp only [Nat.choose_one_right,Nat.succ_eq_add_one,Nat.reduceAdd,Nat.add_assoc] at h1 h2
  omega

theorem homogeneity_of_cups {n : ℕ} (Ψ : State (n+4)) (ψ : State (n+2))
    (hex : LowerExchange (liftState Ψ) (n+4))
    (hc : ∀ i≤n+2, CupAt (liftState Ψ) (liftState ψ) (n+2) i)
    (hh : ∀ s, (ψ s).IsHomogeneous ((n+2).choose 2))
    (hd : ∀ s i, (Ψ s).degreeOf i≤n+3)
    (hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i≤n+2)
    (hz : MinusZero Ψ) : ∀ s, (Ψ s).IsHomogeneous ((n+4).choose 2) := by
  apply homogeneous_of_scalingDiscrepancy
  apply cup_vanishing_rigidity (m:=n+3) (by omega)
  · exact scalingDiscrepancy_exchange Ψ (fun j hj => hex j (by omega))
  · intro i hi X hX
    have heq : (n+4).choose 2=2*(n+2)+1+(n+2).choose 2 := homogDegree_step (n+2)
    rw [heq]
    exact scalingDiscrepancy_cup Ψ ψ hc hh i (by omega) X hX
  · intro s j hj
    exact scalingDiscrepancy_degree Ψ s ⟨j,by omega⟩ (hd _ _)
  · intro s j hj hs
    have he := scalingDiscrepancy_degree (d:=(n+4).choose 2) Ψ s ⟨j,by omega⟩ (hp _ ⟨j,by omega⟩ hs)
    exact he.trans (by omega)
  · intro s j hj hs
    exact scalingDiscrepancy_minusZero Ψ hz s ⟨j,by omega⟩ hs

end PolynomialVacuumAlgebra

end OAI
