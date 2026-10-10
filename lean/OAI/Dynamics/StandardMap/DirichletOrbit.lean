import OAI.Dynamics.StandardMap.BridgeNonlinear

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma green_convolution_jump (v : ℕ → ℝ) (n l : ℕ) (hl : l < n) (F : Fin n → ℝ) :
    v (l+1)*(∑ j : Fin n, greenKernel v (n+1) (l+1) (j+1)*F j)-
      (∑ j : Fin n, greenKernel v (n+1) l (j+1)*F j)-
      (∑ j : Fin n, greenKernel v (n+1) (l+2) (j+1)*F j)=F ⟨l,hl⟩ := by
  classical
  rw [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin n, (if l+1=(j:ℕ)+1 then 1 else 0)*F j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← greenKernel_jump v (n+1) l (j+1)]
      ring
    _ = _ := by
      rw [Finset.sum_eq_single (⟨l,hl⟩:Fin n)]
      · simp
      · intro j hj hjl
        have hne : l ≠ (j:ℕ) := by
          intro hh
          apply hjl
          apply Fin.ext
          exact hh.symm
        simp [hne]
      · simp

lemma nonlinear_fixedPoint_orbit (k q a r : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q a) (n+1) ≠ 0)
    (ζ : Fin n → ℝ)
    (hζ : ∀ i, ζ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ζ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ j))) :
    ∃ b : ℝ, liftedOrbit k (q+r) b (n+1)=liftedOrbit k q a (n+1) ∧
      ∀ i : Fin n, liftedOrbit k (q+r) b (i+1)-liftedOrbit k q a (i+1)=ζ i := by
  let v:=orbitCoefficient k q a
  let U:=dirichletSolution v (n+1)
  let F : Fin n → ℝ := fun j => -(phi k (liftedOrbit k q a (j+1)+ζ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ j)
  let ξ : ℕ → ℝ := fun p => U p*r+∑ j : Fin n, greenKernel v (n+1) p (j+1)*F j
  have hξ (i : Fin n) : ξ (i+1)=ζ i := (hζ i).symm
  have hξ0 : ξ 0=r := by simp only [ξ,U,dirichletSolution_zero,greenKernel_zero,zero_mul,Finset.sum_const_zero,one_mul,add_zero]
  have hξn : ξ (n+1)=0 := by
    simp only [ξ,U,dirichletSolution_boundary v (n+1) ht,zero_mul,zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    rw [greenKernel_boundary v (n+1) (j+1) ht (by omega),zero_mul]
  have hstep (l : ℕ) (hl : l<n) :
      liftedOrbit k q a (l+2)+ξ (l+2)=
        phi k (liftedOrbit k q a (l+1)+ξ (l+1))-(liftedOrbit k q a l+ξ l) := by
    have hG:=green_convolution_jump v n l hl F
    have hU:=dirichletSolution_step v (n+1) l
    have hζ':=hξ (⟨l,hl⟩:Fin n)
    change U (l+2)=v (l+1)*U (l+1)-U l at hU
    have hlin : v (l+1)*ξ (l+1)-ξ l-ξ (l+2)=F ⟨l,hl⟩ := by
      dsimp only [ξ]
      linear_combination hG - r*hU
    dsimp only [F] at hlin
    rw [← hζ'] at hlin
    change potential k (liftedOrbit k q a (l+1))*ξ (l+1)-ξ l-ξ (l+2)=
      -(phi k (liftedOrbit k q a (l+1)+ξ (l+1))-phi k (liftedOrbit k q a (l+1))-
        potential k (liftedOrbit k q a (l+1))*ξ (l+1)) at hlin
    rw [liftedOrbit_step]
    linarith
  have horb : ∀ p, p ≤ n+1 → liftedOrbit k (q+r) (a+ξ 1) p=liftedOrbit k q a p+ξ p := by
    intro p
    induction p using Nat.twoStepInduction with
    | zero => intro hp; simp [liftedOrbit,hξ0]
    | one => intro hp; rfl
    | more p ih0 ih1 =>
      intro hp
      rw [liftedOrbit_step,ih0 (by omega),ih1 (by omega)]
      exact (hstep p (by omega)).symm
  refine ⟨a+ξ 1,?_,?_⟩
  · simpa only [hξn,add_zero] using horb (n+1) le_rfl
  · intro i
    rw [horb (i+1) (by omega),add_sub_cancel_left,hξ i]
end StandardMapEntropy

end OAI
