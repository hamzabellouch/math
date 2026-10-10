import OAI.Dynamics.StandardMap.WeightedStability

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma linear_fixedPoint_dirichlet (v v' : ℕ → ℝ) (n : ℕ)
    (ht : tSolution v (n+1) ≠ 0) (ζ : Fin n → ℝ)
    (hζ : ∀ i, ζ i=dirichletSolution v (n+1) (i+1)+
      ∑ j, greenMatrix v n i j*((v (j+1)-v' (j+1))*ζ j)) :
    tSolution v' (n+1) ≠ 0 ∧ ∀ i : Fin n, dirichletSolution v' (n+1) (i+1)=ζ i := by
  let U:=dirichletSolution v (n+1)
  let F : Fin n → ℝ := fun j => (v (j+1)-v' (j+1))*ζ j
  let ξ : ℕ → ℝ := fun p => U p+∑ j : Fin n, greenKernel v (n+1) p (j+1)*F j
  have hξ (i : Fin n) : ξ (i+1)=ζ i := (hζ i).symm
  have hξ0 : ξ 0=1 := by simp only [ξ,U,dirichletSolution_zero,greenKernel_zero,zero_mul,Finset.sum_const_zero,add_zero]
  have hξn : ξ (n+1)=0 := by
    simp only [ξ,U,dirichletSolution_boundary v (n+1) ht,zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    rw [greenKernel_boundary v (n+1) (j+1) ht (by omega),zero_mul]
  have hstep (l : ℕ) (hl : l<n) : ξ (l+2)=v' (l+1)*ξ (l+1)-ξ l := by
    have hG:=green_convolution_jump v n l hl F
    have hU:=dirichletSolution_step v (n+1) l
    have hζ':=hξ (⟨l,hl⟩:Fin n)
    change U (l+2)=v (l+1)*U (l+1)-U l at hU
    have hlin : v (l+1)*ξ (l+1)-ξ l-ξ (l+2)=F ⟨l,hl⟩ := by
      dsimp only [ξ]
      linear_combination hG - hU
    dsimp only [F] at hlin
    rw [← hζ'] at hlin
    nlinarith only [hlin]
  have hsol : ∀ p, p ≤ n+1 → linearSolution v' 1 (ξ 1) p=ξ p := by
    intro p
    induction p using Nat.twoStepInduction with
    | zero => intro hp; exact hξ0.symm
    | one => intro hp; rfl
    | more p ih0 ih1 =>
      intro hp
      rw [linearSolution_step,ih0 (by omega),ih1 (by omega)]
      exact (hstep p (by omega)).symm
  have hterm : linearSolution v' 1 (ξ 1) (n+1)=0 := (hsol _ le_rfl).trans hξn
  have ht' : tSolution v' (n+1) ≠ 0 := by
    have hh:=solution_wronskian v' 1 (ξ 1) n
    rw [hterm,zero_mul,sub_zero] at hh
    intro hz
    rw [hz,mul_zero] at hh
    norm_num at hh
  have hb : ξ 1=boundaryValue v' (n+1) := boundaryValue_unique v' (n+1) ht' (ξ 1) hterm
  refine ⟨ht',?_⟩
  intro i
  have he:=hsol (i+1) (by omega)
  rw [hb] at he
  exact he.trans (hξ i)

lemma varied_dirichlet_bound (v v' : ℕ → ℝ) (M : ℝ) (n : ℕ)
    (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*M^(-(7/10:ℝ)) ≤ 1/2)
    (ht : tSolution v (n+1) ≠ 0)
    (hv : ∀ p, 1 ≤ p → p ≤ n → |tSolution v p| ≤ M^((p:ℝ)-1))
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution v (n+1) p| ≤ 12*M^(-(9/10:ℝ)*(p:ℝ)))
    (hdiff : ∀ i : Fin n, |v (i+1)-v' (i+1)| ≤ (2*Real.pi*M)*8/M^((4/5:ℝ)*((i:ℝ)+1))) :
    tSolution v' (n+1) ≠ 0 ∧ ∀ i : Fin n,
      |dirichletSolution v' (n+1) (i+1)| ≤ 24/M^((4/5:ℝ)*((i:ℝ)+1)) := by
  have hp : 0 < M := by linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : Fin n → ℝ := fun i => dirichletSolution v (n+1) (i+1)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  let F : Fin n → ℝ → ℝ := fun i x => (v (i+1)-v' (i+1))*x
  have hw (i : Fin n) : 0 < w i := Real.rpow_pos_of_pos hp _
  have hlin (i : Fin n) : |w i*U i*1| ≤ (24:ℝ)/2 := by
    have hU':=hU (i+1) (by omega) (by omega)
    have hexp : M^((4/5:ℝ)*((i:ℝ)+1))*M^(-(9/10:ℝ)*((i:ℝ)+1)) ≤ 1 := by
      rw [← Real.rpow_add hp]
      exact Real.rpow_le_one_of_one_le_of_nonpos hM.le (by have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _; linarith)
    rw [mul_one,abs_mul,abs_of_pos (hw i)]
    calc
      _ ≤ w i*(12*M^(-(9/10:ℝ)*((i:ℝ)+1))) := by
        gcongr
        simpa only [U,Nat.cast_add,Nat.cast_one] using hU'
      _ ≤ 24/2 := by dsimp only [w]; nlinarith
  have hrow (i : Fin n) : ∑ j, |w i*greenMatrix v n i j| *L j/w j ≤ 1/2 := by
    have hh:=green_weighted_rows M 12 8 n (tSolution v) (dirichletSolution v (n+1))
      hM (by norm_num) (by norm_num) hq hv hU i
    have he : ∀ i j : Fin n, greenMatrix v n i j=
        tSolution v (min (i:ℕ) (j:ℕ)+1)*dirichletSolution v (n+1) (max (i:ℕ) (j:ℕ)+1) := by
      intro i j
      simp only [greenMatrix,greenKernel,min_add_add_right,max_add_add_right]
    simp_rw [he]
    exact hh.trans (by nlinarith only [hsmall])
  obtain ⟨ζ,hζb,hζ⟩:=finite_weighted_dirichlet w U (greenMatrix v n) F L 1 24 hw
    (by norm_num) (fun i => by dsimp only [L]; positivity)
    (by intro i; simp [F])
    (by
      intro i x y hx hy
      dsimp only [F]
      rw [← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_right (hdiff i) (abs_nonneg _)) hlin hrow
  have hζ' : ∀ i, ζ i=dirichletSolution v (n+1) (i+1)+
      ∑ j, greenMatrix v n i j*((v (j+1)-v' (j+1))*ζ j) := by
    intro i
    simpa only [U,F,mul_one] using hζ i
  obtain ⟨ht',hsol⟩:=linear_fixedPoint_dirichlet v v' n ht ζ hζ'
  exact ⟨ht',fun i => (hsol i ▸ hζb i)⟩
end StandardMapEntropy

end OAI
