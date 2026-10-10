import OAI.Dynamics.StandardMap.BridgeWeights

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma tSolution_abs_le_pow (v : ℕ → ℝ) (M : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hM : 1 ≤ M) (hv : ∀ i, 1 ≤ i → i < p → |v i|+1 ≤ M) :
    |tSolution v p| ≤ M^((p:ℝ)-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have hh := (transferProduct_norm_bounds v M n (by linarith)
    (fun i hi hin => hv i hi (by omega))).2
  have hp := (transferProduct v n).le_opNorm (1:ℂ)
  have he : (transferProduct v n 1).re=tSolution v (n+1) := by
    change (transferProduct v n ⟨1,0⟩).re=tSolution v (n+1)
    rw [transferProduct_pair]; rfl
  calc
    _ = |(transferProduct v n 1).re| := congrArg abs he.symm
    _ ≤ ‖transferProduct v n 1‖ := Complex.abs_re_le_norm _
    _ ≤ M^n := by simpa only [norm_one,mul_one] using hp.trans (by simpa using hh)
    _ = _ := by simp only [Nat.cast_succ,add_sub_cancel_right,Real.rpow_natCast]

lemma nonlinear_dirichlet_fixedPoint (k q a r : ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hr : |r| ≤ 1/4)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (hU : ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ ξ : Fin n → ℝ,
      (∀ i, |ξ i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      ∀ i, ξ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ξ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ξ j)) := by
  let M := growthBase k
  have hMm : 4 ≤ M := growthBase_ge_four k hk
  have hm : 1 < M := by linarith
  have hp : 0 < M := by linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : Fin n → ℝ := fun i => dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)
  let F : Fin n → ℝ → ℝ := fun j z => -(phi k (liftedOrbit k q a (j+1)+z)-
    phi k (liftedOrbit k q a (j+1))-potential k (liftedOrbit k q a (j+1))*z)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  have hw (i : Fin n) : 0 < w i := Real.rpow_pos_of_pos hp _
  have hlin (i : Fin n) : |w i*U i*r| ≤ (8:ℝ)/2 := by
    have hU':=hU (i+1) (by omega) (by omega)
    have hexp : M^((4/5:ℝ)*((i:ℝ)+1))*M^(-(9/10:ℝ)*((i:ℝ)+1)) ≤ 1 := by
      rw [← Real.rpow_add hp]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm.le (by have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _; linarith)
    rw [abs_mul,abs_mul,abs_of_pos (hw i)]
    calc
      _ ≤ w i*(12*M^(-(9/10:ℝ)*((i:ℝ)+1)))*(1/4) := by
        gcongr
        simpa only [U,Nat.cast_add,Nat.cast_one] using hU'
      _ ≤ 3 := by dsimp only [w]; nlinarith
      _ ≤ _ := by norm_num
  have hrow (i : Fin n) : ∑ j, |w i*greenMatrix (orbitCoefficient k q a) n i j| *L j/w j ≤ 1/2 := by
    have hh:=green_weighted_rows M 12 8 n (tSolution (orbitCoefficient k q a))
      (dirichletSolution (orbitCoefficient k q a) (n+1)) hm (by norm_num) (by norm_num) hq
      (fun p hp' hn => tSolution_abs_le_pow _ M p hp' hm.le
        (fun i hi hip => potential_bound k (liftedOrbit k q a i) hk)) hU i
    have he : ∀ i j : Fin n, greenMatrix (orbitCoefficient k q a) n i j=
        tSolution (orbitCoefficient k q a) (min (i:ℕ) (j:ℕ)+1)*
        dirichletSolution (orbitCoefficient k q a) (n+1) (max (i:ℕ) (j:ℕ)+1) := by
      intro i j
      simp only [greenMatrix,greenKernel,min_add_add_right,max_add_add_right]
    simp_rw [he]
    exact hh.trans (by nlinarith only [hsmall])
  exact finite_weighted_dirichlet w U (greenMatrix (orbitCoefficient k q a) n) F L r 8 hw
    (by norm_num) (fun i => by dsimp [L]; positivity)
    (by intro i; simp [F])
    (by
      intro i x y hx hy
      dsimp only [F]
      rw [← neg_sub,abs_neg]
      have hh:=phi_remainder_lipschitz k (liftedOrbit k q a (i+1)) x y (8/w i) hk hx hy
      dsimp only [L,M]
      convert hh using 1 <;> ring_nf)
    hlin hrow
end StandardMapEntropy

end OAI
