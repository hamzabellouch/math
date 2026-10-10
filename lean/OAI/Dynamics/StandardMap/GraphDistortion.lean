import OAI.Dynamics.StandardMap.LogDerivativeCore

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma finite_six_tenths_sum (M : ℝ) (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2) (n : ℕ) :
    ∑ i ∈ Finset.range n, M^(-(3/5:ℝ)*((i:ℝ)+1)) ≤ 2 := by
  have hp : 0 < M := by linarith
  have he (i : ℕ) : M^(-(3/5:ℝ)*((i:ℝ)+1)) = (M^(-(3/5:ℝ)))^i*M^(-(3/5:ℝ)) := by
    rw [← Real.rpow_mul_natCast hp.le,← Real.rpow_add hp]
    congr 1; ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hs : ∑ i ∈ Finset.range n, (M^(-(3/5:ℝ)))^i ≤ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (1/2:ℝ)^i := by gcongr
      _ ≤ 2 := sum_geometric_two_le n
  nlinarith [Real.rpow_pos_of_pos hp (-(3/5:ℝ))]

lemma log_dirichlet_row_bound (M : ℝ) (n : ℕ) (t U V : ℕ → ℝ)
    (hM : 1 < M) (hq : M^(-(3/5:ℝ)) ≤ 1/2)
    (ht : ∀ p, 1 ≤ p → p ≤ n → |t p| ≤ M^((p:ℝ)-1))
    (hU : ∀ p, 1 ≤ p → p ≤ n → |U p| ≤ 24/M^((4/5:ℝ)*(p:ℝ)))
    (hV : ∀ p, 1 ≤ p → p ≤ n → |V p| ≤ 2*Real.pi*M) :
    |∑ i ∈ Finset.range n, t (i+1)*U (i+1)*(V (i+1)*U (i+1))| ≤ 2304*Real.pi := by
  have hp : 0 < M := by linarith
  calc
    _ ≤ ∑ i ∈ Finset.range n, |t (i+1)*U (i+1)*(V (i+1)*U (i+1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (1152*Real.pi)*M^(-(3/5:ℝ)*((i:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simp only [abs_mul]
      calc
        _ ≤ M^((i:ℝ))* (24/M^((4/5:ℝ)*((i:ℝ)+1)))*
            ((2*Real.pi*M)*(24/M^((4/5:ℝ)*((i:ℝ)+1)))) := by
          gcongr
          · simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using ht (i+1) (by omega) (by omega)
          · simpa only [Nat.cast_add,Nat.cast_one] using hU (i+1) (by omega) (by omega)
          · exact hV (i+1) (by omega) (by omega)
          · simpa only [Nat.cast_add,Nat.cast_one] using hU (i+1) (by omega) (by omega)
        _ = _ := by
          rw [show -(3/5:ℝ)*((i:ℝ)+1)=(i:ℝ)+1-((4/5)*((i:ℝ)+1)+(4/5)*((i:ℝ)+1)) by ring,
            Real.rpow_sub hp,Real.rpow_add hp,Real.rpow_add hp,Real.rpow_one]
          ring
    _ = (1152*Real.pi)*(∑ i ∈ Finset.range n, M^(-(3/5:ℝ)*((i:ℝ)+1))) := by rw [Finset.mul_sum]
    _ ≤ (1152*Real.pi)*2 := mul_le_mul_of_nonneg_left (finite_six_tenths_sum M hM hq n) (by positivity)
    _ = _ := by ring

lemma log_terminal_derivative_bound (k q r : ℝ) (b : ℝ → ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (ht : tSolution (orbitCoefficient k (q+r) (b r)) (n+1) ≠ 0)
    (hd : ∀ p, HasDerivAt (fun x => liftedOrbit k (q+x) (b x) p)
      (dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) p) r)
    (hU : ∀ i : Fin n, |dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) (i+1)| ≤
      24/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) :
    ∃ D : ℝ, HasDerivAt (fun x => Real.log |tSolution (orbitCoefficient k (q+x) (b x)) (n+1)|) D r ∧
      |D| ≤ 2304*Real.pi := by
  let v : ℝ → ℕ → ℝ := fun x => orbitCoefficient k (q+x) (b x)
  let U:=dirichletSolution (v r) (n+1)
  let V : ℕ → ℝ := fun p => phiSecond k (liftedOrbit k (q+r) (b r) p)
  have hv (p : ℕ) : HasDerivAt (fun x => v x p) (V p*U p) r :=
    (hasDerivAt_potential k _).comp r (hd p)
  have hder:=hasDerivAt_log_tSolution_family v (fun p => V p*U p) r hv n ht
  refine ⟨_,hder,?_⟩
  have hm : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  exact log_dirichlet_row_bound (growthBase k) n (tSolution (v r)) U V hm hq
    (fun p hp' hn => tSolution_abs_le_pow _ _ p hp' hm.le
      (fun i hi hip => potential_bound k (liftedOrbit k (q+r) (b r) i) hk))
    (by
      intro p hp' hpn
      obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      simpa only [Nat.cast_succ] using hU ⟨i,by omega⟩)
    (fun p hp' hpn => phiSecond_bound k _ hk)

lemma log_ratio_of_derivative_bound (f : ℝ → ℝ) (C R x y : ℝ)
    (_hC : 0 ≤ C) (hx : |x| < R) (hy : |y| < R)
    (hD : ∀ r, |r| < R → ∃ D, HasDerivAt (fun r => Real.log |f r|) D r ∧ |D| ≤ C)
    (hn : ∀ r, |r| < R → f r ≠ 0) :
    Real.exp (-C*|y-x|) ≤ |f y|/|f x| ∧ |f y|/|f x| ≤ Real.exp (C*|y-x|) := by
  have hlog : |Real.log (abs (f y))-Real.log (abs (f x))| ≤ C*|y-x| := by
    have hh:=Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun r => Real.log |f r|) (s := Ioo (-R) R)
      (fun r hr => (hD r (abs_lt.mpr hr)).choose_spec.1.differentiableAt)
      (by
        intro r hr
        obtain ⟨D,hD,hb⟩:=hD r (abs_lt.mpr hr)
        rw [hD.deriv,Real.norm_eq_abs]
        exact hb)
      (convex_Ioo (-R) R) (abs_lt.mp hx) (abs_lt.mp hy)
    exact hh
  have hposx : 0 < |f x| := abs_pos.mpr (hn x hx)
  have hposy : 0 < |f y| := abs_pos.mpr (hn y hy)
  have he : Real.exp (Real.log |f y|-Real.log |f x|)=|f y|/|f x| := by
    rw [Real.exp_sub,Real.exp_log hposy,Real.exp_log hposx]
  constructor
  · rw [← he,Real.exp_le_exp]
    linarith [(abs_le.mp hlog).1]
  · rw [← he,Real.exp_le_exp]
    exact (abs_le.mp hlog).2

lemma contracting_graph_terminal_ratio (k q : ℝ) (b : ℝ → ℝ) (n : ℕ)
    (hk : 0 ≤ k) (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (ht : ∀ r, |r| < 1/4 → tSolution (orbitCoefficient k (q+r) (b r)) (n+1) ≠ 0)
    (hd : ∀ r, |r| < 1/4 → ∀ p, HasDerivAt (fun x => liftedOrbit k (q+x) (b x) p)
      (dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) p) r)
    (hU : ∀ r, |r| < 1/4 → ∀ i : Fin n,
      |dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) (i+1)| ≤
      24/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    {x y : ℝ} (hx : |x| < 1/4) (hy : |y| < 1/4) :
    Real.exp (-1152*Real.pi) ≤
      |tSolution (orbitCoefficient k (q+y) (b y)) (n+1)|/
      |tSolution (orbitCoefficient k (q+x) (b x)) (n+1)| ∧
      |tSolution (orbitCoefficient k (q+y) (b y)) (n+1)|/
      |tSolution (orbitCoefficient k (q+x) (b x)) (n+1)| ≤ Real.exp (1152*Real.pi) := by
  have hh:=log_ratio_of_derivative_bound
    (fun r => tSolution (orbitCoefficient k (q+r) (b r)) (n+1)) (2304*Real.pi) (1/4) x y
    (by positivity) hx hy
    (fun r hr => log_terminal_derivative_bound k q r b n hk hq (ht r hr) (hd r hr) (hU r hr)) ht
  have hxy : |y-x| ≤ 1/2 := by
    have hh:=norm_sub_le y x
    simp only [Real.norm_eq_abs] at hh
    linarith
  constructor
  · apply le_trans _ hh.1
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  · apply le_trans hh.2
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos]
end StandardMapEntropy

end OAI
