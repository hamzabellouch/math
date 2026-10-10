import OAI.Dynamics.StandardMap.GraphCalculus

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma bridge_green_row (k q a : ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
      12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) (i : Fin n) :
    ∑ j : Fin n, |growthBase k^((4/5:ℝ)*((i:ℝ)+1))*greenMatrix (orbitCoefficient k q a) n i j| *
      ((2*Real.pi*growthBase k)*8/growthBase k^((4/5:ℝ)*((j:ℝ)+1)))/
        growthBase k^((4/5:ℝ)*((j:ℝ)+1)) ≤ 1/2 := by
  have hm : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hh:=green_weighted_rows (growthBase k) 12 8 n (tSolution (orbitCoefficient k q a))
    (dirichletSolution (orbitCoefficient k q a) (n+1)) hm (by norm_num) (by norm_num) hq
    (fun p hp' hn => tSolution_abs_le_pow _ _ p hp' hm.le
      (fun i hi hip => potential_bound k (liftedOrbit k q a i) hk)) hU i
  have he : ∀ i j : Fin n, greenMatrix (orbitCoefficient k q a) n i j=
      tSolution (orbitCoefficient k q a) (min (i:ℕ) (j:ℕ)+1)*
      dirichletSolution (orbitCoefficient k q a) (n+1) (max (i:ℕ) (j:ℕ)+1) := by
    intro i j
    simp only [greenMatrix,greenKernel,min_add_add_right,max_add_add_right]
  simp_rw [he]
  exact hh.trans (by nlinarith only [hsmall])

lemma nonlinear_fixedPoint_stability (k q a : ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
      12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (r s : ℝ) (ξ ζ : Fin n → ℝ)
    (hξb : ∀ i, |ξ i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hζb : ∀ i, |ζ i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hξ : ∀ i, ξ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ξ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ξ j)))
    (hζ : ∀ i, ζ i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*s+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ζ j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ j))) :
    ∀ i, |ξ i-ζ i| ≤ 24*|r-s|/growthBase k^((4/5:ℝ)*((i:ℝ)+1)) := by
  let M := growthBase k
  have hm : 1 < M := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < M := by linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : Fin n → ℝ := fun i => dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)
  let F : Fin n → ℝ → ℝ := fun j z => -(phi k (liftedOrbit k q a (j+1)+z)-
    phi k (liftedOrbit k q a (j+1))-potential k (liftedOrbit k q a (j+1))*z)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  have hw (i : Fin n) : 0 < w i := Real.rpow_pos_of_pos hp _
  have hlin : ‖fun i => w i*U i‖ ≤ (12:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    have hU':=hU (i+1) (by omega) (by omega)
    have hexp : M^((4/5:ℝ)*((i:ℝ)+1))*M^(-(9/10:ℝ)*((i:ℝ)+1)) ≤ 1 := by
      rw [← Real.rpow_add hp]
      exact Real.rpow_le_one_of_one_le_of_nonpos hm.le (by have : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _; linarith)
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (hw i)]
    calc
      _ ≤ w i*(12*M^(-(9/10:ℝ)*((i:ℝ)+1))) := by
        gcongr
        simpa only [U,Nat.cast_add,Nat.cast_one] using hU'
      _ ≤ _ := by dsimp only [w]; nlinarith
  have hn:=weighted_fixedPoint_stability w U (greenMatrix (orbitCoefficient k q a) n) F L ξ ζ r s 12 hw
    (fun i => by dsimp only [L]; positivity) (by
      intro i
      dsimp only [F]
      rw [← neg_sub,abs_neg]
      have hh:=phi_remainder_lipschitz k (liftedOrbit k q a (i+1)) (ξ i) (ζ i) (8/w i) hk (hξb i) (hζb i)
      dsimp only [L,M]
      convert hh using 1 <;> ring_nf)
    (bridge_green_row k q a n hk hq hsmall hU) hlin hξ hζ
  intro i
  apply (le_div_iff₀ (hw i)).mpr
  have hh:=(norm_le_pi_norm (fun i => w i*(ξ i-ζ i)) i).trans hn
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (hw i),mul_comm,show (2:ℝ)*12=24 by norm_num] using hh

lemma nonlinear_dirichlet_family (k q a : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (ht : tSolution (orbitCoefficient k q a) (n+1) ≠ 0)
    (hU : ∀ p, 1 ≤ p → p ≤ n → |dirichletSolution (orbitCoefficient k q a) (n+1) p| ≤
      12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : ℝ → ℝ, b 0=a ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (q+r) (b r) (n+1)=liftedOrbit k q a (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (q+r) (b r) (i+1)-liftedOrbit k q a (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      (∀ r s, |r| ≤ 1/4 → |s| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (q+r) (b r) (i+1)-liftedOrbit k (q+s) (b s) (i+1)| ≤
          24*|r-s|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  classical
  let ζ : ℝ → Fin n → ℝ := fun r => if hr : |r| ≤ 1/4 then
    (nonlinear_dirichlet_fixedPoint k q a r n hk hr hq hsmall hU).choose else 0
  have hz (r : ℝ) (hr : |r| ≤ 1/4) :=
    (nonlinear_dirichlet_fixedPoint k q a r n hk hr hq hsmall hU).choose_spec
  have hζb (r : ℝ) (hr : |r| ≤ 1/4) (i : Fin n) :
      |ζ r i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)) := by
    simpa only [ζ,dite_eq_left hr] using (hz r hr).1 i
  have hζ (r : ℝ) (hr : |r| ≤ 1/4) (i : Fin n) :
      ζ r i=dirichletSolution (orbitCoefficient k q a) (n+1) (i+1)*r+
        ∑ j, greenMatrix (orbitCoefficient k q a) n i j *
          (-(phi k (liftedOrbit k q a (j+1)+ζ r j)-phi k (liftedOrbit k q a (j+1))-
            potential k (liftedOrbit k q a (j+1))*ζ r j)) := by
    simpa only [ζ,dite_eq_left hr] using (hz r hr).2 i
  let b : ℝ → ℝ := fun r => a+ζ r ⟨0,hn⟩
  have horb (r : ℝ) (hr : |r| ≤ 1/4) :
      liftedOrbit k (q+r) (b r) (n+1)=liftedOrbit k q a (n+1) ∧
      ∀ i : Fin n, liftedOrbit k (q+r) (b r) (i+1)-liftedOrbit k q a (i+1)=ζ r i := by
    obtain ⟨b',he,hξ⟩:=nonlinear_fixedPoint_orbit k q a r n ht (ζ r) (hζ r hr)
    have h0:=hξ ⟨0,hn⟩
    change b'-a=ζ r ⟨0,hn⟩ at h0
    have hb' : b'=b r := by dsimp only [b]; linarith
    subst b'
    exact ⟨he,hξ⟩
  have hζ0 : ζ 0=0 := by
    have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
    have hh:=nonlinear_fixedPoint_stability k q a n hk hq hsmall hU 0 0 (ζ 0) 0
      (hζb 0 (by norm_num)) (fun i => by simpa using (div_nonneg (by norm_num : (0:ℝ) ≤ 8) (Real.rpow_pos_of_pos hp _).le))
      (hζ 0 (by norm_num)) (fun i => by simp)
    funext i
    have hi:=hh i
    simpa using (abs_nonpos_iff.mp (by simpa using hi) : ζ 0 i=0)
  refine ⟨b,?_,fun r hr => (horb r hr).1,?_,?_⟩
  · simp [b,hζ0]
  · intro r hr i
    rw [(horb r hr).2 i]
    exact hζb r hr i
  · intro r s hr hs i
    have hh:=nonlinear_fixedPoint_stability k q a n hk hq hsmall hU r s (ζ r) (ζ s)
      (hζb r hr) (hζb s hs) (hζ r hr) (hζ s hs) i
    have he : liftedOrbit k (q+r) (b r) (i+1)-liftedOrbit k (q+s) (b s) (i+1)=ζ r i-ζ s i := by
      rw [← (horb r hr).2 i,← (horb s hs).2 i]; ring
    rwa [he]
end StandardMapEntropy

end OAI
