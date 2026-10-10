import OAI.Dynamics.StandardMap.FixedPointFamily

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma hasStrictFDerivAt_liftedOrbit_shift (k q r a : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k (q+z.1) z.2 n)
      (sSolution (orbitCoefficient k (q+r) a) n • ContinuousLinearMap.fst ℝ ℝ ℝ+
       tSolution (orbitCoefficient k (q+r) a) n • ContinuousLinearMap.snd ℝ ℝ ℝ) (r,a) := by
  have hpair : HasStrictFDerivAt (fun z : ℝ × ℝ => (q+z.1,z.2)) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) (r,a) := by
    have h1 : HasStrictFDerivAt (fun z : ℝ × ℝ => q+z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (r,a) := by
      have hh := (hasStrictFDerivAt_const q (r,a)).add (hasStrictFDerivAt_fst (𝕜 := ℝ))
      convert! hh using 1
      simp
    have h2 : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (r,a) := hasStrictFDerivAt_snd
    simpa using h1.prodMk h2
  have hh := (hasStrictFDerivAt_liftedOrbit k (q+r) a n).comp (r,a) hpair
  simpa only [ContinuousLinearMap.comp_id] using hh

lemma hasDerivAt_liftedOrbit_curve (k q r : ℝ) (b : ℝ → ℝ) (b' : ℝ)
    (hb : HasDerivAt b b' r) (n : ℕ) :
    HasDerivAt (fun x => liftedOrbit k (q+x) (b x) n)
      (linearSolution (orbitCoefficient k (q+r) (b r)) 1 b' n) r := by
  have hpair := ((hasDerivAt_id r).const_add q).prodMk hb
  have hh := (hasStrictFDerivAt_liftedOrbit k (q+r) (b r) n).hasFDerivAt.comp_hasDerivAt r hpair
  rw [linearSolution_decomposition]
  convert! hh using 1
  change 1*sSolution _ n+b'*tSolution _ n=sSolution _ n*1+tSolution _ n*b'
  ring

lemma continuousAt_of_local_lipschitz (f : ℝ → ℝ) (x R C : ℝ) (hC : 0 ≤ C)
    (hx : |x| < R)
    (hLip : ∀ y z, |y| ≤ R → |z| ≤ R → |f y-f z| ≤ C*|y-z|) : ContinuousAt f x := by
  have hcont : ContinuousOn f (Icc (-R) R) := by
    apply LipschitzOnWith.continuousOn (K := (⟨C,hC⟩ : NNReal))
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    change |f y-f z| ≤ C*|y-z|
    exact hLip y z (abs_le.mpr hy) (abs_le.mpr hz)
  exact (hcont x (abs_le.mp hx.le)).continuousAt
    (Icc_mem_nhds (by linarith [(abs_lt.mp hx).1]) (abs_lt.mp hx).2)

lemma contracting_family_derivatives (k q a : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
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
      (∀ r, |r| ≤ 1/4 → tSolution (orbitCoefficient k (q+r) (b r)) (n+1) ≠ 0) ∧
      (∀ r, |r| < 1/4 → ∀ p,
        HasDerivAt (fun x => liftedOrbit k (q+x) (b x) p)
          (dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) p) r) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |dirichletSolution (orbitCoefficient k (q+r) (b r)) (n+1) (i+1)| ≤
          24/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  obtain ⟨b,hb0,hterm,hbound,hLip⟩:=nonlinear_dirichlet_family k q a n hn hk hq hsmall ht hU
  have hm : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < growthBase k := by linarith
  have hvar (r : ℝ) (hr : |r| ≤ 1/4) := varied_dirichlet_bound (orbitCoefficient k q a)
    (orbitCoefficient k (q+r) (b r)) (growthBase k) n hm hq hsmall ht
    (fun p hp' hn => tSolution_abs_le_pow _ _ p hp' hm.le
      (fun i hi hip => potential_bound k (liftedOrbit k q a i) hk)) hU (by
      intro i
      have hh:=potential_lipschitz k (liftedOrbit k q a (i+1)) (liftedOrbit k (q+r) (b r) (i+1)) hk
      dsimp only [orbitCoefficient]
      calc
        _ ≤ (2*Real.pi*growthBase k)*|liftedOrbit k q a (i+1)-liftedOrbit k (q+r) (b r) (i+1)| := by simpa only [abs_sub_comm] using hh
        _ ≤ (2*Real.pi*growthBase k)*(8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
          gcongr
          simpa only [abs_sub_comm] using hbound r hr i
        _ = _ := by ring)
  refine ⟨b,hb0,hterm,hbound,fun r hr => (hvar r hr).1,?_,fun r hr => (hvar r hr).2⟩
  intro r hr p
  have hcont : ContinuousAt b r := continuousAt_of_local_lipschitz b r (1/4)
    (24/growthBase k^((4/5:ℝ))) (by positivity) hr (by
      intro y z hy hz
      have hh:=hLip y z hy hz (⟨0,hn⟩:Fin n)
      simpa only [Fin.val_zero,Nat.cast_zero,zero_add,mul_one,liftedOrbit_one,div_mul_eq_mul_div] using hh)
  have hd := hasDerivAt_of_regular_level (fun z : ℝ × ℝ => liftedOrbit k (q+z.1) z.2 (n+1)) b r
    (sSolution (orbitCoefficient k (q+r) (b r)) (n+1)) (tSolution (orbitCoefficient k (q+r) (b r)) (n+1))
    (hasStrictFDerivAt_liftedOrbit_shift k q r (b r) (n+1)) (hvar r hr.le).1 hcont (by
      have he : ∀ᶠ y in 𝓝 r, |y| < 1/4 := (continuous_abs.continuousAt.eventually (Iio_mem_nhds hr))
      filter_upwards [he] with y hy
      exact (hterm y hy.le).trans (hterm r hr.le).symm)
  exact hasDerivAt_liftedOrbit_curve k q r b _ hd p
end StandardMapEntropy

end OAI
