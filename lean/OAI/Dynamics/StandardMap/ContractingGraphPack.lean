import OAI.Dynamics.StandardMap.StrictGraphCalculus

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma continuous_contracting_graph_pack_full (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (S : Set (ℝ × ℝ))
    (ht : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : (ℝ × ℝ) → ℝ → ℝ,
      ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (S ×ˢ Icc (-(1/4)) (1/4)) ∧
      ∀ z ∈ S, b z 0=z.2 ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1) ≠ 0) ∧
      (∀ r, |r| < 1/4 → HasStrictDerivAt (b z)
        (boundaryValue (orbitCoefficient k (z.1+r) (b z r)) (n+1)) r) ∧
      (∀ r, |r| ≤ 1/4 →
        |boundaryValue (orbitCoefficient k (z.1+r) (b z r)) (n+1)| ≤
          24/growthBase k^((4/5:ℝ))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 →
        |b z r-b z t| ≤ (24/growthBase k^((4/5:ℝ)))*|r-t|) ∧
      (∀ r t, |r| < 1/4 → |t| < 1/4 →
        Real.exp (-1152*Real.pi) ≤
          |tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1)|/
          |tSolution (orbitCoefficient k (z.1+t) (b z t)) (n+1)| ∧
        |tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1)|/
          |tSolution (orbitCoefficient k (z.1+t) (b z t)) (n+1)| ≤ Real.exp (1152*Real.pi)) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)| ≤
          24*|r-t|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
  obtain ⟨b,hcont,hb⟩ := jointly_continuous_dirichlet_family k n hn hk hq hsmall S ht hU
  refine ⟨b,hcont,?_⟩
  intro z hz
  obtain ⟨hb0,hterm,hbound,hLip⟩ := hb z hz
  obtain ⟨ht',hd,hU'⟩ := contracting_family_derivatives_of_bounds k z.1 z.2 n hn hk hq hsmall
    (ht z hz) (hU z hz) (b z) hterm hbound hLip
  have hLip' (r t : ℝ) (hr : |r| ≤ 1/4) (ht : |t| ≤ 1/4) :
      |b z r-b z t| ≤ (24/growthBase k^((4/5:ℝ)))*|r-t| := by
    simpa only [Fin.val_zero,Nat.cast_zero,zero_add,mul_one,liftedOrbit_one,div_mul_eq_mul_div]
      using hLip r t hr ht (⟨0,hn⟩:Fin n)
  refine ⟨hb0,hterm,ht',?_,?_,hLip',?_,hbound,hLip⟩
  · intro r hr
    apply hasStrictDerivAt_of_regular_level
      (fun w : ℝ × ℝ => liftedOrbit k (z.1+w.1) w.2 (n+1)) (b z) r
      (sSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1))
      (tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1))
      (hasStrictFDerivAt_liftedOrbit_shift k z.1 r (b z r) (n+1)) (ht' r hr.le)
    · exact continuousAt_of_local_lipschitz (b z) r (1/4) (24/growthBase k^((4/5:ℝ)))
        (by positivity) hr hLip'
    · filter_upwards [(continuous_abs.continuousAt.eventually (Iio_mem_nhds hr))] with y hy
      exact (hterm y hy.le).trans (hterm r hr.le).symm
  · intro r hr
    simpa only [Fin.val_zero,Nat.cast_zero,zero_add,mul_one,dirichletSolution,linearSolution] using hU' r hr (⟨0,hn⟩:Fin n)
  · intro r t hr ht
    exact contracting_graph_terminal_ratio k z.1 (b z) n hk hq
      (fun r hr => ht' r hr.le) hd (fun r hr => hU' r hr.le) ht hr
lemma continuous_contracting_graph_pack (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (S : Set (ℝ × ℝ))
    (ht : ∀ z ∈ S, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ S, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : (ℝ × ℝ) → ℝ → ℝ,
      ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (S ×ˢ Icc (-(1/4)) (1/4)) ∧
      ∀ z ∈ S, b z 0=z.2 ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1) ≠ 0) ∧
      (∀ r, |r| < 1/4 → HasStrictDerivAt (b z)
        (boundaryValue (orbitCoefficient k (z.1+r) (b z r)) (n+1)) r) ∧
      (∀ r, |r| ≤ 1/4 →
        |boundaryValue (orbitCoefficient k (z.1+r) (b z r)) (n+1)| ≤
          24/growthBase k^((4/5:ℝ))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 →
        |b z r-b z t| ≤ (24/growthBase k^((4/5:ℝ)))*|r-t|) ∧
      (∀ r t, |r| < 1/4 → |t| < 1/4 →
        Real.exp (-1152*Real.pi) ≤
          |tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1)|/
          |tSolution (orbitCoefficient k (z.1+t) (b z t)) (n+1)| ∧
        |tSolution (orbitCoefficient k (z.1+r) (b z r)) (n+1)|/
          |tSolution (orbitCoefficient k (z.1+t) (b z t)) (n+1)| ≤ Real.exp (1152*Real.pi)) := by
  obtain ⟨b,hc,hb⟩ := continuous_contracting_graph_pack_full k n hn hk hq hsmall S ht hU
  refine ⟨b,hc,?_⟩
  intro z hz
  obtain ⟨h0,hterm,ht',hd,hs,hL,hrat,_,_⟩ := hb z hz
  exact ⟨h0,hterm,ht',hd,hs,hL,hrat⟩
end StandardMapEntropy

end OAI
