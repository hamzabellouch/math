import OAI.Dynamics.StandardMap.GraphParameterContinuity

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy

lemma jointly_continuous_dirichlet_family (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (s : Set (ℝ × ℝ))
    (ht : ∀ z ∈ s, tSolution (orbitCoefficient k z.1 z.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ s, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1 z.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ))) :
    ∃ b : (ℝ × ℝ) → ℝ → ℝ,
      ContinuousOn (fun z : (ℝ × ℝ) × ℝ => b z.1 z.2) (s ×ˢ Icc (-(1/4)) (1/4)) ∧
      ∀ z ∈ s, b z 0=z.2 ∧
      (∀ r, |r| ≤ 1/4 → liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1)) ∧
      (∀ r, |r| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)| ≤
          8/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) ∧
      (∀ r t, |r| ≤ 1/4 → |t| ≤ 1/4 → ∀ i : Fin n,
        |liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)| ≤
          24*|r-t|/growthBase k^((4/5:ℝ)*((i:ℝ)+1))) := by
  classical
  let S := s ×ˢ Icc (-(1/4:ℝ)) (1/4)
  let ξ : ((ℝ × ℝ) × ℝ) → Fin n → ℝ := fun z => if hz : z ∈ S then
    (nonlinear_dirichlet_fixedPoint k z.1.1 z.1.2 z.2 n hk (abs_le.mpr hz.2) hq hsmall (hU z.1 hz.1)).choose else 0
  have hξb (z : (ℝ × ℝ) × ℝ) (hz : z ∈ S) (i : Fin n) :
      |ξ z i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)) := by
    simpa only [ξ,dite_eq_left hz] using
      (nonlinear_dirichlet_fixedPoint k z.1.1 z.1.2 z.2 n hk (abs_le.mpr hz.2) hq hsmall (hU z.1 hz.1)).choose_spec.1 i
  have hξ (z : (ℝ × ℝ) × ℝ) (hz : z ∈ S) (i : Fin n) :
      ξ z i=dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) (i+1)*z.2+
        ∑ j, greenMatrix (orbitCoefficient k z.1.1 z.1.2) n i j *
          (-(phi k (liftedOrbit k z.1.1 z.1.2 (j+1)+ξ z j)-
            phi k (liftedOrbit k z.1.1 z.1.2 (j+1))-
            potential k (liftedOrbit k z.1.1 z.1.2 (j+1))*ξ z j)) := by
    simpa only [ξ,dite_eq_left hz] using
      (nonlinear_dirichlet_fixedPoint k z.1.1 z.1.2 z.2 n hk (abs_le.mpr hz.2) hq hsmall (hU z.1 hz.1)).choose_spec.2 i
  let b : (ℝ × ℝ) → ℝ → ℝ := fun z r => z.2+ξ (z,r) ⟨0,hn⟩
  have hcont : ContinuousOn ξ S := continuousOn_nonlinear_dirichlet_corrections k n hk hq hsmall S ξ
    (fun z hz => ht z.1 hz.1) (fun z hz => hU z.1 hz.1) hξb hξ
  have horb (z : ℝ × ℝ) (hz : z ∈ s) (r : ℝ) (hr : |r| ≤ 1/4) :
      liftedOrbit k (z.1+r) (b z r) (n+1)=liftedOrbit k z.1 z.2 (n+1) ∧
      ∀ i : Fin n, liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k z.1 z.2 (i+1)=ξ (z,r) i := by
    have hz' : (z,r) ∈ S := ⟨hz,abs_le.mp hr⟩
    obtain ⟨b',he,hξ'⟩:=nonlinear_fixedPoint_orbit k z.1 z.2 r n (ht z hz) (ξ (z,r)) (hξ (z,r) hz')
    have h0:=hξ' ⟨0,hn⟩
    change b'-z.2=ξ (z,r) ⟨0,hn⟩ at h0
    have hb' : b'=b z r := by dsimp only [b]; linarith
    subst b'
    exact ⟨he,hξ'⟩
  refine ⟨b,((continuous_snd.comp continuous_fst).continuousOn).add
    (continuousOn_pi.mp hcont ⟨0,hn⟩),?_⟩
  intro z hz
  have hξ0 : ξ (z,0)=0 := by
    have hp : 0 < growthBase k := by have := growthBase_ge_four k hk; linarith
    have hz0 : (z,(0:ℝ)) ∈ S := ⟨hz,by norm_num⟩
    have hh:=nonlinear_fixedPoint_stability k z.1 z.2 n hk hq hsmall (hU z hz) 0 0 (ξ (z,0)) 0
      (hξb (z,0) hz0) (fun i => by simpa using (div_nonneg (by norm_num : (0:ℝ) ≤ 8) (Real.rpow_pos_of_pos hp _).le))
      (hξ (z,0) hz0) (fun i => by simp)
    funext i
    have hi:=hh i
    simpa using (abs_nonpos_iff.mp (by simpa using hi) : ξ (z,0) i=0)
  refine ⟨by simp [b,hξ0],fun r hr => (horb z hz r hr).1,?_,?_⟩
  · intro r hr i
    rw [(horb z hz r hr).2 i]
    exact hξb (z,r) ⟨hz,abs_le.mp hr⟩ i
  · intro r t hr ht' i
    have hh:=nonlinear_fixedPoint_stability k z.1 z.2 n hk hq hsmall (hU z hz) r t (ξ (z,r)) (ξ (z,t))
      (hξb (z,r) ⟨hz,abs_le.mp hr⟩) (hξb (z,t) ⟨hz,abs_le.mp ht'⟩)
      (hξ (z,r) ⟨hz,abs_le.mp hr⟩) (hξ (z,t) ⟨hz,abs_le.mp ht'⟩) i
    have he : liftedOrbit k (z.1+r) (b z r) (i+1)-liftedOrbit k (z.1+t) (b z t) (i+1)=ξ (z,r) i-ξ (z,t) i := by
      rw [← (horb z hz r hr).2 i,← (horb z hz t ht').2 i]; ring
    rwa [he]
end StandardMapEntropy

end OAI
