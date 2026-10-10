import OAI.Dynamics.StandardMap.CurveIntegral

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma cell_curve_lintegral (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g v : ℝ → CurvePlane) (hv : ∀t,HasDerivAt g (v t) t)
    (J : CurveInterval) (C : ControlledCurve ε) (hC : C.map=g ∘ J.parameter)
    (c : ℕ → CurvePlane) (n : ℕ) (S : Set ℝ) (hS : S⊆Icc J.left J.right)
    (hword : ∀s∈S,∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g s))) :
    (∫⁻s in S,ENNReal.ofReal ‖curveIterVelocity k g v n s‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
  obtain ⟨I,D,hcover,hmap⟩:=curve_iterate_cover k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 C c n
  let K:CurveTree N n → CurveInterval:=fun b=>J.comp (I b)
  have hD:∀b,(D b).map=(liftStep k)^[n] ∘ g ∘ (K b).parameter := by
    intro b
    rw [hmap,hC]
    funext t
    simp only [Function.comp_apply,K,CurveInterval.comp_parameter]
  have hK:∀s∈S,∃b,s∈Icc (K b).left (K b).right := by
    intro s hs
    obtain ⟨t,ht,hts⟩:=J.parameter_range.superset (hS hs)
    have hw:∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (C.map t)) := by
      intro j hj
      rw [hC]
      simpa only [Function.comp_apply,hts] using hword s hs j hj
    obtain ⟨a,ha⟩:=hcover t ht hw
    refine ⟨a,?_⟩
    rw [← hts]
    exact J.comp_mem (I a) ha
  have h:=curve_cover_lintegral_speed K (curveIterVelocity k g v n) ε hε
    (fun b=>controlled_curve_speed_from_map _ _ (curveIter_hasDeriv k g v hv n) ε (K b) (D b) (hD b)) S hK
  simpa only [curveTree_card,Nat.cast_pow] using h
end StandardMapEntropy

end OAI
