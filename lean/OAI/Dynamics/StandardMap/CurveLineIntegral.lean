import OAI.Dynamics.StandardMap.CurveColumns

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology ENNReal Classical BigOperators
namespace StandardMapEntropy
lemma cell_line_lintegral (k ε δ : ℝ) (hk : 0≤k) (hε : 0≤ε) (hδ0 : 0≤δ)
    (hδ1 : δ≤1) (hδ : 6*δ≤ε) (hε1 : 2*Real.pi*ε≤1) (hε2 : growthBase k*ε≤1)
    (N : ℕ) (hN : 0<N) (hN2 : 2*growthBase k≤(N:ℝ)^2)
    (g:ℝ → CurvePlane) (u:CurvePlane) (hu:‖u‖≤1) (hv : ∀t,HasDerivAt g u t)
    (J : CurveInterval) (hJ:J.length≤ε)
    (c : ℕ → CurvePlane) (n : ℕ) (S : Set ℝ) (hS : S⊆Icc J.left J.right)
    (hword : ∀s∈S,∀j<n,wrappedBox δ (c j) ((liftStep k)^[j+1] (g s))) :
    (∫⁻s in S,ENNReal.ofReal ‖curveIterVelocity k g (fun _=>u) n s‖)≤
      ((196*N:ℕ):ℝ≥0∞)^n*ENNReal.ofReal ε := by
  obtain ⟨C,hC,_⟩:=restricted_controlled_curve ε hε g (fun _=>u) hv continuous_const
    (by intro s hs t ht; simp only [sub_self,norm_zero]; positivity) J (by
      intro t ht
      rw [J.velocity_norm]
      exact (mul_le_mul_of_nonneg_left hu J.length_nonneg).trans (by simpa only [mul_one] using hJ))
  exact cell_curve_lintegral k ε δ hk hε hδ0 hδ1 hδ hε1 hε2 N hN hN2 g (fun _=>u) hv J C hC c n S hS hword
end StandardMapEntropy

end OAI
