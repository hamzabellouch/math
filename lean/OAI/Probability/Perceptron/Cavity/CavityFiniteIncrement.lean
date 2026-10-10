import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityOldExpectation

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem cavity_finite_increment_lower (n k M d : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (v : ℕ→ℝ) {C : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C) :
    Real.log ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))-
      Real.pi*cavityBulkCovarianceError n (k+1) C (3*((k+1:ℕ)+1))-
      cavityOldError n k M d f h1 h2 h3-
      ‖f.d1‖*d*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ)+
      cavityBulkFullLog k d n M f v ≤
      bulkExpectedLog (n+(k+1)) (M+d) f.f v-bulkExpectedLog n M f.f v := by
  have hs:=cavity_expected_shell_restriction n (k+1) (M+d) f.f v hC hv hp
  have hf:=cavity_fresh_expected_lower n (k+1) M d f v hp
  have ho:=cavity_proxy_expected_lower n k M d f h1 h2 h3 hn hp v
  simp only [Nat.cast_add,Nat.cast_one] at *
  linarith

def cavityUniformError (n k M D : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (C KC : ℝ) : ℝ :=
  Real.pi*cavityBulkCovarianceError n (k+1) C (3*((k+1:ℕ)+1))+
  Real.exp (2*(D*‖f.f‖+((k+1:ℕ)+1)*KC/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
    Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2)+
  (∫ y : Fin M→Spin (k+1),∑ i,cavityRemainderMajorant
    (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) (n+1:ℕ) ‖y i‖
    ∂Measure.pi (fun _=>stdGaussian (Spin (k+1))))+
  ‖f.d1‖*D*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ)

lemma cavityUniformError_tendsto (k D : ℕ) (M : ℕ→ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (C KC : ℝ) {α : ℝ}
    (hM : Tendsto (fun n=>(M n:ℝ)/(n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n=>cavityUniformError n k (M n) D f h1 h2 h3 C KC) atTop (𝓝 0) := by
  have hc:=(cavityBulkCovarianceError_tendsto (k+1) C (by positivity : (0:ℝ)≤3*((k+1:ℕ)+1))).const_mul Real.pi
  have hq:=cavity_quadratic_cost_tendsto_zero M ‖f.d1‖ ‖f.d2‖
    (D*‖f.f‖+((k+1:ℕ)+1)*KC/2) ((k+1:ℕ)+1) α hM
  have hr:=cavityRemainderMajorant_row_tendsto M (k+1)
    (cavityRemainderCoefficients f h1 h2 h3 (k+1) ((k+1)+1)) hM
  have hN : Tendsto (fun n : ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hf:=(tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hN)).const_mul
    (‖f.d1‖*D*((k+1:ℕ)+1)*(1+Real.sqrt (k+1)))
  convert ((hc.add hq).add hr).add hf using 1 <;>
    simp [cavityUniformError,div_eq_mul_inv]

lemma cavity_finite_increment_uniform (n k M d D : ℕ) (f : Jet3)
    (h1 : HasCompactSupport (f.d1 : ℝ→ℝ)) (h2 : HasCompactSupport (f.d2 : ℝ→ℝ))
    (h3 : HasCompactSupport (f.d3 : ℝ→ℝ)) (hn : 2*((k+1)+1)≤n+1)
    (hp : (cavitySphereLaw n (k+1) : Measure (Spin (k+1))) (cavityShell (k+1))≠0)
    (v : ℕ→ℝ) {C KC : ℝ} (hC : 0≤C) (hv : ∀ j,|v (j+1)|≤C)
    (hd : d≤D) (hK : M/(n+1:ℕ)*‖f.dilationMark h1‖≤KC) :
    Real.log ((cavitySphereLaw n (k+1) : Measure (Spin (k+1))).real (cavityShell (k+1)))-KC/2-
      cavityUniformError n k M D f h1 h2 h3 C KC+cavityBulkFullLog k d n M f v ≤
      bulkExpectedLog (n+(k+1)) (M+d) f.f v-bulkExpectedLog n M f.f v := by
  have hinc:=cavity_finite_increment_lower n k M d f h1 h2 h3 hn hp v hC hv
  have hd' : (d:ℝ)≤D:=by exact_mod_cast hd
  have hE : d*‖f.f‖+((k+1:ℕ)+1)*(M/(n+1:ℕ)*‖f.dilationMark h1‖)/2≤
      D*‖f.f‖+((k+1:ℕ)+1)*KC/2 := by gcongr
  have hq :
      Real.exp (2*(d*‖f.f‖+((k+1:ℕ)+1)*(M/(n+1:ℕ)*‖f.dilationMark h1‖)/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2) ≤
      Real.exp (2*(D*‖f.f‖+((k+1:ℕ)+1)*KC/2)+(Real.sqrt (n+1:ℕ))⁻¹^2*((k+1:ℕ)+1)^2*M*‖f.d1‖^2)*
        Real.sqrt ((1/(2*(n+1:ℕ)))^2*(((k+1:ℕ)+1)^2)^2*squareGaussianVariance*M*‖f.d2‖^2) := by
    gcongr
  have hf : ‖f.d1‖*d*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ)≤
      ‖f.d1‖*D*((k+1:ℕ)+1)*(1+Real.sqrt (k+1))/Real.sqrt (n+1:ℕ) := by gcongr
  dsimp only [cavityOldError] at hinc
  dsimp only [cavityUniformError]
  simp only [Nat.cast_add,Nat.cast_one] at *
  linarith


lemma cavitySplitPartition_lower (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : Fin M→Spin (n+1)) (b : Fin d→Fin (m+1)→ℝ)
    {KC : ℝ} (hC : ∀ x,|bulkC (m+1) M f a.1 x|≤KC) :
    Real.exp (-(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2) ≤ cavitySplitPartition n d m M f v (a,y,b) := by
  let μ:=tiltLaw (unitSphereLaw (m+1)) (bulkHamiltonian (m+1) M f.f v a.1 a.2) 1
  have : IsProbabilityMeasure μ := tilt_law_probability_of_integrable _
    (by simpa only [one_mul] using bulkHamiltonian_exp_integrable m M f.f v a)
  let F:=fun x : NormalizedSpin (m+1)=>Real.exp (normalizedPatternEnergy (m+1) d f.f b x+
    (n+1:ℕ)*bulkC (m+1) M f a.1 x/2)*
    sphericalExp n (cavityVectorField M (n+1) (fun t=>f.d1 (∑ i,a.1 t i*x.val i))
      (Real.sqrt (m+1:ℕ))⁻¹ y) (Real.sqrt (n+1:ℕ))
  have hw : Continuous (normalizedPatternEnergy (m+1) d f.f b) :=
    (normalizedPatternEnergy_continuous (m+1) d f.f).comp (continuous_const.prodMk continuous_id)
  have hc : Continuous (bulkC (m+1) M f a.1) := by unfold bulkC; fun_prop
  have hv : Continuous (fun x : NormalizedSpin (m+1)=>cavityVectorField M (n+1)
      (fun t=>f.d1 (∑ i,a.1 t i*x.val i)) (Real.sqrt (m+1:ℕ))⁻¹ y) := by
    unfold cavityVectorField
    fun_prop
  have hi : Integrable F μ := ((hw.add ((continuous_const.mul hc).div_const 2)).rexp.mul
    ((sphericalExp_continuous n _).comp hv)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  change _≤∫ x,F x ∂μ
  calc
    _=(∫ _ : NormalizedSpin (m+1),Real.exp (-(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2) ∂μ) := by simp
    _≤_ := integral_mono (integrable_const _) hi (fun x=>by
      have hb:=(abs_le.mp (normalizedPatternEnergy_bound (m+1) d f.f b x)).1
      have hc':=(abs_le.mp (hC x)).1
      have hs := mul_le_mul_of_nonneg_left hc' (show (0:ℝ)≤(n+1:ℕ) from by positivity)
      dsimp only [F]
      calc
        _≤Real.exp (normalizedPatternEnergy (m+1) d f.f b x+(n+1:ℕ)*bulkC (m+1) M f a.1 x/2) :=
          Real.exp_le_exp.mpr (by nlinarith)
        _≤_ := le_mul_of_one_le_right (Real.exp_pos _).le (one_le_sphericalExp n _ _))

lemma cavitySplitLog_lower (n d m M : ℕ) (f : Jet3) (v : ℕ→ℝ)
    (a : BulkDisorder (m+1) M) (y : Fin M→Spin (n+1)) (b : Fin d→Fin (m+1)→ℝ)
    {KC : ℝ} (hC : ∀ x,|bulkC (m+1) M f a.1 x|≤KC) :
    -(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2 ≤ Real.log (cavitySplitPartition n d m M f v (a,y,b)) := by
  have h:=cavitySplitPartition_lower n d m M f v a y b hC
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h

lemma cavityBulkFullLog_lower (n d m M : ℕ) (f : Jet3)
    (hf : HasCompactSupport (f.d1 : ℝ→ℝ)) (v : ℕ→ℝ)
    {KC : ℝ} (hC : ∀ (a : BulkDisorder (m+1) M) x,|bulkC (m+1) M f a.1 x|≤KC) :
    -(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2 ≤ cavityBulkFullLog n d m M f v := by
  let G:=fun p : CavityProxyRandom m (n+1) M d=>Real.log (cavitySplitPartition n d m M f v (p.1,p.2.2,p.2.1))
  have hi : Integrable G (cavityProxyLaw m (n+1) M d):=cavitySplitLog_proxy_integrable m n M d f hf v
  have he: (∫ p,G p ∂cavityProxyLaw m (n+1) M d)=cavityBulkFullLog n d m M f v := by
    unfold cavityProxyLaw
    rw [cavity_three_integral _ _ _ G hi,cavityBulkFullLog_split n d m M f hf v]
  rw [←he]
  calc
    _=(∫ _ : CavityProxyRandom m (n+1) M d,-(d:ℝ)*‖f.f‖-(n+1:ℕ)*KC/2 ∂cavityProxyLaw m (n+1) M d) := by simp
    _≤_ := integral_mono (integrable_const _) hi (fun p=>cavitySplitLog_lower n d m M f v p.1 p.2.2 p.2.1 (hC p.1))
end SphericalPerceptronFreeEnergy

end

end OAI
