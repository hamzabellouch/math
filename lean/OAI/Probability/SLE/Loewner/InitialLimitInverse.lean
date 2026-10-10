import OAI.Probability.SLE.Loewner.InitialInverseRange
import OAI.Probability.SLE.Loewner.SlitChartFarHeight
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

namespace OAI

/-! The inverse of a terminal inverse-chart limit is holomorphic and retains
the common far-height bound. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialForwardChart_far_height (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R)
    (t : unitInterval) {z : ℂ} (hz : 2*R≤z.im) :
    ‖initialForwardChart p hi h0 hH t z-z‖≤3*R^2/z.im := by
  by_cases ht : t=0
  · simp only [ht,initialForwardChart_zero,id_eq,sub_self,norm_zero]
    exact div_nonneg (by positivity) (by linarith)
  · rw [initialForwardChart,dite_eq_right ht]
    exact (initialSlitChart p hi h0 hH t ht).far_height_displacement hR
      (fun u => hp (t*u)) hz

lemma initialInverse_limit_forward_subsequence (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ z∈upperHalfPlane \ range p,
      Tendsto (fun n => initialForwardChart p hi h0 hH (t (φ n)) z)
        atTop (𝓝 (invFunOn F upperHalfPlane z)) := by
  have hcov : SurjOn F upperHalfPlane (upperHalfPlane \ range p) :=
    initialInverse_limit_covers_final_domain p hi h0 hH hF hlim
  have hinj := initialInverse_limit_injOn p hi h0 hH hlim
  obtain ⟨φ,A,hφ,hA,hAlim⟩ := initialForwardCayley_subsequence p hi h0 hH t
  refine ⟨φ,hφ,fun z hz => ?_⟩
  have hw := halfPlaneCayleyInv_open
    (initialForwardCayley_limit_interior p hi h0 hH hA hAlim z hz)
  have hfwd := initialForward_limit_tendsto p hi h0 hH hA hAlim hz
  have heval := locallyUniform_evaluation_tendsto isOpen_upperHalfPlane
    hF.continuousOn (locallyUniform_reindex hlim hφ.tendsto_atTop) hw hfwd
  have he : F (halfPlaneCayleyInv (A z))=z := by
    apply tendsto_nhds_unique heval
    simpa only [initialInverse_forward_on_final p hi h0 hH _ hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
  have hwG : halfPlaneCayleyInv (A z)=invFunOn F upperHalfPlane z := by
    apply hinj hw (hcov.mapsTo_invFunOn hz)
    exact he.trans (hcov.rightInvOn_invFunOn hz).symm
  rwa [hwG] at hfwd

lemma initialInverse_limit_inverse_far_height (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ u : unitInterval, ‖p u‖≤R)
    {z : ℂ} (hz : 2*R≤z.im) :
    ‖invFunOn F upperHalfPlane z-z‖≤3*R^2/z.im := by
  have hzD : z∈upperHalfPlane \ range p := by
    refine ⟨by change 0<z.im; linarith,?_⟩
    rintro ⟨u,hu⟩
    have hn := (Complex.im_le_norm z).trans (hu ▸ hp u)
    linarith
  obtain ⟨φ,_,hφ⟩ := initialInverse_limit_forward_subsequence p hi h0 hH hF hlim
  exact le_of_tendsto ((hφ z hzD).sub_const z).norm
    (Eventually.of_forall fun n => initialForwardChart_far_height p hi h0 hH hR hp _ hz)

lemma initialInverse_limit_uniform_displacement (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {z : ℂ} (hz : z∈upperHalfPlane) :
    ‖F z-z‖ ≤ initialCapacity p hi h0 hH 1/z.im := by
  apply le_of_tendsto ((hlim.tendsto_at hz).sub_const z).norm
  exact Eventually.of_forall fun n => (initialInverseChart_displacement p hi h0 hH (t n) hz).trans
    (div_le_div_of_nonneg_right (initialCapacity_monotone p hi h0 hH (show t n≤1 from le_top))
      (show 0<z.im from hz).le)

end SLEExactGauge

end

end OAI
