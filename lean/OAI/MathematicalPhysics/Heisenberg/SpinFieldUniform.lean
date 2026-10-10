import OAI.MathematicalPhysics.Heisenberg.SpinCubeAverage

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
lemma metric_triangle5 {E : Type*} [PseudoMetricSpace E] (a b c d e : E) :
    dist a e≤dist a b+dist b c+dist c d+dist d e :=
  (dist_triangle a d e).trans (add_le_add (dist_triangle4 a b c d) le_rfl)
variable {d ℓ : ℕ}

lemma field_local_small (F : Finset (Site d)) (B : QuasiLocal d ℓ)
    (hB : B∈localAlgebra d ℓ (F : Set (Site d))) (K : Set ℝ) (hK : IsCompact K)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧ ∀ Γ : Finset (Site d),F⊆Γ →
      ∀ h : ℝ,|h|<δ → ∀ t∈K,
        dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)<ε := by
  have hc : ContinuousAt (fun s : ℝ=>GibbsStrip.evolve (totalZ (ℓ:=ℓ) F) (s:ℂ) B) 0 :=
    (GibbsStrip.evolve_differentiable _ _).continuous.continuousAt.comp Complex.continuous_ofReal.continuousAt
  obtain ⟨η,hη,hsmall⟩:=Metric.continuousAt_iff.mp hc ε hε
  obtain ⟨M,hM⟩:=hK.exists_bound_of_continuousOn continuous_id.continuousOn
  refine ⟨η/(|M|+1),by positivity,?_⟩
  intro Γ hΓ h hh t ht
  rw [shiftedField_evolve,local_field_evolve hΓ hB,(finiteDynamics_isometry d ℓ Γ t).dist_eq]
  have htime : dist (-h*t) 0<η := by
    rw [Real.dist_eq,sub_zero,abs_mul,abs_neg]
    have htM : |t|≤|M|+1:=(hM t ht).trans ((le_abs_self M).trans (by linarith [abs_nonneg M]))
    exact (mul_le_mul_of_nonneg_left htM (abs_nonneg h)).trans_lt ((lt_div_iff₀ (by positivity : 0 < |M|+1)).mp hh)
  simpa only [Complex.ofReal_zero,GibbsStrip.evolve,mul_zero,neg_zero,zero_smul,NormedSpace.exp_zero,one_mul,mul_one] using hsmall htime

theorem field_deep_uniform (A : QuasiLocal d ℓ) (K : Set ℝ) (hK : IsCompact K)
    {ε : ℝ} (hε : 0<ε) : ∃ r : ℕ,∃ δ : ℝ,0<δ ∧
      ∀ Γ : Finset (Site d),box d r⊆Γ → ∀ h : ℝ,|h|<δ → ∀ t∈K,
        dist (GibbsStrip.evolve (shiftedField Γ h) t A) (dynamics d ℓ t A)<ε := by
  obtain ⟨B,hB,hAB⟩:=(localCore_dense d ℓ).exists_dist_lt A (show 0<ε/8 by positivity)
  obtain ⟨F,hF⟩:=localCore_finite_support hB
  obtain ⟨r₀,hr₀⟩:=(eventually_subset_box F).exists
  obtain ⟨r₁,hr₁⟩:=finiteDynamics_deep_uniform d ℓ A K hK (show 0<ε/4 by positivity)
  obtain ⟨δ,hδ,hfield⟩:=field_local_small F B hF K hK (show 0<ε/4 by positivity)
  refine ⟨max r₀ r₁,δ,hδ,?_⟩
  intro Γ hΓ h hh t ht
  have hFΓ : F⊆Γ :=hr₀.trans ((box_mono (le_max_left r₀ r₁)).trans hΓ)
  have hdeep : box d r₁⊆Γ :=(box_mono (le_max_right r₀ r₁)).trans hΓ
  calc _ ≤ dist (GibbsStrip.evolve (shiftedField Γ h) t A) (GibbsStrip.evolve (shiftedField Γ h) t B)+
      dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)+
      dist (finiteDynamics d ℓ Γ t B) (finiteDynamics d ℓ Γ t A)+
      dist (finiteDynamics d ℓ Γ t A) (dynamics d ℓ t A) := metric_triangle5 _ _ _ _ _
       _ = dist A B+dist (GibbsStrip.evolve (shiftedField Γ h) t B) (finiteDynamics d ℓ Γ t B)+dist B A+
         dist (finiteDynamics d ℓ Γ t A) (dynamics d ℓ t A) := by
           rw [GibbsStrip.real_evolve_dist _ (shiftedField_selfAdjoint Γ h), (finiteDynamics_isometry d ℓ Γ t).dist_eq]
       _ < ε := by have h1:=hfield Γ hFΓ h hh t ht; have h2:=hr₁ Γ hdeep t ht; rw [dist_comm B A]; linarith

end Heisenberg
end
end

end OAI
