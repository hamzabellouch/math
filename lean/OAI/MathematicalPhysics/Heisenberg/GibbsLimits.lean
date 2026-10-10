import OAI.MathematicalPhysics.Heisenberg.BoundedStrip

namespace OAI

noncomputable section
open scoped ComplexConjugate ENNReal Classical
open scoped ComplexConjugate BigOperators
open Filter Topology Metric
open scoped NNReal
open scoped ComplexConjugate Topology
open Set Filter Complex
open scoped Topology

namespace Heisenberg

open GibbsStrip

lemma state_apply_norm_le {d ℓ : ℕ} (ω : State d ℓ) (A : QuasiLocal d ℓ) :
    ‖ω.functional A‖ ≤ 4 * ‖A‖ :=
  (ω.functional.le_opNorm A).trans (mul_le_mul_of_nonneg_right (state_norm_bound ω) (norm_nonneg A))

lemma state_product_norm_le {d ℓ : ℕ} (ω : State d ℓ) (A B : QuasiLocal d ℓ) :
    ‖ω.functional (A*B)‖ ≤ 4*‖A‖*‖B‖ := by
  exact (state_apply_norm_le ω _).trans (by nlinarith [norm_mul_le A B])

theorem finite_gibbs_strip {d ℓ : ℕ} (τ : State d ℓ)
    (hτ : ∀ A B, τ.functional (A*B) = τ.functional (B*A))
    {K : QuasiLocal d ℓ} (hK : IsSelfAdjoint K) {β : ℝ} (hβ : 0 < β)
    (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,
      DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z ∈ HeisenbergStrip.closedStrip β, ‖F z‖ ≤ 4*‖A‖*‖B‖) ∧
      (∀ t : ℝ, F t = (gibbsState τ K β).functional (A * evolve K t B)) ∧
      (∀ t : ℝ, F ((t:ℂ)+Complex.I*β) = (gibbsState τ K β).functional (evolve K t B * A)) := by
  let ω := gibbsState τ K β
  let F : ℂ → ℂ := fun z => ω.functional (A*evolve K z B)
  have hd : Differentiable ℂ F := ω.functional.differentiable.comp
    ((evolve_differentiable K B).const_mul A)
  have hu (t : ℝ) : F ((t:ℂ)+Complex.I*β) = ω.functional (evolve K t B*A) := by
    change (gibbsState τ K β).functional (A*evolve K ((t:ℂ)+Complex.I*β) B) =
      (gibbsState τ K β).functional (evolve K t B*A)
    rw [gibbsState_apply τ hτ hK,gibbsState_apply τ hτ hK]
    simpa only [gibbsDensity,Complex.ofReal_neg] using
      gibbs_upper_boundary τ.functional hτ K β t ((τ.functional (gibbsDensity K β)).re : ℂ)⁻¹ A B
  have hb : ∃ M : ℝ, ∀ z ∈ HeisenbergStrip.closedStrip β, ‖F z‖ ≤ M := by
    obtain ⟨M,hM0,hM⟩ := strip_evolve_bounded hK B β
    refine ⟨4*‖A‖*M, fun z hz => ?_⟩
    exact (state_product_norm_le ω A _).trans
      (mul_le_mul_of_nonneg_left (hM z hz.1 hz.2) (by positivity))
  refine ⟨F,hd.diffContOnCl,?_, fun _ => rfl,hu⟩
  intro z hz
  apply HeisenbergStrip.bounded_strip_max hβ hd.diffContOnCl hb ?_ ?_ hz
  · intro w hw
    have he : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw]
    rw [he]
    exact (state_product_norm_le ω A _).trans_eq (by rw [real_evolve_norm hK])
  · intro w hw
    have he : w = (w.re:ℂ)+Complex.I*β := by apply Complex.ext <;> simp [hw]
    rw [he,hu]
    exact (state_product_norm_le ω _ A).trans_eq (by rw [real_evolve_norm hK]; ring)

open Filter Topology GibbsStrip

lemma limit_state_dynamics_locallyUniform {d ℓ : ℕ} {η : ℕ → State d ℓ}
    {ω : State d ℓ} {κ : ℕ → ℕ} (hκ : StrictMono κ)
    (hη : ∀ A, Tendsto (fun n => (η n).functional A) atTop (𝓝 (ω.functional A)))
    (M : QuasiLocal d ℓ →L[ℂ] QuasiLocal d ℓ) (B : QuasiLocal d ℓ) :
    TendstoLocallyUniformly
      (fun n t => (η n).functional (M (finiteDynamics d ℓ (box d (κ n)) t B)))
      (fun t => ω.functional (M (dynamics d ℓ t B))) atTop := by
  have hb (n : ℕ) : ‖(η n).functional.comp M‖ ≤ 4*‖M‖ :=
    ((η n).functional.opNorm_comp_le M).trans
      (mul_le_mul_of_nonneg_right (state_norm_bound (η n)) (norm_nonneg M))
  apply EquicontinuousLimits.locallyUniform
  · exact EquicontinuousLimits.equicontinuous_apply (by positivity) hb
      (fun t => (finiteDynamics_equicontinuous d ℓ B t).comp (fun n => box d (κ n)))
  · intro t
    exact EquicontinuousLimits.apply_varying (φ := atTop) (l := ω.functional.comp M) hb
      (fun A => hη (M A))
      ((dynamics_converges d ℓ t B).comp hκ.tendsto_atTop)

theorem gibbs_limit_KMS {d ℓ : ℕ} (τ : State d ℓ)
    (hτ : ∀ A B, τ.functional (A*B) = τ.functional (B*A))
    {β : ℝ} (hβ : 0 < β) {κ : ℕ → ℕ} (hκ : StrictMono κ)
    {ω : State d ℓ}
    (hω : ∀ A, Tendsto
      (fun n => (gibbsState τ (hamiltonian d ℓ (box d (κ n))) β).functional A)
      atTop (𝓝 (ω.functional A))) : IsKMS β ω := by
  refine ⟨hβ, fun A B => ?_⟩
  have hF (n : ℕ) := finite_gibbs_strip τ hτ
    (hamiltonian_selfAdjoint d ℓ (box d (κ n))) hβ A B
  choose F hd hb hzero htop using hF
  let η : ℕ → State d ℓ := fun n => gibbsState τ (hamiltonian d ℓ (box d (κ n))) β
  have hboundary₀ := limit_state_dynamics_locallyUniform hκ hω
    (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B
  have hboundaryβ := limit_state_dynamics_locallyUniform hκ hω
    ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B
  have he (n : ℕ) (t : ℝ) : evolve (hamiltonian d ℓ (box d (κ n))) t B =
      finiteDynamics d ℓ (box d (κ n)) t B := by
    simp only [evolve,finiteDynamics,mul_comm Complex.I (t:ℂ)]
  have hf₀ : TendstoLocallyUniformly (fun n (t : ℝ) => F n (t:ℂ))
      (fun t => ω.functional (A*dynamics d ℓ t B)) atTop := by
    simpa only [hzero,he,ContinuousLinearMap.mul_apply'] using hboundary₀
  have hfβ : TendstoLocallyUniformly (fun n (t : ℝ) => F n ((t:ℂ)+Complex.I*β))
      (fun t => ω.functional (dynamics d ℓ t B*A)) atTop := by
    simpa only [htop,he,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply'] using hboundaryβ
  obtain ⟨f,_,hfd,hfb,hfzero,hftop⟩ := HeisenbergStrip.bounded_strip_limit
    hβ (show 0 ≤ 4*‖A‖*‖B‖ by positivity) hd
    (fun n => ⟨_,hb n⟩)
    (fun n t => hb n t (by constructor <;> simp [hβ.le]))
    (fun n t => hb n ((t:ℂ)+Complex.I*β) (by constructor <;> simp [hβ.le]))
    hf₀ hfβ
  refine ⟨f,?_,hfd.1,⟨_,fun z h₀ htop => hfb z ⟨h₀,htop⟩⟩,hfzero,hftop⟩
  apply hfd.2.mono
  intro z hz
  rw [HeisenbergStrip.closure_openStrip hβ]
  exact hz

theorem exists_KMS (d ℓ : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ ω : State d ℓ, IsKMS β ω := by
  obtain ⟨τ,hτ⟩ := exists_tracial_state d ℓ
  obtain ⟨ω,κ,hκ,hω⟩ := state_subsequence (fun n => gibbsState τ (hamiltonian d ℓ (box d n)) β)
  exact ⟨ω,gibbs_limit_KMS τ hτ hβ hκ hω⟩

end Heisenberg
end

end OAI
