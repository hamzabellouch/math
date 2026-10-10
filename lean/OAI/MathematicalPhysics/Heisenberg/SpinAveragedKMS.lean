import OAI.MathematicalPhysics.Heisenberg.SpinAverageBoundary

namespace OAI

section
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Topology
namespace Heisenberg
variable {d ℓ : ℕ}

lemma uniform_mass {X : Type*} (Λ : Finset X) (hΛ : Λ.Nonempty) :
    ∑ _ : Λ,(Λ.card:ℝ)⁻¹=1 := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
  exact mul_inv_cancel₀ (show (Λ.card:ℝ)≠0 by exact_mod_cast Finset.card_ne_zero.mpr hΛ)

lemma uniform_sum {X : Type*} (Λ : Finset X) (f : X → ℂ) :
    (∑ x : Λ,Complex.ofReal ((Λ.card:ℝ)⁻¹)*f x.val)=(Λ.card:ℂ)⁻¹*∑ x∈Λ,f x := by
  rw [←Finset.mul_sum,Finset.sum_coe_sort Λ f]
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast]

lemma cubeBoundary_lower (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
    (A B : QuasiLocal d ℓ) (t : ℝ) :
    cubeBoundary Λ ω h (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B t=
      (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (translation d ℓ x A*
        GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)) := by
  simp only [cubeBoundary,ContinuousLinearMap.mul_apply',map_mul,translation_fieldDynamics,translated_volume_cancel]

lemma cubeBoundary_upper (Λ : Finset (Site d)) (ω : State d ℓ) (h : ℝ)
    (A B : QuasiLocal d ℓ) (t : ℝ) :
    cubeBoundary Λ ω h ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t=
      (Λ.card:ℂ)⁻¹*∑ x∈Λ,ω.functional (GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)*translation d ℓ x A) := by
  simp only [cubeBoundary,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',map_mul,translation_fieldDynamics,translated_volume_cancel]

lemma finite_cube_gibbs_strip (Λ : Finset (Site d)) (hΛ : Λ.Nonempty) (h : ℝ)
    (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    {β : ℝ} (hβ : 0<β) (A B : QuasiLocal d ℓ) :
    ∃ F : ℂ → ℂ,DiffContOnCl ℂ F (HeisenbergStrip.openStrip β) ∧
      (∀ z∈HeisenbergStrip.closedStrip β,‖F z‖≤4*‖A‖*‖B‖) ∧
      (∀ t : ℝ,F t=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
        (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B t) ∧
      (∀ t : ℝ,F ((t:ℂ)+Complex.I*β)=cubeBoundary Λ (gibbsState τ (shiftedField Λ h) β) h
        ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B t) := by
  let μ : Λ → ℝ := fun _ => (Λ.card : ℝ)⁻¹
  have hμ : ∀ i, 0 ≤ μ i := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hm : ∑ i, μ i = 1 := uniform_mass Λ hΛ
  have hh := averaged_gibbs_strip μ hμ hm (fun x : Λ => x.val) τ hτ
    (shiftedField Λ h) (shiftedField_selfAdjoint Λ h) hβ A B
  obtain ⟨F,hd,hb,h0,h1⟩ := hh
  refine ⟨F,hd,hb,?_,?_⟩
  · intro t
    exact (h0 t).trans ((uniform_sum Λ (fun x =>
      (gibbsState τ (shiftedField Λ h) β).functional
        (translation d ℓ x A * GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B)))).trans
      (cubeBoundary_lower Λ (gibbsState τ (shiftedField Λ h) β) h A B t).symm)
  · intro t
    exact (h1 t).trans ((uniform_sum Λ (fun x =>
      (gibbsState τ (shiftedField Λ h) β).functional
        (GibbsStrip.evolve (shiftedField Λ h) t (translation d ℓ x B) * translation d ℓ x A))).trans
      (cubeBoundary_upper Λ (gibbsState τ (shiftedField Λ h) β) h A B t).symm)

theorem cubeAverage_limit_KMS (τ : State d ℓ)
    (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    {β : ℝ} (hβ : 0<β) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0)) (ω : State d ℓ)
    (hω : ∀ A,Tendsto (fun n=>(cubeAverage (box d (N n)) (box_nonempty d (N n))
      (gibbsState τ (shiftedField (box d (N n)) (h n)) β)).functional A) atTop (𝓝 (ω.functional A))) : IsKMS β ω := by
  refine ⟨hβ,fun A B=>?_⟩
  choose F hd hb hzero htop using fun n=>finite_cube_gibbs_strip (box d (N n)) (box_nonempty d (N n)) (h n) τ hτ hβ A B
  let η : ℕ → State d ℓ:=fun n=>gibbsState τ (shiftedField (box d (N n)) (h n)) β
  have hl:=cubeBoundary_locallyUniform N hN h hh η ω hω (ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ) A) B
  have hu:=cubeBoundary_locallyUniform N hN h hh η ω hω ((ContinuousLinearMap.mul ℂ (QuasiLocal d ℓ)).flip A) B
  have hf0 : TendstoLocallyUniformly (fun n (t : ℝ)=>F n t) (fun t=>ω.functional (A*dynamics d ℓ t B)) atTop := by
    simpa only [hzero,ContinuousLinearMap.mul_apply',η] using hl
  have hf1 : TendstoLocallyUniformly (fun n (t : ℝ)=>F n ((t:ℂ)+Complex.I*β)) (fun t=>ω.functional (dynamics d ℓ t B*A)) atTop := by
    simpa only [htop,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',η] using hu
  obtain ⟨f,_,hfd,hfb,hfzero,hftop⟩:=HeisenbergStrip.bounded_strip_limit hβ
    (show 0≤4*‖A‖*‖B‖ by positivity) hd (fun n=>⟨4*‖A‖*‖B‖,hb n⟩)
    (fun n t=>hb n t (by constructor <;> simp [hβ.le]))
    (fun n t=>hb n ((t:ℂ)+Complex.I*β) (by constructor <;> simp [hβ.le])) hf0 hf1
  refine ⟨f,?_,hfd.1,⟨4*‖A‖*‖B‖,fun z hz0 hz1=>hfb z ⟨hz0,hz1⟩⟩,hfzero,hftop⟩
  simpa only [HeisenbergStrip.closure_openStrip hβ, HeisenbergStrip.closedStrip, Set.preimage, Set.mem_Icc] using hfd.2

end Heisenberg
end
end

end OAI
