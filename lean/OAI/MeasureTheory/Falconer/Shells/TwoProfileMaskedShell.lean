import OAI.MeasureTheory.Falconer.Recursion.TwoProfileInverseScalar
import OAI.MeasureTheory.Falconer.Shells.EndpointWeightedDistance
import OAI.MeasureTheory.Falconer.Fourier.BaseJetAmplitude

namespace OAI

/-! # The scalar shell for two actual descriptor products

The Fourier law is formed from the original two measures. Its inverse
terms keep the two profile and descriptor data throughout the shell bound.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

 theorem exists_two_profile_masked_shell_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ k : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ L : ℕ,
      ∃ A B : Fin (k+1) → ℝ, (∀ j, 1 ≤ A j) ∧ (∀ j, 1 ≤ B j) ∧
      ∀ R E δ W C₀ : ℝ, 1 ≤ R → 1 ≤ E → E ≤ R^2 → ∀ (hδ : 0 < δ) (hW : 0 < W), 1 ≤ C₀ →
      ∀ (Q₁ Q₂ : DyadicCube (n+3)) (ρ₁ ρ₂ : Measure (Space (n+3)))
        (profile₁ profile₂ : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
        (F G : Finset PolicyDescriptor) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (n+3))),
      (∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      (∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      ∀ (μ ν : Measure (Space (n+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
        (M P s : ℝ), 0 < M → 0 < P → 0 < s →
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ x y l, l ≤ 2*(k+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ l (fun t =>
          (descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁ x t : ℂ)*
          (descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂ y t : ℂ)) w‖ ≤ C₀*E^l) →
      ∀ U : ℝ, 0 < U → ∀ (a v : ℝ) (Ψ : ℝ → ℝ),
      Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x ≤ 0, Ψ x = 0) →
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        0 < r*s ∧ E^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a)) →
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        ∀ᵐ z ∂μ.prod ν, 1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ energy : ℝ,
      (∀ (u : DescriptorJetSymbol (n+1) (2*k) L F 1)
        (w : DescriptorJetSymbol (n+1) (2*k) L G 1),
        independentAngularEnergy a v Ψ
          (fun z => endpointTransform μ M (u.value Q₁ ρ₁ profile₁ N σ J i S₁ U) z.1 z.2)
          (fun z => endpointTransform ν P (w.value Q₂ ρ₂ profile₂ N σ J i S₂ U) z.1 z.2) ≤ energy) →
      let f := descriptorRootSymbol (n+1) F (L+2*k)
      let g := descriptorRootSymbol (n+1) G (L+2*k)
      let left := descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁
      let right := descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂
      (2:ℝ)^(-a) * (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
        ‖charFun (endpointWeightedDistance μ ν M P s left right) r‖^2) ≤
        2*(descriptorInverseShellCost f g k A B 1 1 U δ W hδ hW*energy)+
        2*(2:ℝ)^(v-a)*
          (|M⁻¹*P⁻¹| *((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*(μ.prod ν).real univ))^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  obtain ⟨k,A₀,hA₀,hrem⟩ := exists_integrated_scaled_inverse_order hgnomonic hquadratic n (T := T) hκ
  refine ⟨k,A₀,hA₀,?_⟩
  intro L
  choose A B hA hB hfamily using fun j : Fin (k+1) => exists_descriptorInverseSymbols n j.val L
  refine ⟨A,B,hA,hB,?_⟩
  intro R E δ W C₀ hR hE hER hδ hW hC₀ Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i F G S₁ S₂
    hsepF hsepG hFE hGE μ ν _ _ M P s hM hP hs hsep hnear hderiv U hU a v Ψ hΨ hpos hzero hone _
    hregime hfreq energy henergy
  let f := descriptorRootSymbol (n+1) F (L+2*k)
  let g := descriptorRootSymbol (n+1) G (L+2*k)
  let family (j : Fin (k+1)) : DescriptorInverseSymbols f g j.val L (A j) (B j) :=
    Classical.choice (hfamily j 0 0 (L+2*k) F G 1 f g (by norm_num) (by have := j.isLt; omega))
  let left := descriptorAmbientProduct Q₁ ρ₁ profile₁ N σ J i F S₁
  let right := descriptorAmbientProduct Q₂ ρ₂ profile₂ N σ J i G S₂
  have hleft (x t : Space (n+3)) : f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ 1 x t = (left x t : ℂ) := by
    simp only [f,descriptorRootSymbol,DescriptorJetSymbol.base_ambient,inv_one,
      Complex.ofReal_one,mul_one,left]
  have hright (x t : Space (n+3)) : g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ 1 x t = (right x t : ℂ) := by
    simp only [g,descriptorRootSymbol,DescriptorJetSymbol.base_ambient,inv_one,
      Complex.ofReal_one,mul_one,right]
  have hInt (r : ℝ) := two_profile_scaled_inverse_integrable k L A B family (by norm_num)
    (fun j => zero_lt_one.trans_le (hA j)) (fun j => zero_lt_one.trans_le (hB j))
    Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hsepF hsepG 1 1 hU δ hδ s μ ν
    (hsep.mono fun _ hz => hz.1) r
  have hleftB (x t) : left x t ∈ Icc (0:ℝ) 1 :=
    descriptorAmbientProduct_global_bounds Q₁ ρ₁ profile₁ N σ J i F S₁ x t
  have hrightB (x t) : right x t ∈ Icc (0:ℝ) 1 :=
    descriptorAmbientProduct_global_bounds Q₂ ρ₂ profile₂ N σ J i G S₂ x t
  have hmleft : Measurable (Function.uncurry left) := descriptorAmbientProduct_measurable _ _ _ _ _ _ _ _ _
  have hmright : Measurable (Function.uncurry right) := descriptorAmbientProduct_measurable _ _ _ _ _ _ _ _ _
  let := endpointWeightedDistance_finite (by omega : 1 ≤ n+3) μ ν hM hP hδ left right hleftB hrightB
    (hsep.mono fun _ hz => hz.1)
  have hscalar := scalar_shell_of_two_profile_inverse k L A B family (by norm_num)
    (fun j => zero_lt_one.trans_le (hA j)) (fun j => zero_lt_one.trans_le (hB j))
    Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hsepF hsepG 1 1 hU hE hE hFE hGE δ W hδ hW
    hs μ ν hsep hM hP a v Ψ hΨ hpos hzero hone hregime energy
    (by
      intro u w
      exact henergy (u.relax (by omega) le_rfl (by norm_num) le_rfl)
        (w.relax (by omega) le_rfl (by norm_num) le_rfl))
    (charFun (endpointWeightedDistance μ ν M P s left right)) measurable_charFun
    (ε := |M⁻¹*P⁻¹| *((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*(μ.prod ν).real univ))
  have hb := hscalar (by
    filter_upwards [hfreq] with r hr
    rw [norm_sub_rev,endpointWeightedDistance_fourier n μ ν hM hP hs left right hmleft hmright
      (fun x w => (hleftB x w).1) (fun x w => (hrightB x w).1)]
    simp only [hleft,hright]
    apply hrem R E s r δ hR hE hER hs hδ μ ν (hsep.mono fun _ hz => hz.1) hnear hr
      (fun x y w => (left x w : ℂ)*(right y w : ℂ))
    · exact (hmleft.comp (measurable_fst.fst.prodMk measurable_snd)).complex_ofReal |>.mul
        (hmright.comp (measurable_fst.snd.prodMk measurable_snd)).complex_ofReal
    · intro x y
      exact (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff _ _ _ _ _ _ _ _ _ x)).mul
        (Complex.ofRealCLM.contDiff.comp (descriptorAmbientProduct_contDiff _ _ _ _ _ _ _ _ _ y))
    · exact zero_le_one.trans hC₀
    · intro x y w
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hleftB x w).1,
        abs_of_nonneg (hrightB y w).1]
      exact (mul_le_mul (hleftB x w).2 (hrightB y w).2 (hrightB y w).1 (by norm_num)).trans
        (by simpa only [one_mul] using hC₀)
    · exact hderiv
    · simpa only [hleft,hright] using hInt r)
  exact hb.2

end Falconer

end OAI
