import OAI.NumberTheory.DirichletL.Descent.FirstModeColumns

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation
open MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstModeIdealRows (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (C₁ C₂ : Finset ι → ℂ) (d h : Eis) (a : Fin 7 → ℝ)
    (y₁ y₂ : Finset ι → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
    idealPairReindex p hg F
      (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
        (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
      (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
        (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h

theorem first_gauss_common_integral
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (R : ℝ)
    (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
      ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
        firstPoissonProfile W₁ W₂ Φ V R (firstCoordinates a (y₁ N) (y₂ P)) else 0) =
    ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
      firstModeIdealRows p hp hcop hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z := by
  let coeff := fun j : Finset ι × Finset ι => if Disjoint j.1 j.2 then
    threeGaussRowFactor p hp hcop hg j.1 j.2 B v ε₁ ε₂ C₁ C₂ d h else 0
  let coord := fun j : Finset ι × Finset ι => firstCoordinates a (y₁ j.1) (y₂ j.2)
  calc
    _ = ∑ j ∈ F.powerset ×ˢ F.powerset, coeff j *
        ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (coord j) z.1 z.2 := by
      simp only [Finset.sum_product,coeff,coord]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : Disjoint N P <;> simp [hd,he]
    _ = ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
        ∑ j ∈ F.powerset ×ˢ F.powerset, coeff j *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (coord j) z.1 z.2 :=
      full_density_finite_sum _ g b₁ b₂ b₃ _ _ _ coeff coord
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      simp only [Finset.sum_product,coeff,coord,ite_mul,zero_mul]
      exact actual_first_mode_ideal_rows p hp hcop hg hinj hc hpr F B hFB
        v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z

theorem first_gauss_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs₁ : Function.support W₁ ⊆ Set.Icc lo hi)
    (hs₂ : Function.support W₂ ⊆ Set.Icc lo hi)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ,ℂ)) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b₃ : 𝓢(ℝ,ℂ),
      (∀ (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
        (F B : Finset ι), Disjoint F B → ∀ (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (C₁ C₂ : Finset ι → ℂ) (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ),
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
            firstPoissonProfile W₁ W₂ Φ V R (firstCoordinates a (y₁ N) (y₂ P)) else 0) =
        ∫ z : Frequency × (Fin 9 → ℝ),
          fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
          firstModeIdealRows p hp hcop hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z) ∧
      Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
        tripleHeight J z.1 * coordinateHeight J z.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ∧
      (1+R)^A * (∫ z : Frequency × (Fin 9 → ℝ),
        tripleHeight J z.1 * coordinateHeight J z.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hs⟩ := first_full_profile_common_measure
    W₁ W₂ lo hi hlo hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,hI,hB⟩ := hs R hR
  refine ⟨b₃,?_,hI,hB⟩
  intro hinj hc hpr F B hFB v ε₁ ε₂ C₁ C₂ d h a y₁ y₂
  apply first_gauss_common_integral p hp hcop hg hinj hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ W₁ W₂ Φ V R
    (firstRootSchwartz V hV hS) b₁ b₂ b₃
  intro y
  rw [full_density_mode_fubini]
  simpa only [pureProfileMode_height] using he y

end
end SevenEighths.InverseMoment

end OAI
