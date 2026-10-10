import OAI.NumberTheory.DirichletL.Descent.ActualSecondMeasure

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w

def ActualSecondCommonMeasureAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hS : ∀ i, HasCompactSupport (V i))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) : Prop :=
  ∀ {κ : Type u} {ι : Type v} {σ : Type w} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (weight : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ),
    (∀ j ∈ source, (x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0) →
    (∀ j ∈ secondProfileIndices source F x, ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) →
    (∑ j ∈ source, weight j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ z : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ z *
          ∑ j ∈ secondProfileIndices source F x,
            (weight j.1 * secondActualCoefficient p hp hcop hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) z.1 z.2

theorem actual_second_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      ActualSecondCommonMeasureAt.{u,v,w} W₁ W₂ Φ V hV hS G₀ E₀ V₀ K₀ X₀ Y b₁ b₂ b₃ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hstar : ContDiff ℝ ∞ (fun t => star (W₁ t)) := Complex.conjCLE.contDiff.comp hW₁
  have hsstar : Function.support (fun t => star (W₁ t)) ⊆ Set.Icc a b := by
    intro t ht
    apply hs₁
    simpa only [Function.mem_support,star_ne_zero] using ht
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    (fun t => star (W₁ t)) W₂ a b ha hsstar hs₂ hstar hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ ι σ _ _ p hp _ hcop hg source F x weight slots₁ slots₂ lists₁ lists₂ a₁ a₂ hn hcut
  apply actualSecondProfileRows_integral p hp hcop hg source F x weight
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y G₀ E₀ V₀ K₀ X₀
    (secondRootSchwartz V hV hS) b₁ b₂ b₃
  intro j hj
  have hj0 := (mem_secondProfileIndices source F x j).mp hj
  exact he (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hj0.1).1 (hn j.1 hj0.1).2 j.2.1 j.2.2)
    (hcut j hj)

end
end SevenEighths.InverseMoment

end OAI
