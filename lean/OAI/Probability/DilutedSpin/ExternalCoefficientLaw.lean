import OAI.Probability.DilutedSpin.ExternalFreshLaw

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
lemma integral_fresh_label_prod {W J Z : Type*} [MeasurableSpace W] [MeasurableSpace J]
    [MeasurableSpace Z] (ρ : Measure W) [IsProbabilityMeasure ρ]
    (τ : Measure Z) [IsProbabilityMeasure τ] (label : Z → J) (hl : Measurable label)
    (F : W × J → ℝ) (hF : Measurable F) {B : ℝ} (hb : ∀ z, |F z| ≤ B) :
    (∫ z, F z ∂ρ.prod (τ.map label)) = ∫ z : W×Z, F (z.1,label z.2) ∂ρ.prod τ := by
  rw [integral_fresh_label ρ τ label hl F hF hb]
  symm
  apply integral_prod
  apply Integrable.of_bound (hF.comp (measurable_fst.prodMk (hl.comp measurable_snd))).aestronglyMeasurable B
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb (z.1,label z.2))
end DilutedSpinGlass

namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma externalCoefficientAverage_fresh_label
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (label : Z → I) (hl : Measurable label) (k : ℕ) :
    externalCoefficientAverage ξ μ ν (τ.map label) r s S a T Q m base old D E f k =
      ∫ z : FullRootState Y X I M × Z, rootExternalCoefficient S a T Q m base old D E f k z.1 (label z.2)
        ∂(fullRootLaw ξ μ ν r s).prod τ := by
  apply integral_fresh_label_prod (fullRootLaw ξ μ ν r s) τ label hl
  · exact measurable_rootExternalCoefficient S a T Q m hm base old D E f k hb
  · intro z
    exact externalCoefficient_bound S a T Q m hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old (D z.2) (E z.2) f hB hf (hD z.2) (hE z.2) k

lemma integrable_rootExternalCoefficient_label
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (label : Z → I) (hl : Measurable label) (k : ℕ) :
    Integrable (fun z : FullRootState Y X I M × Z =>
      rootExternalCoefficient S a T Q m base old D E f k z.1 (label z.2))
      ((fullRootLaw ξ μ ν r s).prod τ) := by
  apply Integrable.of_bound ((measurable_rootExternalCoefficient S a T Q m hm base old D E f k hb).comp
    (measurable_fst.prodMk (hl.comp measurable_snd))).aestronglyMeasurable
    (B*PrescribedTree.derivativeBound (S.leaves+(Finset.univ.erase a).card) k/(k.factorial:ℝ))
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs]
    exact externalCoefficient_bound S a T Q m hmono hpos hroot hend
      (base z.1.1 z.1.2.1.1 z.1.2.1.2) (rootArray z.1.2.2.1 z.1.2.2.2) (label z.2) old _ _ f hB hf (hD _) (hE _) k)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
