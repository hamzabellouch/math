import OAI.Probability.DilutedSpin.FullPalm

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ν : Measure I) [IsProbabilityMeasure ν]

lemma selected_palm_averaged (S : PrescribedTree L) (a : S.Leaf)
    (s : ℝ≥0) (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ n : ℕ, ∫ y, selectedTreeScore S a T Q m base (rootArray n y) sel fixed D E t u f
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s) =
      (s:ℝ) * ∫ n : ℕ, ∫ y,
        averagedInsertedTreeScore ν S a T Q m base (rootArray n y)
          (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
        ∂rootLaw n (fun _ => ν) ∂poissonMeasure s := by
  rw [selected_palm ν S a s T Q m base sel fixed D E t u f hf hE hA]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro n
  apply integral_integral_swap
  exact Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (2*B)
    (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs,Function.uncurry] using
      abs_insertedTreeScore_le S a T Q m base (rootArray n z.2) z.1 _ _ f hf (selectedNumerator_bound sel E hE) hA))

noncomputable def fullInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (z : FullRootState Y X I M) : ℝ :=
  packRoot (fun h k x n y => averagedInsertedTreeScore ν S a T Q m (base h k x) (rootArray n y) factor numerator f) z

variable (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- Full-root Palm identity, including the original physical Poisson/sample
and field laws. The surviving root law on the right is exactly the left law. -/
theorem fullRoot_selected_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor sel fixed D E t u i x y) :
    (∫ z, fullSelectedTreeScore S a T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) =
      (s:ℝ) * ∫ z, fullInsertedTreeScore ν S a T Q m base
        (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f z ∂fullRootLaw ξ μ ν r s := by
  let F := fun h k x n y => selectedTreeScore S a T Q m (base h k x) (rootArray n y) sel fixed D E t u f
  let G := fun h k x n y => averagedInsertedTreeScore ν S a T Q m (base h k x) (rootArray n y)
    (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => F z.1.1 k z.1.2 n z.2) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_selectedTreeScore S a T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) sel fixed D E t u f (hb k)
  have hG (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n => G z.1.1 k z.1.2 n z.2) := by
    apply measurable_from_prod_countable_left
    intro y
    exact measurable_averagedInsertedTreeScore ν S a T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (rootArray n y) _ _ f (hb k)
  have hFb (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |F h k x n y| ≤ 2*B+0*(k:ℝ)^2+2*B*(n:ℝ)^2 := by
    have hh := fullSelectedTreeScore_bound S a T Q m base sel fixed D E t u f hB hf hD hE ht hu (h,⟨k,x⟩,⟨n,y⟩)
    have hn : (n:ℝ) ≤ 1+(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1), (show 0 ≤ (n:ℝ) by positivity)]
    have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*B by positivity)
    dsimp only [fullSelectedTreeScore,packRoot] at hh
    dsimp only [F]
    nlinarith
  have hGb (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |G h k x n y| ≤ 2*B+0*(k:ℝ)^2+0*(n:ℝ)^2 := by
    simpa only [zero_mul,add_zero] using abs_averagedInsertedTreeScore_le ν S a T Q m (base h k x) (rootArray n y) _ _ f hf (selectedNumerator_bound sel E hE) hA
  change (∫ z, packRoot F z ∂fullRootLaw ξ μ ν r s) = (s:ℝ) * ∫ z, packRoot G z ∂fullRootLaw ξ μ ν r s
  rw [integral_fullRootLaw_quadratic ξ μ ν r s hF hFb,
    integral_fullRootLaw_quadratic ξ μ ν r s hG hGb]
  dsimp only [F,G]
  simp_rw [selected_palm_averaged ν S a s T Q m _ sel fixed D E t u f hf hE hA,
    integral_const_mul]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
