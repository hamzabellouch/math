import OAI.Probability.DilutedSpin.PairSquare
import OAI.Probability.DilutedSpin.SelectedTree

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

lemma integrable_fullSelectedTreeMean
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B) :
    Integrable (fullSelectedTreeMean S T Q m base sel fixed D E t u f) (fullRootLaw ξ μ ν r s) := by
  apply (integrable_const B).mono' (measurable_fullSelectedTreeMean S T Q m base sel fixed D E t u f hb).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using fullSelectedTreeMean_bound S T Q m base sel fixed D E t u f hf z)

lemma integrable_fullSelectedTreeScore
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    Integrable (fullSelectedTreeScore S a T Q m base sel fixed D E t u f) (fullRootLaw ξ μ ν r s) := by
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  apply (hci.const_mul (2*B)).mono' (measurable_fullSelectedTreeScore S a T Q m base sel fixed D E t u f hb).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using fullSelectedTreeScore_bound S a T Q m base sel fixed D E t u f hB hf hD hE ht hu z)

 
theorem fullTree_score_error
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4) :
    |(∫ z, fullSelectedTreeScore S a T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) -
      (∫ z, fullSelectedTreeMean S T Q m base sel fixed D E t u f z ∂fullRootLaw ξ μ ν r s) *
      (∫ z, fullSelectedRawScore T Q m base sel fixed D E t z u ∂fullRootLaw ξ μ ν r s)| ≤
      B * fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u := by
  let P := fullRootLaw ξ μ ν r s
  let center := ∫ z, fullSelectedRawScore T Q m base sel fixed D E t z u ∂P
  have hiM := integrable_fullSelectedTreeMean ξ μ ν r s S T Q m base sel fixed D E t u f hb hf
  have hiS := integrable_fullSelectedTreeScore ξ μ ν r s S a T Q m base sel fixed D E t u f hb hB hf hD hE ht hu
  have hci : Integrable (fun z : FullRootState Y X I M => (z.2.2.1:ℝ)) P :=
    (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hiD : Integrable (fun z => fullSelectedDeviation T Q m base sel fixed D E t z u center) P := by
    apply ((hci.const_mul 2).add (integrable_const |center|)).mono'
      ((measurable_fullSelectedDeviation T Q m base sel fixed D E t hb measurable_const).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      dsimp only [Function.comp_apply,id_eq,Pi.add_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedDeviation_nonneg T Q m base sel fixed D E t z u center)]
      exact fullSelectedDeviation_bound T Q m base sel fixed D E t hD hE ht hu z center)
  have hh := abs_integral_le_integral_abs.trans (integral_mono
    (hiS.sub (hiM.mul_const center)).abs (hiD.const_mul B)
    (fun z => fullSelectedTree_centered_bound S a T Q m base sel fixed D E t u f hB hf z))
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hiS (hiM.mul_const center),integral_mul_const,integral_const_mul] at hh
  exact hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {L : ℕ}
lemma shapeHistory_pair (T : KernelTower Ω (L+1)) (m : Fin (L+2) → ℝ)
    (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) :
    shapeHistory T m (fun B : Option (Fin 1) → Option (Fin 1) → ℕ => if B none (some 0) = d then 1 else 0)
      (fun c x => match c with | none => if true = true then D x else 1 | some _ => D x) S a f =
      pairObservableHistory T m S a d (fun x y => D x * D y) f := by
  have hcol : (fun (c : Option (Fin 1)) x => match c with | none => if true = true then D x else 1 | some _ => D x) =
      (fun c => match c with | none => D | some _ => D) := by
    funext c x; cases c <;> rfl
  rw [hcol]
  exact (shapeHistory_one T m S a d D D f).trans (pairObservableHistory_product T m S a d D D f).symm
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
