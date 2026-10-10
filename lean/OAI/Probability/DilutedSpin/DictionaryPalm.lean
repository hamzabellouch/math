import OAI.Probability.DilutedSpin.ExternalRoot
import OAI.Probability.DilutedSpin.PalmError
import OAI.Probability.DilutedSpin.ParameterProduct

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)] {L n : ℕ}

lemma insertedTreeScore_selected (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) :
    insertedTreeScore S a T Q m base roots i (selectedFactor sel fixed D E t u) (selectedNumerator sel E) f =
      if sel i then externalTreeScore S a T Q m base roots i (selectedFactor sel fixed D E t u)
        (fun x y => 1+t*D i x y+u*E i x y) (E i) f else 0 := by
  rw [inserted_eq_external]
  cases hi : sel i
  · have hn : selectedNumerator sel E i = fun _ _ => 0 := by funext x y; simp only [selectedNumerator,hi,Bool.false_eq_true,ite_false]
    rw [hn]
    simp only [externalTreeScore,zero_div,mul_zero,FiniteLaw.expect_const,Bool.false_eq_true,ite_false]
  · have hn : selectedNumerator sel E i = E i := by funext x y; simp only [selectedNumerator,hi,ite_true]
    have ha : selectedFactor sel fixed D E t u i = fun x y => 1+t*D i x y+u*E i x y := by
      funext x y
      simp only [selectedFactor,hi,ite_true]
    rw [hn,ha]
    simp only [ite_true]

variable {J Z X Y : Type} [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {M : ℕ}
    {C : J × Z → Type} [∀ i, Fintype (C i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (C i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (fixed D E : (i : J × Z) → FinitePath Ω L → FinitePath (C i) L → ℝ)
    (j : J) (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- The exact mass of a selected type emerges from the full law, with its
site average independent of the unchanged complete reservoir. -/
lemma fullInserted_select_type
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i x y, |E i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ 1+t*D i x y+u*E i x y) :
    (∫ z, fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base
      (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u)
      (selectedNumerator (fun i => decide (i.1 = j)) E) f z ∂fullRootLaw ξ μ (ν.prod τ) r s) =
      ν.real {j} * externalAverage ξ μ (ν.prod τ) (τ.map (fun z => (j,z))) r s S a T Q m base
        (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) D E f t u := by
  let old := selectedFactor (fun i : J × Z => decide (i.1 = j)) fixed D E t u
  let F : FullRootState Y X (J × Z) M × (J × Z) → ℝ := fun z =>
    rootExternalTreeScore S a T Q (fun l => m l.succ) base old
      (fun i x y => 1+t*D i x y+u*E i x y) E f z.1 z.2
  have hFm : Measurable F := measurable_rootExternalTreeScore S a T Q _ base old _ E f hb
  have hFb (z) : |F z| ≤ 2*B :=
    abs_externalTreeScore_le S a T Q _ (base z.1.1 z.1.2.1.1 z.1.2.1.2)
      (rootArray z.1.2.2.1 z.1.2.2.2) z.2 old _ _ f hf (hE z.2) (hA z.2)
  have he (z : FullRootState Y X (J × Z) M) :
      fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base old
        (selectedNumerator (fun i => decide (i.1 = j)) E) f z =
        ν.real {j} * ∫ q, F (z,(j,q)) ∂τ := by
    dsimp only [fullInsertedTreeScore,packRoot,averagedInsertedTreeScore,old]
    simp_rw [insertedTreeScore_selected]
    simpa only [decide_eq_true_eq,F,rootExternalTreeScore,packRoot,old] using
      integral_select_product ν τ j (fun i => F (z,i)) (by positivity) (fun i => hFb (z,i))
  change (∫ z, fullInsertedTreeScore (ν.prod τ) S a T Q (fun l => m l.succ) base old
    (selectedNumerator (fun i => decide (i.1 = j)) E) f z ∂fullRootLaw ξ μ (ν.prod τ) r s) = _
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  unfold externalAverage
  exact (integral_fresh_label (fullRootLaw ξ μ (ν.prod τ) r s) τ (fun q => (j,q))
    (measurable_const.prodMk measurable_id) F hFm hFb).symm

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
