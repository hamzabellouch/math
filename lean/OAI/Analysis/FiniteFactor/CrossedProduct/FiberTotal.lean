import OAI.Analysis.FiniteFactor.CrossedProduct.FiberIndicators
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Measurable base indicators on the integer fibers determine an L2 vector. -/
theorem sourceFiberIndicators_total (f : SourceHilbert SourceCoordinate)
    (hf : ∀ (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ),
      inner ℂ (sourceFiberIndicator A hA n) f = 0) : f = 0 := by
  apply Lp.ext
  refine (Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f (by norm_num) (by norm_num)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top f (by norm_num) hs.ne) ?_).trans ?_
  · intro s hs hμs
    let A : ℤ → Set (SourceCoordinate → ℝ) := fun n => {x | (x,n) ∈ s}
    have hA (n : ℤ) : MeasurableSet (A n) := hs.preimage (measurable_id.prodMk measurable_const)
    have hcover : s = ⋃ n : ℤ, A n ×ˢ {n} := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
      constructor
      · intro hz; exact ⟨z.2, hz, rfl⟩
      · rintro ⟨n,hn,he⟩; simpa only [← he, Prod.eta] using hn
    have hd : Pairwise (fun n m : ℤ => Disjoint (A n ×ˢ {n}) (A m ×ˢ {m})) := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      rintro z ⟨_,hn⟩ ⟨_,hm⟩
      exact hnm (hn.symm.trans hm)
    have hi : IntegrableOn f (⋃ n : ℤ, A n ×ˢ {n}) (sourceMeasure SourceCoordinate) := by
      rw [← hcover]
      exact integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs.ne
    rw [hcover, integral_iUnion (fun n => (hA n).prod (measurableSet_singleton n)) hd hi]
    have hz (n : ℤ) : ∫ z in A n ×ˢ {n}, f z ∂sourceMeasure SourceCoordinate = 0 := by
      have he := hf (A n) (hA n) n
      rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one] at he
      exact he
    simp_rw [hz]
    exact tsum_zero
  · exact (Lp.coeFn_zero _ _ _).symm

end
end FiniteFactor

end OAI
