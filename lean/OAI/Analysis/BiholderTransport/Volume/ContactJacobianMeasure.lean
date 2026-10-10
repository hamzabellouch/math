import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma measure_eq_zero_of_nonsingular_null_image {f : E → E} {df : E → E →L[ℝ] E}
    {s : Set E} (hd : ∀ x∈s, HasFDerivWithinAt f (df x) s x)
    (hdet : ∀ x∈s, (df x).det≠0) (hnull : μ (f '' s)=0) : μ s=0 := by
  classical
  have hchoice : ∀ A : E →L[ℝ] E, ∃ δ : ℝ≥0, 0<δ ∧
      (A.det≠0 → ∀ a : Set E, ∀ g : E → E,
        ApproximatesLinearOn g A a δ → μ (g '' a)=0 → μ a=0) := by
    intro A
    by_cases hA : A.det=0
    · exact ⟨1,zero_lt_one,fun h => (h hA).elim⟩
    have ha : 0 < |A.det| := abs_pos.mpr hA
    let m : ℝ≥0 := ⟨|A.det|/2,by positivity⟩
    have hm : (m:ℝ≥0∞)<ENNReal.ofReal |A.det| := by
      rw [ENNReal.ofReal_eq_coe_nnreal,ENNReal.coe_lt_coe]
      change m < ⟨|A.det|, abs_nonneg _⟩
      exact_mod_cast (half_lt_self ha)
    have hpos : ∀ᶠ δ : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0<δ := self_mem_nhdsWithin
    obtain ⟨δ,hδ,H⟩ := (hpos.and (mul_le_addHaar_image_of_lt_det μ A hm)).exists
    refine ⟨δ,hδ,fun _ a g hg hz => ?_⟩
    have hh : (m:ℝ≥0∞)*μ a=0 := le_antisymm ((H a g hg).trans_eq hz) bot_le
    have hmpos : (0:ℝ≥0∞) < m := by
      exact_mod_cast (show (0:ℝ)<(m:ℝ) by change 0 < |A.det| / 2; exact half_pos ha)
    exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hmpos)
  choose δ hδ Hδ using hchoice
  obtain ⟨t,A,_,hcover,happrox,hA⟩ :=
    exists_closed_cover_approximatesLinearOn_of_hasFDerivWithinAt f s df hd δ
      (fun A => (hδ A).ne')
  rcases s.eq_empty_or_nonempty with rfl|hs
  · exact measure_empty
  have ht : ∀ k, μ (s∩t k)=0 := by
    intro k
    obtain ⟨y,hy,hAy⟩ := hA hs k
    apply Hδ (A k) (hAy ▸ hdet y hy) (s∩t k) f (happrox k)
    exact measure_mono_null (Set.image_mono inter_subset_left) hnull
  apply measure_mono_null (t := ⋃ k, s∩t k)
  · intro x hx
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover hx)
    exact mem_iUnion.mpr ⟨k,hx,hk⟩
  · exact measure_iUnion_null ht

end WeakMTWTransport

end

end OAI
