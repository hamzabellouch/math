import Mathlib

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.AffineSelector
open Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def Regular (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) (x : E) : Prop :=
  ∀ i j, a i x + b i = a j x + b j → a i = a j

theorem locally_affine (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {f : E → ℝ} (hf : Continuous f)
    (hselect : ∀ y, ∃ i, f y = a i y + b i) {x : E}
    (hx : Regular a b x) :
    ∃ i, f =ᶠ[𝓝 x] (fun y => a i y + b i) := by
  obtain ⟨i, hi⟩ := hselect x
  refine ⟨i, ?_⟩
  have hj : ∀ j, ∀ᶠ y in 𝓝 x,
      f y = a j y + b j → a j y + b j = a i y + b i := by
    intro j
    by_cases h : f x = a j x + b j
    · have ha : a i = a j := hx i j (hi.symm.trans h)
      have hb : b i = b j := by rw [ha] at hi; linarith
      exact Filter.Eventually.of_forall (fun y _ => by rw [ha, hb])
    · have hn : f x - (a j x + b j) ≠ 0 := sub_ne_zero.mpr h
      have he := (hf.continuousAt.sub ((a j).continuous.continuousAt.add_const (b j))).eventually_ne hn
      filter_upwards [he] with y hy
      intro heq
      exact (hy (sub_eq_zero.mpr heq)).elim
  filter_upwards [Filter.eventually_all.mpr hj] with y hy
  obtain ⟨j, hj⟩ := hselect y
  exact hj.trans (hy j hj)

theorem hasFDerivAt (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ)
    {f : E → ℝ} (hf : Continuous f)
    (hselect : ∀ y, ∃ i, f y = a i y + b i) {x : E}
    (hx : Regular a b x) : ∃ i, HasFDerivAt f (a i) x := by
  obtain ⟨i, hi⟩ := locally_affine a b hf hselect hx
  exact ⟨i, ((a i).hasFDerivAt.add_const (b i)).congr_of_eventuallyEq hi⟩

variable [MeasurableSpace E] [BorelSpace E]

theorem regular_measurableSet (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) :
    MeasurableSet {x | Regular a b x} := by
  classical
  simp only [Regular, Set.ofPred_forall]
  apply MeasurableSet.iInter; intro i
  apply MeasurableSet.iInter; intro j
  by_cases h : a i = a j
  · simp [h]
  · simp only [h, imp_false]
    exact (measurableSet_eq_fun ((a i).continuous.measurable.add_const (b i))
      ((a j).continuous.measurable.add_const (b j))).compl

theorem affine_tie_null [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (a a' : E →L[ℝ] ℝ) (b b' : ℝ) (ha : a ≠ a') :
    μ {x | a x + b = a' x + b'} = 0 := by
  let S : AffineSubspace ℝ E := AffineSubspace.comap
    (a-a').toLinearMap.toAffineMap (affineSpan ℝ ({b'-b} : Set ℝ))
  have hmem : ∀ x, x ∈ S ↔ a x + b = a' x + b' := by
    intro x
    simp only [S, AffineSubspace.mem_comap, AffineSubspace.mem_affineSpan_singleton]
    change a x - a' x = b'-b ↔ _
    constructor <;> intro h <;> linarith
  have hproper : S ≠ ⊤ := by
    intro htop
    have hall : ∀ x, a x + b = a' x + b' := fun x =>
      (hmem x).mp (by rw [htop]; exact AffineSubspace.mem_top ℝ E x)
    have hz : b = b' := by simpa using hall 0
    apply ha
    ext x
    linarith [hall x]
  have heq : (S : Set E) = {x | a x + b = a' x + b'} := Set.ext hmem
  rw [← heq]
  exact Measure.addHaar_affineSubspace μ S hproper

theorem ae_regular [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : ι → E →L[ℝ] ℝ) (b : ι → ℝ) : ∀ᵐ x ∂μ, Regular a b x := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : a i = a j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  · have hne : ∀ᵐ x ∂μ, a i x + b i ≠ a j x + b j := by
      rw [ae_iff]
      simpa only [not_not] using affine_tie_null μ (a i) (a j) (b i) (b j) hij
    filter_upwards [hne] with x hx
    exact fun h => (hx h).elim

end VertexCover.AffineSelector


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
