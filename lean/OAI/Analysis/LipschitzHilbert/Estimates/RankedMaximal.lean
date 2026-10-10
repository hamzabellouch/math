import OAI.Analysis.LipschitzHilbert.Estimates.LaminarWeakL1

namespace OAI

/-! Positive integral maximal functions for the line and square grids. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert
variable {ι X : Type*} [MeasurableSpace X]

def rankedMaximal (μ : Measure X) (Q : ι → Set X) (f : X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x

theorem rankedMaximal_measurable [Countable ι] (μ : Measure X) (Q : ι → Set X)
    (hQ : ∀ i, MeasurableSet (Q i)) (f : X → ℝ≥0∞) : Measurable (rankedMaximal μ Q f) :=
  Measurable.iSup (fun i => measurable_const.indicator (hQ i))

theorem rankedMaximal_mono (μ : Measure X) (Q : ι → Set X)
    {f g : X → ℝ≥0∞} (h : f ≤ g) : rankedMaximal μ Q f ≤ rankedMaximal μ Q g := by
  intro x
  change (⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x) ≤
    ⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, g y ∂μ) / μ (Q i)) x
  apply iSup_mono
  intro i
  by_cases hx : x ∈ Q i
  · simp only [indicator_of_mem hx]
    exact mul_le_mul' (lintegral_mono h) le_rfl
  · simp only [indicator_of_notMem hx,le_refl]

theorem average_le_rankedMaximal (μ : Measure X) (Q : ι → Set X) (f : X → ℝ≥0∞)
    (i : ι) {x : X} (hx : x ∈ Q i) :
    (∫⁻ y in Q i, f y ∂μ) / μ (Q i) ≤ rankedMaximal μ Q f x := by
  calc
    _ = (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x := (indicator_of_mem hx _).symm
    _ ≤ _ := le_iSup (fun i => (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x) i

theorem rankedMaximal_weak_L1 [Countable ι] (μ : Measure X) (Q : ι → Set X)
    (rank : ι → ℤ) (hm : ∀ i, MeasurableSet (Q i))
    (hpos : ∀ i, μ (Q i) ≠ 0) (hfinite : ∀ i, μ (Q i) ≠ ∞)
    (hnest : ∀ i j, rank j ≤ rank i → (Q i ∩ Q j).Nonempty → Q j ⊆ Q i)
    (f : X → ℝ≥0∞) (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    μ {x | t < rankedMaximal μ Q f x} ≤ t⁻¹ * ∫⁻ x, f x ∂μ := by
  let G := {i : ι | t * μ (Q i) ≤ ∫⁻ x in Q i, f x ∂μ}
  have hsub : {x | t < rankedMaximal μ Q f x} ⊆ ⋃ i : G, Q i.val := by
    intro x hx
    change t < ⨆ i, (Q i).indicator (fun _ => (∫⁻ y in Q i, f y ∂μ) / μ (Q i)) x at hx
    obtain ⟨i,hi⟩ := lt_iSup_iff.mp hx
    have hxi : x ∈ Q i := by
      by_contra hn
      simp only [indicator_of_notMem hn,not_lt_zero] at hi
    rw [indicator_of_mem hxi] at hi
    have hg : i ∈ G := by
      calc
        t * μ (Q i) ≤ ((∫⁻ y in Q i, f y ∂μ) / μ (Q i)) * μ (Q i) := mul_le_mul' hi.le le_rfl
        _ = _ := ENNReal.div_mul_cancel (hpos i) (hfinite i)
    exact mem_iUnion.mpr ⟨⟨i,hg⟩,hxi⟩
  have hmass := ranked_countable_weak_bound μ (fun i : G => Q i.val) (fun i => rank i.val)
    (fun i => hm i.val) (fun i j => hnest i.val j.val) f t (fun i => i.property)
  calc
    _ ≤ μ (⋃ i : G, Q i.val) := measure_mono hsub
    _ = t⁻¹ * (t * μ (⋃ i : G, Q i.val)) := by
      rw [←mul_assoc,ENNReal.inv_mul_cancel ht htop,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hmass

end LipschitzHilbert

end

end OAI
