import OAI.MeasureTheory.Falconer.Measures.FiberDensityPruning

namespace OAI

/-! # Simultaneous density pruning at finitely many endpoint depths -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {P X ι : Type*} [MeasurableSpace P] [MeasurableSpace X]

noncomputable def multiscaleFiberBad (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ) : Set (P × X) :=
  ⋃ j ∈ Finset.range (J+1), fiberDensityBad μ G (Q j) (I j) θ

theorem multiscaleFiberBad_measurable (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i)) : MeasurableSet (multiscaleFiberBad μ G Q I θ J) := by
  apply Finset.measurableSet_biUnion
  intro j hj
  exact fiberDensityBad_measurable μ G hG (Q j) (I j) (hQ j (by simpa using hj)) θ

theorem multiscaleFiberBad_mass (ν : Measure P) (μ : Measure X) [SFinite μ]
    (G : Set (P × X)) (hG : MeasurableSet G) (Q : ℕ → ι → Set X)
    (I : ℕ → Finset ι) (J : ℕ)
    (hQ : ∀ j ≤ J, ∀ i ∈ I j, MeasurableSet (Q j i))
    (hdisj : ∀ j ≤ J, (I j : Set ι).PairwiseDisjoint (Q j)) (θ : ℝ≥0∞) :
    (ν.prod μ) (multiscaleFiberBad μ G Q I θ J) ≤ (J+1:ℝ≥0∞)*(θ*μ univ)*ν univ := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J+1), (ν.prod μ) (fiberDensityBad μ G (Q j) (I j) θ) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (J+1), (θ*μ univ)*ν univ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjJ : j ≤ J := by simpa using hj
      exact fiberDensityBad_product_mass ν μ G hG (Q j) (I j) (hQ j hjJ) (hdisj j hjJ) θ
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]; ring

omit [MeasurableSpace P] in
theorem multiscaleFiber_retained (μ : Measure X) (G : Set (P × X))
    (Q : ℕ → ι → Set X) (I : ℕ → Finset ι) (θ : ℝ≥0∞) (J : ℕ)
    {p : P} {x : X} (hx : (p,x) ∈ G \ multiscaleFiberBad μ G Q I θ J)
    {j : ℕ} (hj : j ≤ J) {i : ι} (hi : i ∈ I j) (hxi : x ∈ Q j i) :
    θ*μ (Q j i) ≤ μ (Q j i ∩ Prod.mk p ⁻¹' G) := by
  apply fiberDensity_retained μ G (Q j) (I j) θ ⟨hx.1,?_⟩ hi hxi
  intro hbad
  apply hx.2
  exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨by simpa using hj,hbad⟩⟩

end Falconer

end OAI
