import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceIntervals
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanConjugationBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanRecurrenceBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSupports

namespace OAI

/-! # Recurrence cells for the actual conjugated source intervals -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W] (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N] [SimplyConnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]
  (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
  (Exp : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExp : IsGroupExponential Exp)
  (haar : NilpotentExponentialHaarInput EN N) (dynkin : NilpotentDynkinExpansionInput EN N)

include hExp haar dynkin in
/-- The initial cell translation and the inside-sheet conjugation are both
controlled in the containing template. The denominator is an exact radius
power, and is subexponential. No independence after restriction is used. -/
theorem exists_coupled_interval_recurrence_cells
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Set W) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (s : Fin M.letterCount → ℝ)
    (hs : ∀ i, s i ≤ (M.supportIn T hunimod eW).weightSupport E i)
    {m : ℕ} (letters : Fin m → Fin M.letterCount)
    (scale R : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (k₀ : ℕ → N) (k : ℕ → ℕ → N)
    (hk₀ : ∀ n, k₀ n ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n))
    (hk : ∀ n j, k n j ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R n)) :
    let μ := Measure.map ((Exp ∘ eN) ∘ b₀.equivFun.symm) volume
    let Q := fun n => (fun y => y * k₀ n) ''
      M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) 1
    ∃ V D : ℕ → ℝ, (∀ n, 1 ≤ V n) ∧
      HasSubexponentialUpperBoundSeq scale D ∧ (∀ n, 0 < D n) ∧
      let Q' := fun n => (fun y => y * k₀ n) ''
        M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (V n)
      (∀ n, μ (Q n) ≠ ∞ ∧ 0 < (μ (Q n)).toReal ∧
        μ (Q' n) ≠ ∞ ∧ 0 < (μ (Q' n)).toReal ∧
        (μ (Q' n)).toReal = D n * (μ (Q n)).toReal) ∧
      ∀ n j, ∀ x ∈ Q n,
        ∀ u ∈ rootIntervalSupport (Exp ∘ eN) letters M.letter s (scale n) ρ j,
          x * (k n j * u * (k n j)⁻¹) ∈ Q' n := by
  obtain ⟨C, hC, hinterval⟩ := M.exists_source_interval_box_bound T hunimod eW b₀
  let R' := fun n => R n + C * ρ
  have hR'0 : ∀ n, 0 ≤ R' n := fun n => add_nonneg (hR0 n) (mul_nonneg hC hρ)
  have hR' : HasSubexponentialUpperBoundSeq scale R' :=
    hR.add (sequence_subexponential_upper_const hscale (C * ρ)) hscale
  have hmono (n : ℕ) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
      M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) r₁ ⊆
        M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) r₂ := by
    rintro z ⟨v, hv, hb⟩
    exact ⟨v, hv, hb.trans hr⟩
  have hpad (n j : ℕ) {u : N}
      (hu : u ∈ rootIntervalSupport (Exp ∘ eN) letters M.letter s (scale n) ρ j) :
      u ∈ M.groupBox T hunimod eW (Exp ∘ eN) E β (scale n) (R' n) := by
    obtain ⟨t, ht, rfl⟩ := hu
    by_cases hj : j < m
    · rw [rootIntervalSample_letter (Exp ∘ eN) letters M.letter s (scale n) ⟨j, hj⟩]
      exact hmono n (le_add_of_nonneg_left (hR0 n))
        (hinterval E β hβ s hs (Exp ∘ eN) (scale n) ρ (hscale0 n) hρ
          (letters ⟨j, hj⟩) t (by simpa [Real.dist_eq] using ht))
    · have he : rootIntervalSample (Exp ∘ eN) letters M.letter s (scale n) j t = 1 := by
        simp [rootIntervalSample, rootIntervalDirection, hj, hExp.map_zero]
      rw [he]
      exact ⟨0, by simp [hExp.map_zero], by simpa using hR'0 n⟩
  obtain ⟨A, hA0, hA, hconj⟩ := M.exists_sequence_double_conjugate_box T hunimod eW eN Exp
    hExp dynkin b₀ E β hβ scale R' hscale hscale0 hR'0 hR'
  obtain ⟨V, hV, _, hD, hcells⟩ := M.exists_sequence_recurrence_enlargement T hunimod eW
    eN Exp hExp haar dynkin b₀ E β hβ scale A hscale hscale0 hA0 hA
  dsimp only
  refine ⟨V, fun n => V n ^ finrank ℝ (cartanRootIdeal H), hV, hD,
    fun n => pow_pos (zero_lt_one.trans_le (hV n)) _, ?_, ?_⟩
  · intro n
    exact ⟨(hcells n (k₀ n)).1, (hcells n (k₀ n)).2.1,
      (hcells n (k₀ n)).2.2.1, (hcells n (k₀ n)).2.2.2.1,
      (hcells n (k₀ n)).2.2.2.2.1⟩
  · intro n j x hx u hu
    apply (hcells n (k₀ n)).2.2.2.2.2 _ _ x hx
    exact hconj n (k₀ n) (k n j) u
      (hmono n (le_add_of_nonneg_right (mul_nonneg hC hρ)) (hk₀ n))
      (hmono n (le_add_of_nonneg_right (mul_nonneg hC hρ)) (hk n j)) (hpad n j hu)

end PolycyclicRecognition.CartanWordModel

end

end OAI
