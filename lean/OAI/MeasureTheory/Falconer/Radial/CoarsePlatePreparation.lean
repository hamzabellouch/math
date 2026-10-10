import OAI.MeasureTheory.Falconer.Radial.CoarsePlatePositive
import OAI.MeasureTheory.Falconer.Radial.CoarsePlateCells
import OAI.MeasureTheory.Falconer.Radial.CoarsePlateDirections
import OAI.MeasureTheory.Falconer.Radial.CoarsePlateSymmetry

namespace OAI

/-! # Coarse heavy-plate preparation with positive mass and both directional bounds -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem coarse_plate_preparation (hpublished : PublishedHeavyHyperplanes)
    {d : ℕ} (hd : 3 ≤ d) (μ ν : ProbabilityMeasure (Space d))
    (Q : DyadicCube d) (hQ : 0 < Q.side) {M s C : ℝ}
    (hM : 0 ≤ M) (hroot : ∀ x ∈ Q.carrier, ‖x‖ ≤ M)
    (hs : 1/2 < s-((d-2:ℕ):ℝ)) (hs' : s-((d-2:ℕ):ℝ) < 1) (hC : 0 ≤ C)
    (hμbounded : ∀ᵐ x ∂(μ : Measure (Space d)), ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ x ∂(ν : Measure (Space d)), ‖x‖ ≤ M)
    (hμfrost : FrostmanBallBound (μ : Measure (Space d)) s C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space d)) s C)
    (hμroot : (μ : Measure (Space d)) Q.carrier = 1)
    (hνroot : (ν : Measure (Space d)) Q.carrier = 1)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ,
      ((μ : Measure (Space d))+(ν : Measure (Space d))) {x | inner ℝ w x = t} = 0)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ (Γ : ℕ → Set (Space d × Space d)) (K ζ : ℝ), 0 < K ∧ 0 < ζ ∧
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((μ : Measure (Space d)).prod (ν : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N : ℕ, ∃ T : Finset (List (Fin d → Bool) × List (Fin d → Bool)),
        T ⊆ (cubePaths d ⌊ω*(N:ℝ)⌋₊).product (cubePaths d ⌊ω*(N:ℝ)⌋₊) ∧
        Γ N = ⋃ pq ∈ T, (Q.descendant pq.1).carrier ×ˢ (Q.descendant pq.2).carrier) ∧
      ∀ N : ℕ, ∀ x w : Space d, ‖w‖ = 1 → ∀ r : ℝ,
        1/(2:ℝ)^N ≤ r → r ≤ 1 →
        (ν : Measure (Space d)) {y | (x,y) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
          ENNReal.ofReal (K*r^ζ) ∧
        (μ : Measure (Space d)) {y | (y,x) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} ≤
          ENNReal.ofReal (K*r^ζ) := by
  obtain ⟨j₀,hpositive⟩ := coarse_plate_positive_limit hpublished hd μ ν Q hQ hM hroot
    hs hs' hC hμbounded hνbounded hμfrost hνfrost hμroot hνroot hzero
  let ρ := (μ : Measure (Space d))+(ν : Measure (Space d))
  let b := heavyPlateExponent (s-((d-2:ℕ):ℝ))
  let Γ := fun N : ℕ => coarsePlateFilter ρ Q j₀ ⌊ω*(N:ℝ)⌋₊ plateScale (fun j => 2*(plateScale j)^b)
  have hb : 0 < b := heavyPlateExponent_pos (by linarith only [hs])
  have hμle : (μ : Measure (Space d)) ≤ ρ := by
    intro t
    change (μ : Measure (Space d)) t ≤ (μ : Measure (Space d)) t+(ν : Measure (Space d)) t
    exact le_add_right le_rfl
  have hνle : (ν : Measure (Space d)) ≤ ρ := by
    intro t
    change (ν : Measure (Space d)) t ≤ (μ : Measure (Space d)) t+(ν : Measure (Space d)) t
    exact le_add_left le_rfl
  refine ⟨Γ,coarseDirectionalConstant Q j₀ b,ω*b,coarseDirectionalConstant_pos Q j₀ b,
    mul_pos hω hb,?_,?_,?_,?_,?_⟩
  · intro N
    exact measurableSet_coarsePlateFilter ρ Q j₀ _ _ _
  · intro N N' hNN'
    exact coarsePlateFilter_antitone ρ Q j₀ _ _ (Nat.floor_mono
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hNN') hω.le))
  · apply hpositive.trans_le
    apply measure_mono
    intro xy hxy
    exact mem_iInter.mpr (fun N => mem_iInter.mp hxy ⌊ω*(N:ℝ)⌋₊)
  · intro N
    exact coarsePlateFilter_product_cells ρ Q j₀ _ _ _
  · intro N x w hw r hr hr1
    have hr' : plateScale N ≤ r := by simpa only [plateScale_eq] using hr
    constructor
    · exact coarse_filter_directional_bound (ν : Measure (Space d)) ρ Q hQ.le j₀ N
        hb.le hω.le hω1 hνle x w hw hr' hr1
    · have he : {y | (y,x) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} =
          {y | (x,y) ∈ Γ N ∧ |inner ℝ w (normalize (y-x))| ≤ r} := by
        ext y
        exact and_congr (coarsePlateFilter_swap_iff ρ Q j₀ _ _ _ y x) Iff.rfl
      rw [he]
      exact coarse_filter_directional_bound (μ : Measure (Space d)) ρ Q hQ.le j₀ N
        hb.le hω.le hω1 hμle x w hw hr' hr1

end Falconer

end OAI
