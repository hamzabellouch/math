import OAI.Analysis.IrrationalRotation.Sampling.BlockPhaseConstruction
import OAI.Analysis.IrrationalRotation.Product.ProductBlockCost

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology

namespace Invariant233.ProductModel

open ProductPhases

theorem exists_admissible_phase_block_weight_and
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hG : ∀ j, 0 < G j)
    (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j => 1 / K j))
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {P : (ℕ → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)))), P θ) :
    ∃ θ : ℕ → ℝ,
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      AdmissibleAnglesAndCosts θ (fun i => C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure,
        0 < weight θ (fun i => C (e i).1) x ∧ weight θ (fun i => C (e i).1) x ≤ 1) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) ∧ P θ := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  have hKpos (j : ℕ) : 0 < K j := zero_lt_one.trans_le (hK j)
  have hCpos (j : ℕ) : 0 < C j := (sq_pos_of_pos (hKpos j)).trans_le (hC j)
  obtain ⟨θ, hθ, hpos, hsθ, htθ, hind, hsmall, hlarge, hp⟩ :=
    exists_consecutive_phase_angles_and m hgrowth K G hKpos hG hsum e he hP
  have hbounds (i : ℕ) : θ i ∈
      Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)) :=
    hθ (e i).1 i (mem_consecutiveBlock_enumeration m e he i)
  have hunit (i : ℕ) : θ i < 1 :=
    (hbounds i).2.trans_lt ((div_lt_one
      (mul_pos (Nat.cast_pos.mpr (hm _)) (hKpos _))).mpr (hscale _))
  refine ⟨θ, hθ, htθ, ?_, ?_, ?_, hsmall, hlarge, hp⟩
  · exact ⟨fun i => ⟨hpos i, hunit i, hCpos _⟩, hsθ, hind⟩
  · exact hasNegInfiniteLogIntegral_of_block_bounds m hm K C hK hC e θ
      (fun i => ⟨(hpos i).le, hunit i⟩) (fun i => (hbounds i).1)
  · filter_upwards [ae_weight_pos θ (fun i => C (e i).1)
      (fun i => (hpos i).le) (fun i => (hCpos _).le) hsθ] with x hx
    exact ⟨hx, (weight_mem_Icc θ _ x).2⟩

theorem exists_admissible_phase_block_weight
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hG : ∀ j, 0 < G j)
    (hC : ∀ j, (K j) ^ 2 ≤ C j)
    (hscale : ∀ j, 2 < (m j : ℝ) * K j)
    (hsum : Summable (fun j => 1 / K j)) :
    ∃ (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ),
      (∀ a : Σ j, Fin (m j),
        e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val) ∧
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      AdmissibleAnglesAndCosts θ (fun i => C (e i).1) ∧
      HasNegInfiniteLogIntegral baseMeasure (weight θ (fun i => C (e i).1)) ∧
      (∀ᵐ x ∂baseMeasure,
        0 < weight θ (fun i => C (e i).1) x ∧ weight θ (fun i => C (e i).1) x ≤ 1) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  obtain ⟨e, he⟩ := InvariantProjection.IndependentAngles.exists_consecutiveBlocks_equiv m hm
  obtain ⟨θ, hθ, htθ, hadm, hlog, hweight, hsmall, hlarge, _⟩ :=
    exists_admissible_phase_block_weight_and m hgrowth K G C hK hG hC hscale hsum e he
      (P := fun _ => True) (Filter.Eventually.of_forall fun _ => True.intro)
  exact ⟨e, θ, he, hθ, htθ, hadm, hlog, hweight, hsmall, hlarge⟩

end Invariant233.ProductModel

end

end OAI
