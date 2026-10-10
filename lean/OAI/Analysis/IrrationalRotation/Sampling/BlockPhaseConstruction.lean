import OAI.Analysis.IrrationalRotation.Model.PhaseBlocks
import OAI.Analysis.IrrationalRotation.Sampling.LargePhaseAssembly
import OAI.Analysis.IrrationalRotation.Analysis.BlockAngleConstruction

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Invariant233.ProductPhases

@[simp] theorem card_consecutiveBlock (m : ℕ → ℕ) (j : ℕ) :
    (consecutiveBlock m j).card = m j := by
  simp [consecutiveBlock]

theorem mem_consecutiveBlock_iff (m : ℕ → ℕ) (j i : ℕ) :
    i ∈ consecutiveBlock m j ↔
      (∑ r ∈ Finset.range j, m r) ≤ i ∧
        i < (∑ r ∈ Finset.range j, m r) + m j := by
  simp [consecutiveBlock]

theorem enumeration_block_of_mem (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {j i : ℕ} (hi : i ∈ consecutiveBlock m j) : (e i).1 = j := by
  obtain ⟨hlo, hhi⟩ := (mem_consecutiveBlock_iff m j i).mp hi
  let a : Fin (m j) := ⟨i - (∑ r ∈ Finset.range j, m r), by omega⟩
  have ha : e.symm ⟨j, a⟩ = i := by
    rw [he]
    dsimp [a]
    omega
  have heq : e i = ⟨j, a⟩ := by
    rw [← ha, e.apply_symm_apply]
  exact congrArg Sigma.fst heq

theorem mem_consecutiveBlock_enumeration (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    (i : ℕ) : i ∈ consecutiveBlock m (e i).1 := by
  have hi : i = (∑ r ∈ Finset.range (e i).1, m r) + (e i).2.val := by
    simpa only [e.symm_apply_apply] using he (e i)
  apply (mem_consecutiveBlock_iff m (e i).1 i).mpr
  have hb := (e i).2.isLt
  omega

theorem consecutive_uniformProduct_ae_phaseRanges
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G : ℕ → ℝ) (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)))),
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  have hN : ∀ i : ℕ, 0 < (m (e i).1 : ℝ) * K (e i).1 := fun i =>
    mul_pos (Nat.cast_pos.mpr (hm _)) (hK _)
  have h := uniformProduct_ae_phaseRanges
    (fun i => (m (e i).1 : ℝ) * K (e i).1) hN
    (consecutiveBlock m) K G hK hG
    (by simpa only [card_consecutiveBlock] using hgrowth)
    (by
      intro j i hi
      rw [enumeration_block_of_mem m e he hi, card_consecutiveBlock])
  simpa only [card_consecutiveBlock] using h

theorem exists_consecutive_phase_angles_and
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G : ℕ → ℝ) (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hsum : Summable (fun j => 1 / K j))
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    {P : (ℕ → ℝ) → Prop}
    (hP : ∀ᵐ θ ∂Measure.infinitePi (fun i => ProbabilityTheory.cond volume
      (Set.Icc (1 / ((m (e i).1 : ℝ) * K (e i).1))
        (2 / ((m (e i).1 : ℝ) * K (e i).1)))), P θ) :
    ∃ θ : ℕ → ℝ,
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Set.Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∀ i, 0 < θ i) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      LinearIndependent ℚ (fun o : Option ℕ => o.elim 1 θ) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) ∧ P θ := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  let N : ℕ → ℝ := fun i => (m (e i).1 : ℝ) * K (e i).1
  have hN : ∀ i, 0 < N i := fun i =>
    mul_pos (Nat.cast_pos.mpr (hm _)) (hK _)
  have hblock := InvariantProjection.IndependentAngles.enumerated_block_reciprocal
    m hm K hK hsum e
  have hphase := consecutive_uniformProduct_ae_phaseRanges m hgrowth K G hK hG e he
  obtain ⟨θ, hθ, hsθ, htθ, hiθ, hph, hp⟩ :=
    InvariantProjection.IndependentAngles.exists_prescribed_summable_independent_and
      N hN hblock.1 (hphase.and hP)
  refine ⟨θ, ?_, ?_, hsθ, ?_, hiθ, hph.1, hph.2, hp⟩
  · intro j i hi
    simpa only [N, enumeration_block_of_mem m e he hi] using hθ i
  · intro i
    exact (one_div_pos.mpr (hN i)).trans_le (hθ i).1
  · simpa only [N, hblock.2] using htθ

theorem exists_consecutive_phase_angles
    (m : ℕ → ℕ) (hgrowth : ∀ j, 2 ^ j ≤ m j)
    (K G : ℕ → ℝ) (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hsum : Summable (fun j => 1 / K j)) :
    ∃ θ : ℕ → ℝ,
      (∀ j, ∀ i ∈ consecutiveBlock m j,
        θ i ∈ Set.Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) ∧
      (∀ i, 0 < θ i) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' j, 1 / K j) ∧
      LinearIndependent ℚ (fun o : Option ℕ => o.elim 1 θ) ∧
      (∀ j, smallPhaseCondition (consecutiveBlock m j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        largePhaseCondition (consecutiveBlock m j) ((m j : ℝ) * K j) θ) := by
  have hm : ∀ j, 0 < m j := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  obtain ⟨e, he⟩ := InvariantProjection.IndependentAngles.exists_consecutiveBlocks_equiv m hm
  obtain ⟨θ, hθ, hpos, hs, hsumθ, hind, hsmall, hlarge, _⟩ :=
    exists_consecutive_phase_angles_and m hgrowth K G hK hG hsum e he
      (P := fun _ => True) (Filter.Eventually.of_forall fun _ => True.intro)
  exact ⟨θ, hθ, hpos, hs, hsumθ, hind, hsmall, hlarge⟩

end Invariant233.ProductPhases

end

end OAI
