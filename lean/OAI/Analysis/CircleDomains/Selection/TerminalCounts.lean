import OAI.Analysis.CircleDomains.Transfer.GridCollisionEstimate
import OAI.Analysis.CircleDomains.Transfer.GridWidthSelection
import Mathlib.Data.Set.Card

namespace OAI

/-!
# Actual terminal indices and their counting cost

Terminals consist of prescribed points together with points flagged by
two distinct grids. Their cardinality is bounded by the prescribed
cardinality plus the number of pair/flag incidences. This upper counting
cost is integrable and its expectation, scaled by the square of the
spacing, tends to zero for the actual reciprocal-grid laws.
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem finite_active_of_weighted_count_ne_top {T I : Type*}
    (E : I → Set T) (t : T)
    (hfinite : weightedBandIncidence E (fun _ => 1) t ≠ ∞) :
    {i | t ∈ E i}.Finite := by
  have hf := ENNReal.finite_const_le_of_tsum_ne_top hfinite
    (by norm_num : (1 : ℝ≥0∞) ≠ 0)
  apply hf.subset
  intro i hi
  have hi' : t ∈ E i := hi
  change 1 ≤ (E i).indicator (fun _ => ENNReal.ofReal 1) t
  rw [indicator_of_mem hi', ENNReal.ofReal_one]

theorem weighted_count_toReal_eq_ncard {T I : Type*}
    (E : I → Set T) (t : T) (hfinite : {i | t ∈ E i}.Finite) :
    (weightedBandIncidence E (fun _ => 1) t).toReal = ({i | t ∈ E i}.ncard : ℝ) := by
  classical
  rw [weightedBandIncidence_toReal_eq E (fun _ => 1) (fun _ => zero_le_one),
    tsum_eq_sum (s := hfinite.toFinset)]
  · rw [ncard_eq_toFinset_card _ hfinite]
    calc
      _ = ∑ _i ∈ hfinite.toFinset, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact indicator_of_mem (show t ∈ E i from hfinite.mem_toFinset.mp hi) _
      _ = _ := by simp
  · intro i hi
    exact indicator_of_notMem (s := E i)
      (fun h => hi (hfinite.mem_toFinset.mpr h)) _

def gridTerminalIndices {n : ℕ} {P S : Type*} (F : Set S)
    (h : ℝ) (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (θ : Fin n → ℝ) : Set S :=
  F ∪ {s | ∃ p, θ ∈ pairedLatticeIncidence h
    (a (pairs p).1 s) (b (pairs p).1 s)
    (a (pairs p).2 s) (b (pairs p).2 s) (pairs p).1 (pairs p).2}

noncomputable def gridTerminalCost {n : ℕ} {P S : Type*} (F : Set S)
    (h : ℝ) (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (θ : Fin n → ℝ) : ℝ :=
  (F.ncard : ℝ) + (gridCollisionCount h pairs a b θ).toReal

/-- Counting pair/point incidences only overcounts the actual terminal
indices, including the prescribed finite set. -/
theorem finite_gridTerminalIndices_and_card_le {n : ℕ} {P S : Type*}
    (F : Set S) (hF : F.Finite) (h : ℝ)
    (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ)
    (hfinite : gridCollisionCount h pairs a b θ ≠ ∞) :
    (gridTerminalIndices F h pairs a b θ).Finite ∧
      ((gridTerminalIndices F h pairs a b θ).ncard : ℝ) ≤
        gridTerminalCost F h pairs a b θ := by
  let E : P × S → Set (Fin n → ℝ) := fun ps => pairedLatticeIncidence h
    (a (pairs ps.1).1 ps.2) (b (pairs ps.1).1 ps.2)
    (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2) (pairs ps.1).1 (pairs ps.1).2
  let A : Set (P × S) := {ps | θ ∈ E ps}
  have hA : A.Finite := finite_active_of_weighted_count_ne_top E θ hfinite
  have hset : gridTerminalIndices F h pairs a b θ = F ∪ Prod.snd '' A := by
    ext s
    simp only [gridTerminalIndices, mem_union, mem_ofPred_eq, mem_image, Prod.exists,
      A, E, exists_eq_right]
  refine ⟨hset ▸ hF.union (hA.image _), ?_⟩
  have hcount : (gridCollisionCount h pairs a b θ).toReal = (A.ncard : ℝ) :=
    weighted_count_toReal_eq_ncard E θ hA
  rw [gridTerminalCost, hcount, hset]
  exact_mod_cast (ncard_union_le F (Prod.snd '' A)).trans
    (Nat.add_le_add_left (ncard_image_le hA) F.ncard)

theorem integrable_gridTerminalCost {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] (F : Set S) {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Integrable (gridTerminalCost F h pairs a b)
      (Measure.pi (fun _ : Fin n => shiftLaw h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  exact (integrable_const _).add
    (scaled_integral_gridCollisionCount_le hh pairs hpairs a b hwidth hwidth2).1

theorem gridTerminalCost_nonneg {n : ℕ} {P S : Type*} (F : Set S) (h : ℝ)
    (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ) (θ : Fin n → ℝ) :
    0 ≤ gridTerminalCost F h pairs a b θ :=
  add_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg

/-- The finitely many prescribed terminals also have vanishing scaled
expected cost. The number of pair/flag incidences was handled by the
clipped-product summability estimate. -/
theorem scaled_gridTerminalCost_mean_tendsto_zero {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] (F : Set S)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    Tendsto (fun N => reciprocalGridStep N ^ 2 *
      (∫ θ, gridTerminalCost F (reciprocalGridStep N) pairs a b θ
        ∂reciprocalGridLaw n N)) atTop (𝓝 0) := by
  have hconst : Tendsto (fun N => reciprocalGridStep N ^ 2 * (F.ncard : ℝ))
      atTop (𝓝 0) := by
    simpa using (reciprocalGridStep_tendsto_zero.pow 2).mul_const (F.ncard : ℝ)
  have hsum := hconst.add
    (scaled_gridCollisionCount_mean_tendsto_zero pairs hpairs a b hwidth hwidth2)
  simp only [zero_add] at hsum
  convert hsum using 1
  funext N
  let := reciprocalGridLaw_isProbabilityMeasure n N
  have hi := (scaled_integral_gridCollisionCount_le (reciprocalGridStep_pos N)
    pairs hpairs a b hwidth hwidth2).1
  change Integrable (fun θ => (gridCollisionCount (reciprocalGridStep N) pairs a b θ).toReal)
    (reciprocalGridLaw n N) at hi
  dsimp only [gridTerminalCost]
  rw [integral_add (integrable_const _) hi, integral_const,
    probReal_univ, one_smul, mul_add]

/-- Uniform wedge-mean bounds give spacing and shifts with a small terminal
counting cost for every sufficiently narrow staircase. -/
theorem exists_grid_with_finite_terminals_and_good_widths
    {n : ℕ} {P S : Type*} [Fintype P] [Countable S]
    (F : Set S) (hF : F.Finite)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2))
    (W : ℕ → ℕ → (Fin n → ℝ) → ℝ) (Q : ℕ → (Fin n → ℝ) → Prop)
    {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hWi : ∀ N k, Integrable (W N k) (reciprocalGridLaw n N))
    (hW0 : ∀ N k, ∀ᵐ θ ∂reciprocalGridLaw n N, 0 ≤ W N k θ)
    (hQ : ∀ N, ∀ᵐ θ ∂reciprocalGridLaw n N, Q N θ)
    (hWmean : ∀ᶠ N in atTop, ∀ k,
      (∫ θ, W N k θ ∂reciprocalGridLaw n N) < η / 4) :
    ∃ (N : ℕ) (θ : Fin n → ℝ), reciprocalGridStep N < δ ∧ Q N θ ∧
      (gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).Finite ∧
      reciprocalGridStep N *
        Real.sqrt ((gridTerminalIndices F (reciprocalGridStep N) pairs a b θ).ncard : ℝ) < η ∧
      ∃ᶠ k in atTop, W N k θ < η := by
  have hfinite N : ∀ᵐ θ ∂reciprocalGridLaw n N,
      gridCollisionCount (reciprocalGridStep N) pairs a b θ ≠ ∞ := by
    have hm : Measurable (gridCollisionCount (reciprocalGridStep N) pairs a b) :=
      measurable_weightedBandIncidence _ _ (fun _ =>
        measurableSet_pairedLatticeIncidence (reciprocalGridStep_pos N) _ _ _ _ _ _)
    exact (ae_lt_top hm (lintegral_gridCollisionCount_lt_top
      (reciprocalGridStep_pos N) pairs hpairs a b hwidth hwidth2).ne).mono
        (fun _ hx => hx.ne)
  obtain ⟨N, θ, hN, hθ, hJ, hW⟩ := exists_reciprocal_grid_with_frequently_small_widths
    W (fun N => gridTerminalCost F (reciprocalGridStep N) pairs a b)
    (fun N θ => Q N θ ∧ gridCollisionCount (reciprocalGridStep N) pairs a b θ ≠ ∞)
    hη hδ hWi
    (fun N => integrable_gridTerminalCost F (reciprocalGridStep_pos N)
      pairs hpairs a b hwidth hwidth2)
    hW0 (fun N => Filter.Eventually.of_forall (gridTerminalCost_nonneg F _ pairs a b))
    (fun N => (hQ N).and (hfinite N)) hWmean
    (scaled_gridTerminalCost_mean_tendsto_zero F pairs hpairs a b hwidth hwidth2)
  obtain ⟨hterm, hcard⟩ := finite_gridTerminalIndices_and_card_le
    F hF _ pairs a b θ hθ.2
  exact ⟨N, θ, hN, hθ.1, hterm,
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcard)
      (reciprocalGridStep_pos N).le).trans_lt hJ, hW⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
