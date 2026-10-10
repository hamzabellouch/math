import OAI.Analysis.IrrationalRotation.Model.BlockProductCoupling
import OAI.Analysis.IrrationalRotation.Couplings.ProductCoupling
import OAI.Analysis.IrrationalRotation.Analysis.BlockAverageSum
import OAI.Analysis.IrrationalRotation.Analysis.ConsecutiveBlocks
import Mathlib.Analysis.PSeries

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.OrderedProductCoupling
open InvariantProjection.IndependentAngles

lemma sourceKappa_nonneg (s : ℕ) : 0 ≤ sourceKappa s := by
  unfold sourceKappa
  positivity

lemma sourceKappa_pos (s : ℕ) : 0 < sourceKappa s := by
  unfold sourceKappa
  positivity

lemma sourceKappa_le (s : ℕ) : sourceKappa s ≤ 1 / 100 := by
  unfold sourceKappa
  apply (div_le_iff₀ (by positivity : 0 < 100 * ((s : ℝ) + 1))).2
  nlinarith [Nat.cast_nonneg (α := ℝ) s]

lemma summable_sourceKappa_sq : Summable (fun s => sourceKappa s ^ 2) := by
  have hbase : Summable (fun s : ℕ => 1 / ((s + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by norm_num))
  apply (hbase.mul_left (1 / 10000 : ℝ)).congr
  intro s
  have hs : (s : ℝ) + 1 ≠ 0 := by positivity
  simp only [sourceKappa, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

lemma blockDensityBound_pos (κ : ℕ → ℝ) : 0 < blockDensityBound κ :=
  Real.exp_pos _

lemma blockDensityBound_sq (κ : ℕ → ℝ) :
    blockDensityBound κ ^ 2 = Real.exp (20 * (2 * (∑' s, κ s ^ 2) + 1)) := by
  rw [blockDensityBound, pow_two, ← Real.exp_add]
  congr 1
  ring

section BlockData
variable (m : ℕ → ℕ) (κ a b : ℕ → ℝ)
    (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ)

lemma energyBound_ofBlocks (i : ℕ) :
    energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) i =
      (20 * (2 * κ (e i).1 ^ 2 + if (e i).1 = tag then 1 else 0)) /
        (m (e i).1 : ℝ) := by
  unfold energyBound ofBlocks
  ring

theorem ofBlocks_energy_sum (hsκ : Summable (fun s => κ s ^ 2)) :
    Summable (energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag)) ∧
    (∑' i, energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) i) =
      20 * (2 * (∑' s, κ s ^ 2) + 1) := by
  let u : ℕ → ℝ := fun s => 20 * (2 * κ s ^ 2 + if s = tag then 1 else 0)
  have hu : ∀ s, 0 ≤ u s := by
    intro s
    dsimp [u]
    split_ifs <;> positivity
  have htag : Summable (fun s : ℕ => if s = tag then (1 : ℝ) else 0) :=
    (hasSum_ite_eq tag (1 : ℝ)).summable
  have hsu : Summable u := ((hsκ.mul_left 2).add htag).mul_left 20
  have hblock := enumerated_block_average m (fun s => by have := hm s; omega) u hu hsu e
  have henergy : energyBound (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) =
      fun i => u (e i).1 / (m (e i).1 : ℝ) := by
    funext i
    exact energyBound_ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag i
  rw [henergy]
  refine ⟨hblock.1, hblock.2.trans ?_⟩
  dsimp [u]
  rw [tsum_mul_left, (hsκ.mul_left 2).tsum_add htag, tsum_mul_left,
    tsum_ite_eq]

theorem exists_hybrid_density_ofBlocks (hsκ : Summable (fun s => κ s ^ 2))
    (ε : ℕ → Bool) :
    ∃ H : Endpoint → ℝ, MemLp H 2 baseMeasure ∧ (0 ≤ᵐ[baseMeasure] H) ∧
      (∫ x, H x ∂baseMeasure) = 1 ∧
      eLpNorm H 2 baseMeasure ≤ ENNReal.ofReal (blockDensityBound κ) ∧
      (law (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag)).map (hybridEndpoint ε) =
        baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨hs, htotal⟩ := ofBlocks_energy_sum m κ a b hκ0 hκ hm ha ha' hb hb' e tag hsκ
  have hbound : Real.exp ((20 * (2 * (∑' s, κ s ^ 2) + 1)) / 2) =
      blockDensityBound κ := by
    unfold blockDensityBound
    congr 1
    ring
  simpa only [hbound] using exists_hybrid_density
    (ofBlocks m κ a b hκ0 hκ hm ha ha' hb hb' e tag) ε hs htotal.le

end BlockData

theorem exists_source_hybrid_density
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) (ε : ℕ → Bool) :
    ∃ H : Endpoint → ℝ, MemLp H 2 baseMeasure ∧ (0 ≤ᵐ[baseMeasure] H) ∧
      (∫ x, H x ∂baseMeasure) = 1 ∧
      eLpNorm H 2 baseMeasure ≤ ENNReal.ofReal (blockDensityBound sourceKappa) ∧
      (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
        ha ha' hb hb' e tag)).map (hybridEndpoint ε) =
        baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) :=
  exists_hybrid_density_ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
    ha ha' hb hb' e tag summable_sourceKappa_sq ε

theorem exists_source_consecutive_couplings
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4) :
    ∃ e : ℕ ≃ Σ s, Fin (m s),
      (∀ i : Σ s, Fin (m s), e.symm i = (∑ r ∈ Finset.range i.1, m r) + i.2.val) ∧
      ∀ (tag : ℕ) (ε : ℕ → Bool),
        ∃ H : Endpoint → ℝ, MemLp H 2 baseMeasure ∧ (0 ≤ᵐ[baseMeasure] H) ∧
          (∫ x, H x ∂baseMeasure) = 1 ∧
          eLpNorm H 2 baseMeasure ≤ ENNReal.ofReal (blockDensityBound sourceKappa) ∧
          (law (ofBlocks m sourceKappa a b sourceKappa_nonneg sourceKappa_le hm
            ha ha' hb hb' e tag)).map (hybridEndpoint ε) =
            baseMeasure.withDensity (fun x => ENNReal.ofReal (H x)) := by
  obtain ⟨e, he⟩ := exists_consecutiveBlocks_equiv m (fun s => by have := hm s; omega)
  exact ⟨e, he, fun tag ε => exists_source_hybrid_density m a b hm ha ha' hb hb' e tag ε⟩

end Invariant233.OrderedProductCoupling

end OAI
