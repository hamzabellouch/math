import OAI.Analysis.IrrationalRotation.Product.ProductTailTrimming
import OAI.Analysis.IrrationalRotation.Analysis.BlockReciprocalSum
import OAI.Analysis.IrrationalRotation.Analysis.GeometricTails
import OAI.Analysis.IrrationalRotation.Sampling.SamplingHorizon
import Mathlib.Basic.ENNReal.BigOperators

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.ProductModel

theorem block_angle_sum_le {m : ℕ} (hm : 0 < m) (K : ℝ) (hK : 0 < K)
    (θ : Fin m → ℝ) (hθ : ∀ r, θ r ≤ 2 / ((m : ℝ) * K)) :
    (∑' r, ENNReal.ofReal (θ r)) ≤ ENNReal.ofReal (2 / K) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  calc
    (∑' r, ENNReal.ofReal (θ r)) ≤
        ∑' _r : Fin m, ENNReal.ofReal (2 / ((m : ℝ) * K)) :=
      ENNReal.tsum_le_tsum (fun r => ENNReal.ofReal_le_ofReal (hθ r))
    _ = ENNReal.ofReal (∑ r : Fin m, 2 / ((m : ℝ) * K)) := by
      rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    _ = ENNReal.ofReal (2 / K) := by
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

theorem enumerated_tail_angle_sum_le
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ≤ 2 / ((m (e i).1 : ℝ) * K (e i).1)) (l : ℕ) :
    (∑' i : {i : ℕ // l < (e i).1}, ENNReal.ofReal (θ i)) ≤
      2 * ∑' j : {j : ℕ // l < j}, ENNReal.ofReal (1 / K j) := by
  have hsub : (∑' i : {i : ℕ // l < (e i).1}, ENNReal.ofReal (θ i)) =
      ∑' i : ℕ, ({i : ℕ | l < (e i).1}).indicator (fun i => ENNReal.ofReal (θ i)) i :=
    tsum_subtype ({i : ℕ | l < (e i).1}) (fun i => ENNReal.ofReal (θ i))
  rw [hsub]
  rw [← e.symm.tsum_eq (fun i : ℕ =>
    ({i : ℕ | l < (e i).1}).indicator (fun i => ENNReal.ofReal (θ i)) i)]
  simp only [Set.indicator, Set.mem_ofPred_eq, e.apply_symm_apply]
  have hsplit : (∑' p : Σ j, Fin (m j),
      if l < p.1 then ENNReal.ofReal (θ (e.symm p)) else 0) =
      ∑' j, ∑' r : Fin (m j), if l < j then ENNReal.ofReal (θ (e.symm ⟨j, r⟩)) else 0 :=
    ENNReal.tsum_sigma (fun j r => if l < j then ENNReal.ofReal (θ (e.symm ⟨j, r⟩)) else 0)
  rw [hsplit]
  calc
    (∑' j, ∑' r : Fin (m j), if l < j then ENNReal.ofReal (θ (e.symm ⟨j, r⟩)) else 0) ≤
        ∑' j, if l < j then ENNReal.ofReal (2 / K j) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro j
      by_cases hj : l < j
      · simp only [hj, ite_true]
        apply block_angle_sum_le (hm j) (K j) (hK j)
        intro r
        simpa only [e.apply_symm_apply] using hθ (e.symm ⟨j, r⟩)
      · simp only [hj, ite_false, tsum_zero, le_refl]
    _ = 2 * ∑' j : {j : ℕ // l < j}, ENNReal.ofReal (1 / K j) := by
      have hjsub : (∑' j : {j : ℕ // l < j}, ENNReal.ofReal (1 / K j)) =
          ∑' j : ℕ, ({j : ℕ | l < j}).indicator (fun j => ENNReal.ofReal (1 / K j)) j :=
        tsum_subtype ({j : ℕ | l < j}) (fun j => ENNReal.ofReal (1 / K j))
      rw [hjsub, ← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro j
      by_cases hj : l < j
      · simp only [Set.indicator, Set.mem_ofPred_eq, hj, ite_true]
        rw [show (2 : ℝ) / K j = 2 * (1 / K j) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      · simp [Set.indicator, hj]

def strictBlockTailEquiv (l : ℕ) : ℕ ≃ {j : ℕ // l < j} where
  toFun n := ⟨l + 1 + n, by omega⟩
  invFun j := j.val - l - 1
  left_inv n := by dsimp; omega
  right_inv j := by apply Subtype.ext; dsimp; omega

theorem enumerated_tail_angle_sum_le_four_div
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1))
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ≤ 2 / ((m (e i).1 : ℝ) * K (e i).1)) (l : ℕ) :
    (∑' i : {i : ℕ // l < (e i).1}, ENNReal.ofReal (θ i)) ≤
      ENNReal.ofReal (4 / K (l + 1)) := by
  have hs : Summable (fun n : ℕ => 1 / K (l + 1 + n)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff (l + 1)).mpr
      (InvariantProjection.GeometricTails.summable_reciprocal hK hdouble)
  have heq : (∑' j : {j : ℕ // l < j}, ENNReal.ofReal (1 / K j)) =
      ∑' n : ℕ, ENNReal.ofReal (1 / K (l + 1 + n)) :=
    ((strictBlockTailEquiv l).tsum_eq (fun j => ENNReal.ofReal (1 / K j))).symm
  refine (enumerated_tail_angle_sum_le m hm K hK e θ hθ l).trans ?_
  rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun n => (one_div_pos.mpr (hK (l + 1 + n))).le) hs]
  calc
    2 * ENNReal.ofReal (∑' n : ℕ, 1 / K (l + 1 + n)) ≤
        2 * ENNReal.ofReal (2 / K (l + 1)) := by
      gcongr
      exact InvariantProjection.GeometricTails.tsum_reciprocal_tail_le hK hdouble l
    _ = ENNReal.ofReal (4 / K (l + 1)) := by
      rw [show (4 : ℝ) / K (l + 1) = 2 * (2 / K (l + 1)) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

theorem sampling_horizon_ratio_le_decay {m K : ℝ} (hm : 0 < m)
    (hK : m ^ ((3 / 4 : ℝ) * m) ≤ K) :
    m ^ ((7 / 10 : ℝ) * m) / K ≤ m ^ (-m / 20) := by
  calc
    m ^ ((7 / 10 : ℝ) * m) / K ≤
        m ^ ((7 / 10 : ℝ) * m) / m ^ ((3 / 4 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hm.le _)
        (Real.rpow_pos_of_pos hm _) hK
    _ = m ^ (-m / 20) := by
      rw [← Real.rpow_sub hm]
      congr 1
      ring

theorem enumerated_sampled_tail_angle_sum_le_decay
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1))
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ : ∀ i, θ i ≤ 2 / ((m (e i).1 : ℝ) * K (e i).1)) (l n : ℕ)
    (hn : (n : ℝ) ≤ (m l : ℝ) ^ ((7 / 10 : ℝ) * m l))
    (hscale : (m l : ℝ) ^ ((3 / 4 : ℝ) * m l) ≤ K (l + 1)) :
    ENNReal.ofReal (n : ℝ) *
      (∑' i : {i : ℕ // l < (e i).1}, ENNReal.ofReal (θ i)) ≤
        ENNReal.ofReal (4 * (m l : ℝ) ^ (-(m l : ℝ) / 20)) := by
  have hmpos : (0 : ℝ) < m l := Nat.cast_pos.mpr (hm l)
  calc
    ENNReal.ofReal (n : ℝ) *
        (∑' i : {i : ℕ // l < (e i).1}, ENNReal.ofReal (θ i)) ≤
        ENNReal.ofReal (n : ℝ) * ENNReal.ofReal (4 / K (l + 1)) := by
      gcongr
      exact enumerated_tail_angle_sum_le_four_div m hm K hK hdouble e θ hθ l
    _ = ENNReal.ofReal ((n : ℝ) * (4 / K (l + 1))) :=
      (ENNReal.ofReal_mul (Nat.cast_nonneg n)).symm
    _ ≤ ENNReal.ofReal (4 * (m l : ℝ) ^ (-(m l : ℝ) / 20)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (n : ℝ) * (4 / K (l + 1)) ≤
            (m l : ℝ) ^ ((7 / 10 : ℝ) * m l) * (4 / K (l + 1)) :=
          mul_le_mul_of_nonneg_right hn (div_nonneg (by norm_num) (hK (l + 1)).le)
        _ = 4 * ((m l : ℝ) ^ ((7 / 10 : ℝ) * m l) / K (l + 1)) := by ring
        _ ≤ 4 * (m l : ℝ) ^ (-(m l : ℝ) / 20) :=
          mul_le_mul_of_nonneg_left (sampling_horizon_ratio_le_decay hmpos hscale) (by norm_num)

def blockPrefixCoordinates (m : ℕ → ℕ) (e : ℕ ≃ Σ j, Fin (m j)) (l : ℕ) : Finset ℕ :=
  ((Finset.range (l + 1)).sigma (fun j => (Finset.univ : Finset (Fin (m j))))).preimage
    e e.injective.injOn

@[simp] theorem mem_blockPrefixCoordinates (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j)) (l i : ℕ) :
    i ∈ blockPrefixCoordinates m e l ↔ (e i).1 ≤ l := by
  simp [blockPrefixCoordinates]

theorem blockPrefix_tail_tsum (m : ℕ → ℕ) (e : ℕ ≃ Σ j, Fin (m j))
    (l : ℕ) (θ : ℕ → ℝ) :
    (∑' i : {i : ℕ // i ∉ blockPrefixCoordinates m e l}, ENNReal.ofReal (θ i)) =
      ∑' i : {i : ℕ // l < (e i).1}, ENNReal.ofReal (θ i) := by
  let d : {i : ℕ // i ∉ blockPrefixCoordinates m e l} ≃ {i : ℕ // l < (e i).1} :=
    (Equiv.refl ℕ).subtypeEquiv (by intro i; simp)
  exact d.tsum_eq (fun i => ENNReal.ofReal (θ i))

theorem weighted_block_tailOrderFailure_le_decay
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1))
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ i, θ i ≤ 2 / ((m (e i).1 : ℝ) * K (e i).1)) (l n : ℕ)
    (hn : (n : ℝ) ≤ (m l : ℝ) ^ ((7 / 10 : ℝ) * m l))
    (hscale : (m l : ℝ) ^ ((3 / 4 : ℝ) * m l) ≤ K (l + 1))
    (w : (blockPrefixCoordinates m e l → Circle) → ℝ≥0∞) (hw : Measurable w) :
    (baseMeasure.withDensity
      (fun x : Base => w (fun i : blockPrefixCoordinates m e l => x i)))
        (tailOrderFailure (blockPrefixCoordinates m e l) θ n) ≤
      (baseMeasure.withDensity
        (fun x : Base => w (fun i : blockPrefixCoordinates m e l => x i))) Set.univ *
          ENNReal.ofReal (4 * (m l : ℝ) ^ (-(m l : ℝ) / 20)) := by
  refine (TailTrimming.weighted_tailOrderFailure_le
    (blockPrefixCoordinates m e l) θ hθ0 n w hw).trans ?_
  apply mul_le_mul_right
  rw [blockPrefix_tail_tsum]
  exact enumerated_sampled_tail_angle_sum_le_decay m hm K hK hdouble e θ hθ l n hn hscale

theorem orbitAverage_block_unordered_le_decay
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j) (K : ℕ → ℝ) (hK : ∀ j, 0 < K j)
    (hdouble : ∀ j, 2 * K j ≤ K (j + 1))
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : ∀ i, θ i ≤ 2 / ((m (e i).1 : ℝ) * K (e i).1)) (l M : ℕ)
    (hM : (M : ℝ) ≤ (m l : ℝ) ^ ((7 / 10 : ℝ) * m l))
    (hscale : (m l : ℝ) ^ ((3 / 4 : ℝ) * m l) ≤ K (l + 1))
    (N : Finset ℕ) (hN : ∀ n ∈ N, n ≤ M)
    (w : ℕ → (blockPrefixCoordinates m e l → Circle) → ℝ≥0∞)
    (hw : ∀ n ∈ N, Measurable (w n))
    (hprefix : ∀ n ∈ N,
      ∀ᵐ x ∂baseMeasure.withDensity
        (fun x : Base => w n (fun i : blockPrefixCoordinates m e l => x i)),
        ∀ i ∈ blockPrefixCoordinates m e l, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i)) :
    TailTrimming.orbitAverageMeasure θ N
      (fun n x => w n (fun i : blockPrefixCoordinates m e l => x i))
        TailTrimming.orderedPairEventᶜ ≤
      TailTrimming.orbitAverageMeasure θ N
        (fun n x => w n (fun i : blockPrefixCoordinates m e l => x i)) Set.univ *
          ENNReal.ofReal (4 * (m l : ℝ) ^ (-(m l : ℝ) / 20)) := by
  refine (TailTrimming.orbitAverageMeasure_unordered_le
    (blockPrefixCoordinates m e l) N θ hθ0 M hN w hw hprefix).trans ?_
  apply mul_le_mul_right
  rw [blockPrefix_tail_tsum]
  exact enumerated_sampled_tail_angle_sum_le_decay m hm K hK hdouble e θ hθ l M hM hscale

theorem tendsto_four_mul_block_decay {m : ℕ → ℝ}
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun l => 4 * m l ^ (-m l / 20)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun l => 4 * (m l)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hm).const_mul 4
  apply squeeze_zero' _ _ hinv
  · filter_upwards [hm.eventually_ge_atTop 20] with l hl
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [hm.eventually_ge_atTop 20] with l hl
    exact mul_le_mul_of_nonneg_left (SamplingHorizon.decay_le_inv hl) (by norm_num)

theorem tendsto_four_mul_block_decay_of_growth (m : ℕ → ℕ)
    (hm : ∀ l, 2 ^ l ≤ m l) :
    Tendsto (fun l => 4 * (m l : ℝ) ^ (-(m l : ℝ) / 20)) atTop (𝓝 0) := by
  apply tendsto_four_mul_block_decay
  apply tendsto_atTop_mono (fun l => ?_)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  exact_mod_cast hm l

end Invariant233.ProductModel

end

end OAI
