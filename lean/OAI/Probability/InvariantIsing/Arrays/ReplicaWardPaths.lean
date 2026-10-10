import OAI.Probability.InvariantIsing.Arrays.OverlapTestSeparation
import OAI.Probability.InvariantIsing.Arrays.ReplicaProductSymbols
import OAI.Probability.InvariantIsing.Arrays.ReplicaProductRoots
import OAI.Probability.InvariantIsing.Arrays.PathSymbolAEUniqueness

namespace OAI

/-! Extract pointwise path equations from continuous Ward tests, then pass
those equations to symbols and right roots. All Ward hypotheses in this
module are internal consequences to be supplied by rotation calculus. -/

noncomputable section

open MeasureTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def offWardPath (ρa ρb δ da db : ℝ) (a b : ℝ → ℝ) (s : ℝ) : ℝ :=
  ρa * b s - ρb * a s + δ * replicaProductPath da a db b s

def diagonalWardResidual (ρa ρb δ da db : ℝ) (a b : ℝ → ℝ) : ℝ :=
  ρa * db - ρb * da + δ * replicaProductDiagonal da db a b

lemma ae_offWardPath_zero_of_tests (p : OverlapPath) (ζ : Measure ℝ)
    [IsProbabilityMeasure ζ] (hl : pathMeasure.map p = ζ)
    (ρa ρb δ da db : ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : ∀ r, |f r| ≤ A) (hgB : ∀ r, |g r| ≤ B)
    (htest : ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      (∫ s, Φ (p s) * offWardPath ρa ρb δ da db (fun u => f (p u))
        (fun u => g (p u)) s ∂pathMeasure) = 0) :
    ∀ᵐ s ∂pathMeasure, offWardPath ρa ρb δ da db (fun u => f (p u))
      (fun u => g (p u)) s = 0 := by
  let W : ℝ → ℝ := fun r => ρa * g r - ρb * f r + δ * replicaProductValue ζ da db f g r
  let C := |ρa| * B + |ρb| * A + |δ| * (|da| * B + A * |db| + 4 * (A * B))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hW : Continuous W := ((hg.const_mul ρa).sub (hf.const_mul ρb)).add
    ((continuous_replicaProductValue ζ da db f g hf hg hA hB hfB hgB).const_mul δ)
  have hWB (r : ℝ) : |W r| ≤ C := by
    have h1 : |ρa * g r| ≤ |ρa| * B := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hgB r) (abs_nonneg _)
    have h2 : |ρb * f r| ≤ |ρb| * A := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hfB r) (abs_nonneg _)
    have h3 : |δ * replicaProductValue ζ da db f g r| ≤
        |δ| * (|da| * B + A * |db| + 4 * (A * B)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (replicaProductValue_abs_le ζ da db f g hf.measurable hg.measurable hA hB hfB hgB r)
        (abs_nonneg _)
    exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)
  have he : ∀ᵐ s ∂pathMeasure,
      W (p s) = offWardPath ρa ρb δ da db (fun u => f (p u)) (fun u => g (p u)) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    dsimp only [W, offWardPath]
    rw [replicaProductPath_eq_value p ζ hl da db f g hf.measurable hg.measurable hA hfB hgB
      ⟨hs.1.le, hs.2.le⟩]
  have hz : ∀ᵐ s ∂pathMeasure, W (p s) = 0 := by
    apply ae_zero_of_continuous_overlap_tests pathMeasure p p.measurable W hW hC hWB
    intro Φ hΦ K hK hΦK
    calc
      (∫ s, Φ (p s) * W (p s) ∂pathMeasure) =
          ∫ s, Φ (p s) * offWardPath ρa ρb δ da db (fun u => f (p u))
            (fun u => g (p u)) s ∂pathMeasure := by
        apply integral_congr_ae
        filter_upwards [he] with s hs
        rw [hs]
      _ = 0 := htest Φ hΦ K hK hΦK
  filter_upwards [he, hz] with s hs hsz
  exact hs.symm.trans hsz

lemma intervalIntegrable_replicaProductPath (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db s t : ℝ) :
    IntervalIntegrable (replicaProductPath da a db b) volume s t := by
  have hai (v w : ℝ) : IntervalIntegrable a volume v w :=
    intervalIntegrable_of_measurable_abs_le ha haB v w
  have hbi (v w : ℝ) : IntervalIntegrable b volume v w :=
    intervalIntegrable_of_measurable_abs_le hb hbB v w
  have hab (u : ℝ) : |a u * b u| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (haB u) (hbB u) (abs_nonneg _) hA
  have habi (v w : ℝ) : IntervalIntegrable (fun u => a u * b u) volume v w :=
    intervalIntegrable_of_measurable_abs_le (ha.mul hb) hab v w
  have hTa : Continuous (fun u => ∫ v in u..1, a v) := continuous_tail_integral hai 1
  have hTb : Continuous (fun u => ∫ v in u..1, b v) := continuous_tail_integral hbi 1
  have hP : Continuous (fun u => ∫ v in 0..u, a v * b v) := intervalIntegral.continuous_primitive habi 0
  have he : replicaProductPath da a db b = fun u =>
      da * b u + a u * db -
        (a u * (∫ v in u..1, b v) + b u * (∫ v in u..1, a v)) -
        (u * (a u * b u) + ∫ v in 0..u, a v * b v) := by
    funext u
    unfold replicaProductPath pathSymbol
    ring
  rw [he]
  exact ((((hbi s t).const_mul da).add ((hai s t).mul_const db)).sub
    (((hai s t).mul_continuousOn hTb.continuousOn).add
      ((hbi s t).mul_continuousOn hTa.continuousOn))).sub
    (((habi s t).continuousOn_mul continuousOn_id).add (hP.intervalIntegrable s t))

lemma pathSymbol_ward_linear (ρa ρb δ da db dc : ℝ) (a b c : ℝ → ℝ) (s : ℝ)
    (hai : IntervalIntegrable a volume s 1) (hbi : IntervalIntegrable b volume s 1)
    (hci : IntervalIntegrable c volume s 1) :
    pathSymbol (ρa * db - ρb * da + δ * dc)
      (fun u => ρa * b u - ρb * a u + δ * c u) s =
      ρa * pathSymbol db b s - ρb * pathSymbol da a s + δ * pathSymbol dc c s := by
  unfold pathSymbol
  rw [intervalIntegral.integral_add (((hbi.const_mul ρa).sub (hai.const_mul ρb))) (hci.const_mul δ),
    intervalIntegral.integral_sub (hbi.const_mul ρa) (hai.const_mul ρb)]
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma pathSymbol_zero_of_ae {a : ℝ → ℝ} (ha : ∀ᵐ s ∂pathMeasure, a s = 0)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (has : a s = 0) : pathSymbol 0 a s = 0 := by
  have hav : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → a u = 0 :=
    (ae_restrict_iff' measurableSet_Ioo).mp ha
  have hi : (∫ u in s..1, a u) = 0 := by
    calc
      _ = ∫ u in s..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hav, volume.ae_ne (1 : ℝ)] with u hu hune humem
        rw [uIoc_of_le hs.2.le] at humem
        exact hu ⟨hs.1.trans humem.1, lt_of_le_of_ne humem.2 hune⟩
      _ = 0 := by simp
  simp only [pathSymbol, has, hi, mul_zero, sub_zero]

 theorem offWardPath_symbol (ρa ρb δ da db : ℝ) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B)
    (hd : diagonalWardResidual ρa ρb δ da db a b = 0)
    (hw : ∀ᵐ s ∂pathMeasure, offWardPath ρa ρb δ da db a b s = 0) :
    ∀ᵐ s ∂pathMeasure, ρb * pathSymbol da a s - ρa * pathSymbol db b s =
      δ * pathSymbol da a s * pathSymbol db b s := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hw] with s hs hws
  have hai := intervalIntegrable_of_measurable_abs_le ha haB s 1
  have hbi := intervalIntegrable_of_measurable_abs_le hb hbB s 1
  have hci := intervalIntegrable_replicaProductPath a b ha hb hA haB hbB da db s 1
  have he := pathSymbol_ward_linear ρa ρb δ da db (replicaProductDiagonal da db a b)
    a b (replicaProductPath da a db b) s hai hbi hci
  change diagonalWardResidual ρa ρb δ da db a b = 0 at hd
  change offWardPath ρa ρb δ da db a b s = 0 at hws
  change pathSymbol (diagonalWardResidual ρa ρb δ da db a b)
    (offWardPath ρa ρb δ da db a b) s = _ at he
  rw [hd, pathSymbol_zero_of_ae hw hs hws,
    replicaProductPath_symbol a b ha hb hA haB hbB da db ⟨hs.1.le, hs.2.le⟩] at he
  linarith

 theorem offWardPath_root (ρa ρb δ da db : ℝ) (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ} (hA : 0 ≤ A)
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) {ra rb : ℝ}
    (hra : Tendsto a (𝓝[>] 0) (𝓝 ra)) (hrb : Tendsto b (𝓝[>] 0) (𝓝 rb))
    (hw : ∀ᵐ s ∂pathMeasure, offWardPath ρa ρb δ da db a b s = 0) :
    ρb * ra - ρa * rb = δ *
      ((da - ∫ u in 0..1, a u) * rb + ra * (db - ∫ u in 0..1, b u)) := by
  have hp := replicaProductPath_root_tendsto da db a b ha hb hA haB hbB hra hrb
  have ht := ((hrb.const_mul ρa).sub (hra.const_mul ρb)).add (hp.const_mul δ)
  have hz : Tendsto (offWardPath ρa ρb δ da db a b) (𝓝[>] 0)
      (𝓝 (ρa * rb - ρb * ra + δ *
        ((da - ∫ u in 0..1, a u) * rb + ra * (db - ∫ u in 0..1, b u)))) := ht
  have he := ae_constant_right_root hw hz
  linarith

end InvariantIsing

end

end OAI
