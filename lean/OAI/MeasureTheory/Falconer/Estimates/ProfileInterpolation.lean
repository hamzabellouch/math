import OAI.MeasureTheory.Falconer.Recursion.BlockLeafCounts
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace PlanarFalconer

noncomputable def intervalRamp (a b u : ℝ) : ℝ := min u b - min u a

theorem intervalRamp_increment {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    0 ≤ intervalRamp a b v - intervalRamp a b u ∧
      intervalRamp a b v - intervalRamp a b u ≤ v-u := by
  unfold intervalRamp
  simp only [min_def]
  split_ifs <;> constructor <;> linarith

noncomputable def finiteRampProfile (d c : ℕ → ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, c i * intervalRamp (d (i+1)) (d i) u

theorem finiteRampProfile_continuous (d c : ℕ → ℝ) (K : ℕ) :
    Continuous (finiteRampProfile d c K) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((continuous_id.min continuous_const).sub
    (continuous_id.min continuous_const))

theorem intervalRamp_sum (d : ℕ → ℝ) (K : ℕ) (u : ℝ) :
    (∑ i ∈ Finset.range K, intervalRamp (d (i+1)) (d i) u) = min u (d 0)-min u (d K) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; unfold intervalRamp; ring

theorem finiteRampProfile_zero (d c : ℕ → ℝ) (K : ℕ) (hd : ∀ i, 0 ≤ d i) :
    finiteRampProfile d c K 0 = 0 := by
  simp [finiteRampProfile,intervalRamp, min_eq_left (hd _)]

theorem finiteRampProfile_increment (d c : ℕ → ℝ) (K : ℕ) {N C u v : ℝ}
    (hd : Antitone d) (h0 : d 0 = N) (hK : d K = 0)
    (hc : ∀ i < K, 0 ≤ c i ∧ c i ≤ C)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    0 ≤ finiteRampProfile d c K v - finiteRampProfile d c K u ∧
      finiteRampProfile d c K v - finiteRampProfile d c K u ≤ C*(v-u) := by
  have he : finiteRampProfile d c K v - finiteRampProfile d c K u =
      ∑ i ∈ Finset.range K, c i * (intervalRamp (d (i+1)) (d i) v -
        intervalRamp (d (i+1)) (d i) u) := by
    simp only [finiteRampProfile, ← Finset.sum_sub_distrib, mul_sub]
  rw [he]
  have hr (i : ℕ) := intervalRamp_increment (hd (Nat.le_succ i)) huv
  constructor
  · exact Finset.sum_nonneg fun i hi => mul_nonneg (hc i (Finset.mem_range.mp hi)).1 (hr i).1
  · calc
      _ ≤ ∑ i ∈ Finset.range K, C * (intervalRamp (d (i+1)) (d i) v -
          intervalRamp (d (i+1)) (d i) u) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hc i (Finset.mem_range.mp hi)).2 (hr i).1
      _ = C*(v-u) := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib,intervalRamp_sum,intervalRamp_sum,h0,hK]
        rw [min_eq_left hv,min_eq_right (hu.trans huv),min_eq_left (huv.trans hv),min_eq_right hu]
        ring

noncomputable def blockSlope (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B i : ℕ) (p : CellPath) : ℝ :=
  (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card : ℝ) /
    (N:ℝ) / ((blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ))

noncomputable def regularizedProfile (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B K : ℕ) (p : CellPath) : ℝ → ℝ :=
  finiteRampProfile (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) K

theorem blockSlope_bounds {N : ℕ} (hN : 0 < N) {L : Finset CellPath}
    (hL : L ⊆ dyadicPaths N) (F : CellPath → List ℕ) (B i : ℕ) (p : CellPath) :
    0 ≤ blockSlope L F N B i p ∧ blockSlope L F N B i p ≤ 2/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hd' : (blockDepth N B (i+1):ℝ) ≤ (blockDepth N B i:ℝ) := by exact_mod_cast hd
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  have hb' : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
      (blockDepth N B i) p).card:ℝ) ≤ 2*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
    have hbR : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
        (blockDepth N B i) p).card:ℝ) ≤ ((2*(blockDepth N B i-blockDepth N B (i+1)):ℕ):ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hd] using hbR
  unfold blockSlope
  constructor
  · positivity
  · by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
    · rw [he,div_zero]; positivity
    · have hp : 0 < (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) := lt_of_le_of_ne (sub_nonneg.mpr hd') (Ne.symm he)
      apply (div_le_iff₀ hp).mpr
      apply (div_le_iff₀ hN').mpr
      have heq : 2/(N:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ))*(N:ℝ) =
          2*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
        field_simp [hN'.ne']
      rw [heq]
      exact hb'

theorem regularizedProfile_continuous (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B K : ℕ) (p : CellPath) : Continuous (regularizedProfile L F N B K p) :=
  finiteRampProfile_continuous _ _ _

theorem regularizedProfile_zero (L : Finset CellPath) (F : CellPath → List ℕ)
    (N B K : ℕ) (p : CellPath) : regularizedProfile L F N B K p 0 = 0 :=
  finiteRampProfile_zero _ _ _ (fun _ => Nat.cast_nonneg _)

theorem regularizedProfile_increment {N : ℕ} (hN : 0 < N) {L : Finset CellPath}
    (hL : L ⊆ dyadicPaths N) (F : CellPath → List ℕ) {B : ℕ} (hB : 0 < B)
    (p : CellPath) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    0 ≤ regularizedProfile L F N B (N/B+1) p v - regularizedProfile L F N B (N/B+1) p u ∧
      regularizedProfile L F N B (N/B+1) p v - regularizedProfile L F N B (N/B+1) p u ≤
        2*(v-u)/(N:ℝ) := by
  have hh := finiteRampProfile_increment (fun i => (blockDepth N B i:ℝ))
    (fun i => blockSlope L F N B i p) (N/B+1)
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) (by simp [blockDepth])
    (by simp [blockDepth_terminal N hB]) (fun i _ => blockSlope_bounds hN hL F B i p) hu huv hv
  simpa only [regularizedProfile, div_mul_eq_mul_div] using hh

theorem regularizedProfile_adjusted_increment {N : ℕ} (hN : 0 < N) {L : Finset CellPath}
    (hL : L ⊆ dyadicPaths N) (F : CellPath → List ℕ) {B : ℕ} (hB : 0 < B)
    (p : CellPath) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N) :
    |(regularizedProfile L F N B (N/B+1) p v-v/(N:ℝ))-
      (regularizedProfile L F N B (N/B+1) p u-u/(N:ℝ))| ≤ (v-u)/(N:ℝ) := by
  have hh := regularizedProfile_increment hN hL F hB p hu huv hv
  apply abs_le.mpr
  constructor <;> simp only [sub_div,mul_div_assoc] at * <;> linarith

end PlanarFalconer

end OAI
