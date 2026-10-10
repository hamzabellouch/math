import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorWorkBound
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafDomains
import Mathlib.Algebra.Order.Floor.Div

namespace OAI

/-! # Exact integer construction of the separator sample size

The logarithm floor is the binary bit count of `3^(4g)`. The subsequent
floor is a natural-number division. Neither operation uses real arithmetic.
-/

namespace LowSpaceSubsetSum.SeparatorParameters

def logBits (m : ℕ) : ℕ := Nat.log 2 (3 ^ m)

def sampleSize (g k : ℕ) : ℕ :=
  (8 * g * g - logBits (4 * g) * (g - k)) / (16 * g)

def familyCount (g k : ℕ) (i : Fin 4) : ℕ :=
  (10 * g.choose (sampleSize g k)) ⌈/⌉
    (g / 2).choose (sampleSize g k - balancedBlockCounts 4 k i)

noncomputable def rationalBias (g k : ℕ) : ℝ :=
  (g : ℝ) / 2 - (logBits (4 * g) : ℝ) * ((g : ℝ) - k) / (16 * g)

theorem logBits_bounds (m : ℕ) :
    (logBits m : ℝ) ≤ (m : ℝ) * separatorAlpha ∧
      (m : ℝ) * separatorAlpha < (logBits m : ℝ) + 1 := by
  have hlog : Real.logb 2 ((3 ^ m : ℕ) : ℝ) = (m : ℝ) * separatorAlpha := by
    push_cast
    rw [Real.logb_pow]
    rfl
  have hfloor : ⌊(m : ℝ) * separatorAlpha⌋₊ = logBits m := by
    rw [← hlog]
    exact Real.natFloor_logb_natCast 2 (3 ^ m)
  have hnonneg : 0 ≤ (m : ℝ) * separatorAlpha := by
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (lt_trans (by norm_num) separatorAlpha_bounds.1))
  constructor
  · rw [← hfloor]
    exact Nat.floor_le hnonneg
  · rw [← hfloor]
    exact Nat.lt_floor_add_one _

theorem logBits_le (g : ℕ) : logBits (4 * g) ≤ 8 * g := by
  have h := (logBits_bounds (4 * g)).1
  have hmul := mul_le_mul_of_nonneg_left separatorAlpha_bounds.2.le
    (show (0 : ℝ) ≤ 4 * g by positivity)
  have hR : (logBits (4 * g) : ℝ) ≤ (8 * g : ℕ) := by
    push_cast at h ⊢
    nlinarith
  exact_mod_cast hR

theorem numerator_nonnegative (g k : ℕ) :
    logBits (4 * g) * (g - k) ≤ 8 * g * g :=
  Nat.mul_le_mul (logBits_le g) (Nat.sub_le g k)

theorem sampleSize_eq_floor (g k : ℕ) (hg : 0 < g) (hk : k ≤ g) :
    sampleSize g k = ⌊rationalBias g k⌋₊ := by
  have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have he : rationalBias g k =
      ((8 * g * g - logBits (4 * g) * (g - k) : ℕ) : ℝ) / (16 * g : ℕ) := by
    rw [Nat.cast_sub (numerator_nonnegative g k)]
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hk]
    unfold rationalBias
    field_simp [hgR]
    ring
  rw [he, Nat.floor_div_eq_div]
  rfl

theorem rationalBias_bounds (g k : ℕ) (hg : 0 < g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) :
    (g : ℝ) / 3 ≤ rationalBias g k ∧ rationalBias g k ≤ (g : ℝ) / 2 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hkR : (k : ℝ) ≤ g := by exact_mod_cast hk
  have hkloR : (2 : ℝ) * g ≤ 3 * k := by exact_mod_cast hklo
  have hbits : (logBits (4 * g) : ℝ) ≤ 8 * g := by exact_mod_cast logBits_le g
  have hprod := mul_le_mul_of_nonneg_right hbits (sub_nonneg.mpr hkR)
  have hsub : 0 ≤ (logBits (4 * g) : ℝ) * ((g : ℝ) - k) / (16 * g) := by positivity
  unfold rationalBias
  constructor
  · apply (le_sub_iff_add_le).mpr
    have hdiv : (logBits (4 * g) : ℝ) * ((g : ℝ) - k) / (16 * g) ≤ (g : ℝ) / 6 := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    linarith
  · linarith

theorem sampleSize_error (g k : ℕ) (hg : 0 < g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) :
    |(sampleSize g k : ℝ) - rationalBias g k| ≤ 1 := by
  rw [sampleSize_eq_floor g k hg hk]
  have hn := (rationalBias_bounds g k hg hk hklo).1
  have hnonneg : 0 ≤ rationalBias g k := le_trans (by positivity) hn
  exact abs_le.mpr ⟨by linarith [Nat.lt_floor_add_one (rationalBias g k)],
    by linarith [Nat.floor_le hnonneg]⟩

theorem rationalBias_error (g k : ℕ) (hg : 0 < g) (hk : k ≤ g) :
    |rationalBias g k - (g : ℝ) *
      ((k : ℝ) / (4 * g) + separatorY ((k : ℝ) / (4 * g)))| ≤ 1 := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hkR : (k : ℝ) ≤ g := by exact_mod_cast hk
  have hlo := (logBits_bounds (4 * g)).1
  have hhi := (logBits_bounds (4 * g)).2
  push_cast at hlo hhi
  have hgap0 : 0 ≤ 4 * (g : ℝ) * separatorAlpha - logBits (4 * g) := by linarith
  have hgap1 : 4 * (g : ℝ) * separatorAlpha - logBits (4 * g) ≤ 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hgap1 (sub_nonneg.mpr hkR)
  have he : rationalBias g k - (g : ℝ) *
      ((k : ℝ) / (4 * g) + separatorY ((k : ℝ) / (4 * g))) =
      (4 * (g : ℝ) * separatorAlpha - logBits (4 * g)) * ((g : ℝ) - k) / (16 * g) := by
    unfold rationalBias separatorY
    field_simp [hgR.ne']
    ring
  rw [he, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

theorem sampleSize_ideal_error (g k : ℕ) (hg : 0 < g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) :
    |(sampleSize g k : ℝ) - (g : ℝ) *
      ((k : ℝ) / (4 * g) + separatorY ((k : ℝ) / (4 * g)))| ≤ 2 := by
  have h : |(sampleSize g k : ℝ) - (g : ℝ) *
      ((k : ℝ) / (4 * g) + separatorY ((k : ℝ) / (4 * g)))| ≤
      |(sampleSize g k : ℝ) - rationalBias g k| +
      |rationalBias g k - (g : ℝ) *
        ((k : ℝ) / (4 * g) + separatorY ((k : ℝ) / (4 * g)))| := abs_sub_le _ _ _
  linarith [sampleSize_error g k hg hk hklo, rationalBias_error g k hg hk]

theorem sampleSize_upper (g k : ℕ) (hg : 0 < g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) (heven : 2 ∣ g) : sampleSize g k ≤ g / 2 := by
  have hnonneg : 0 ≤ rationalBias g k :=
    le_trans (by positivity) (rationalBias_bounds g k hg hk hklo).1
  have hf : (sampleSize g k : ℝ) ≤ rationalBias g k := by
    rw [sampleSize_eq_floor g k hg hk]
    exact Nat.floor_le hnonneg
  have hhalf : ((g / 2 : ℕ) : ℝ) = (g : ℝ) / 2 := Nat.cast_div heven (by norm_num)
  have h : (sampleSize g k : ℝ) ≤ (g / 2 : ℕ) := by
    rw [hhalf]
    exact hf.trans (rationalBias_bounds g k hg hk hklo).2
  exact_mod_cast h

theorem count_le_sampleSize (g k : ℕ) (hg : 64 ≤ g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) (i : Fin 4) : balancedBlockCounts 4 k i ≤ sampleSize g k := by
  have hg0 : 0 < g := by omega
  have hgR : (64 : ℝ) ≤ g := by exact_mod_cast hg
  have hkR : (k : ℝ) ≤ g := by exact_mod_cast hk
  have hcount := (abs_le.mp (balancedBlockCounts_error 4 k (by decide) i)).2
  have hsample := (abs_le.mp (sampleSize_error g k hg0 hk hklo)).1
  have hlow := (rationalBias_bounds g k hg0 hk hklo).1
  have h : (balancedBlockCounts 4 k i : ℝ) ≤ sampleSize g k := by linarith
  exact_mod_cast h

noncomputable def rounded (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2 * g ≤ 3 * k) : SeparatorExpectation.RoundedParameters g where
  e := fun _ => sampleSize g k
  c := balancedBlockCounts 4 k
  density := (k : ℝ) / (4 * g)
  large := hg
  even := heven
  count_le := count_le_sampleSize g k hg hk hklo
  size_le := fun _ => (sampleSize_upper g k (by omega) hk hklo heven).trans (Nat.div_le_self _ _)
  feasible := fun _ => (Nat.sub_le _ _).trans (sampleSize_upper g k (by omega) hk hklo heven)
  density_mem := by
    have hgR : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
    have hkR : (k : ℝ) ≤ g := by exact_mod_cast hk
    have hkloR : (2 : ℝ) * g ≤ 3 * k := by exact_mod_cast hklo
    constructor
    · apply (le_div_iff₀ (by positivity)).mpr
      linarith
    · apply (div_le_iff₀ (by positivity)).mpr
      linarith
  count_error := by
    intro i
    have he : (g : ℝ) * ((k : ℝ) / (4 * g)) = (k : ℝ) / 4 := by
      have hgR : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
      field_simp
    rw [he]
    exact balancedBlockCounts_error 4 k (by decide) i
  size_error := fun _ => sampleSize_ideal_error g k (by omega) hk hklo

theorem ceil_ratio (a d : ℕ) (hd : 0 < d) :
    ⌈(a : ℝ) / d⌉₊ = a ⌈/⌉ d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hdR).mpr
    have h := (ceilDiv_le_iff_le_mul hd).mp (le_refl (a ⌈/⌉ d))
    rw [mul_comm] at h
    exact_mod_cast h
  · apply (ceilDiv_le_iff_le_mul hd).mpr
    have h := (div_le_iff₀ hdR).mp (Nat.le_ceil ((a : ℝ) / d))
    rw [mul_comm] at h
    exact_mod_cast h

theorem familyCount_eq (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g)
    (hk : k ≤ g) (hklo : 2 * g ≤ 3 * k) :
    familyCount g k = (rounded g k hg heven hk hklo).counts := by
  funext i
  let S := rounded g k hg heven hk hklo
  have hd : 0 < (g / 2).choose (sampleSize g k - balancedBlockCounts 4 k i) :=
    Nat.choose_pos (S.feasible i)
  change (10 * g.choose (sampleSize g k)) ⌈/⌉
      (g / 2).choose (sampleSize g k - balancedBlockCounts 4 k i) =
    ⌈10 / (((g / 2).choose (sampleSize g k - balancedBlockCounts 4 k i) : ℝ) /
      g.choose (sampleSize g k))⌉₊
  rw [div_div_eq_mul_div]
  have he : (10 : ℝ) * (g.choose (sampleSize g k) : ℝ) =
      ((10 * g.choose (sampleSize g k) : ℕ) : ℝ) := by push_cast; rfl
  rw [he, ceil_ratio _ _ hd]

end LowSpaceSubsetSum.SeparatorParameters

end OAI
