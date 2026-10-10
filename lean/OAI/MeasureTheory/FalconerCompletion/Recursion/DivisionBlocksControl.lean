import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Shells.RegularizationLeaves

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open MeasureTheory
open scoped ENNReal
variable {d : ℕ}
theorem division_blocks_control {H N : ℕ} (hH : 0 < H) (hN : H ≤ N) :
    0 < N/H ∧ N/(N/H)+1 ≤ 2*H := by
  have hB : 0 < N/H := Nat.div_pos hN hH
  have hrem : N < (N/H+1)*H := by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ N hH
  have hmul : (N/H+1)*H ≤ (2*(N/H))*H := Nat.mul_le_mul_right H (by omega)
  have hlt : N < (2*H)*(N/H) := by nlinarith
  have hdiv : N/(N/H) < 2*H := (Nat.div_lt_iff_lt_mul hB).mpr hlt
  exact ⟨hB,by omega⟩

theorem division_block_width {H N : ℕ} {lam : ℝ} (hlam : 0 ≤ lam)
    (hH : 1 ≤ lam*(H:ℝ)) : ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) := by
  have hn : (((N/H)*H:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N H
  have h0 : 0 ≤ ((N/H:ℕ):ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left hH h0
  have hl := mul_le_mul_of_nonneg_left hn hlam
  simp only [Nat.cast_mul, mul_one] at hh hl
  nlinarith

theorem exists_regularization_block_control {lam : ℝ} (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧ ∀ N ≥ N₀,
      0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
      ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧
      (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam := by
  obtain ⟨H,hH⟩ := exists_nat_gt (1/lam)
  have hHp : 0 < H := by
    have hp : 0 < (H:ℝ) := (one_div_pos.mpr hlam).trans hH
    exact_mod_cast hp
  have hHl : 1 ≤ lam*(H:ℝ) := by
    have := (div_lt_iff₀ hlam).mp hH
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (((2*H+1:ℕ):ℝ)/lam)
  refine ⟨H,max H M,hHp,?_⟩
  intro N hN
  have hHN : H ≤ N := (le_max_left _ _).trans hN
  have hMN : M ≤ N := (le_max_right _ _).trans hN
  have hc := division_blocks_control hHp hHN
  refine ⟨lt_of_lt_of_le hHp hHN,hc.1,hc.2,division_block_width hlam.le hHl,?_⟩
  have hreal : ((2*H+1:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hm := (div_lt_iff₀ hlam).mp hM
    have hn : (M:ℝ) ≤ N := by exact_mod_cast hMN
    nlinarith
  have hcount : ((N/(N/H)+2:ℕ):ℝ) ≤ (N:ℝ)*lam := by
    have hh : N/(N/H)+2 ≤ 2*H+1 := by omega
    have hhR : ((N/(N/H)+2:ℕ):ℝ) ≤ ((2*H+1:ℕ):ℝ) := by exact_mod_cast hh
    exact hhR.trans hreal
  rw [← Real.rpow_natCast (2:ℝ) (N/(N/H)+2), ← Real.rpow_natCast (2:ℝ) N,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount

theorem blockDepth_brackets {N n B : ℕ} (hn : n ≤ N) (hB : 0 < B) :
    let i := (N-n)/B
    i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
      blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B := by
  dsimp only
  have hlo := Nat.div_mul_le_self (N-n) B
  have hhi := Nat.lt_mul_div_succ (N-n) hB
  have hi : (N-n)/B ≤ N/B := Nat.div_le_div_right (Nat.sub_le _ _)
  simp only [blockDepth]
  rw [Nat.mul_comm B] at hhi
  have hgap := blockDepth_gap N B ((N-n)/B)
  dsimp only [blockDepth] at hgap
  omega

theorem profile_bracket_mass_bound {R C lam m₀ mₙ m₁ x₀ xₙ x₁ : ℝ}
    (hR : 1 ≤ R) (hC : 0 < C) (hCL : C ≤ R^lam)
    (hml : m₁-mₙ ≤ (d:ℝ)*lam) (hmu : mₙ-m₀ ≤ (d:ℝ)*lam)
    (hlo : R^(-m₁)/C ≤ x₁) (hhi : x₀ ≤ C*R^(-m₀))
    (hxl : x₁ ≤ xₙ) (hxu : xₙ ≤ x₀) :
    R^(-((d:ℝ)+1)*lam)*R^(-mₙ) ≤ xₙ ∧ xₙ ≤ R^(((d:ℝ)+1)*lam)*R^(-mₙ) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  constructor
  · apply le_trans ?_ (hlo.trans hxl)
    apply (le_div_iff₀ hC).mpr
    calc
      R^(-((d:ℝ)+1)*lam)*R^(-mₙ)*C ≤ R^(-((d:ℝ)+1)*lam)*R^(-mₙ)*R^lam :=
        mul_le_mul_of_nonneg_left hCL (by positivity)
      _ = R^(-(d:ℝ)*lam-mₙ) := by rw [← Real.rpow_add hRp,← Real.rpow_add hRp]; congr 1; ring
      _ ≤ R^(-m₁) := Real.rpow_le_rpow_of_exponent_le hR (by nlinarith)
  · apply le_trans (hxu.trans hhi)
    calc
      C*R^(-m₀) ≤ R^lam*R^(-m₀) := mul_le_mul_of_nonneg_right hCL (by positivity)
      _ = R^(lam-m₀) := by rw [← Real.rpow_add hRp]; rfl
      _ ≤ R^(((d:ℝ)+1)*lam-mₙ) := Real.rpow_le_rpow_of_exponent_le hR (by nlinarith)
      _ = R^(((d:ℝ)+1)*lam)*R^(-mₙ) := Real.rpow_add hRp _ _

theorem sourceProfile_short_increment (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : (CellPath d)) {lam u v : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ N)
    (hshort : v-u ≤ B) :
    sourceProfile μ N B p v-sourceProfile μ N B p u ≤ (d:ℝ)*lam := by
  classical
  have hh := regularizedProfile_increment hN (show regularizationLeaves μ N ⊆ dyadicPaths N from Finset.filter_subset _ _)
    (regularizationLabel μ N B) hB p hu huv hv
  apply hh.2.trans
  apply (div_le_iff₀ (by exact_mod_cast hN : 0 < (N:ℝ))).mpr
  have hd : 0 ≤ (d:ℝ) := Nat.cast_nonneg _
  have hs := mul_le_mul_of_nonneg_left hshort hd
  have hw := mul_le_mul_of_nonneg_left hwidth hd
  nlinarith

theorem sourceClass_all_depth_comparison (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    {lam : ℝ} (hwidth : (B:ℝ) ≤ lam*(N:ℝ))
    (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p : (CellPath d)} (hp : p ∈ regularizationLeaves μ N)
    {n : ℕ} (hn : n ≤ N) {P : (CellPath d)}
    (hP : P ∈ (classLeaves (regularizationLeaves μ N) (regularizationLabel μ N B)
      (regularizationLabel μ N B p)).image (List.take n)) :
    ((2:ℝ)^N)^(-((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile μ N B p n) ≤
      (sourceClass μ N B p (treeCell P)).toReal ∧
    (sourceClass μ N B p (treeCell P)).toReal ≤
      ((2:ℝ)^N)^(((d:ℝ)+1)*lam)*((2:ℝ)^N)^(-sourceProfile μ N B p n) := by
  classical
  let i := (N-n)/B
  have hb := blockDepth_brackets hn hB
  change i < N/B+1 ∧ blockDepth N B (i+1) ≤ n ∧ n ≤ blockDepth N B i ∧
    blockDepth N B i-n ≤ B ∧ n-blockDepth N B (i+1) ≤ B at hb
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  let ρ := sourceClass μ N B p
  have : IsProbabilityMeasure ρ := sourceClass_probability μ N B hp
  have hgp := sourceClass_grid_comparison μ hN hB hp (Nat.le_of_lt hb.1)
    (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hgm := sourceClass_grid_comparison μ hN hB hp (by omega : i+1 ≤ N/B+1)
    (Finset.mem_image.mpr ⟨q,hq,rfl⟩)
  have hmono₁ : ρ (treeCell (q.take (blockDepth N B i))) ≤
      ρ (treeCell (q.take n)) := by
    apply measure_mono
    have hh := treeCell_subset_take (q.take (blockDepth N B i)) n
    simpa only [List.take_take,Nat.min_eq_left hb.2.2.1] using hh
  have hmono₀ : ρ (treeCell (q.take n)) ≤
      ρ (treeCell (q.take (blockDepth N B (i+1)))) := by
    apply measure_mono
    have hh := treeCell_subset_take (q.take n) (blockDepth N B (i+1))
    simpa only [List.take_take,Nat.min_eq_left hb.2.1] using hh
  have hml := sourceProfile_short_increment μ hN hB p hwidth
    (Nat.cast_nonneg n) (Nat.cast_le.mpr hb.2.2.1)
    (Nat.cast_le.mpr (Nat.sub_le N (i*B))) (by
      simpa only [Nat.cast_sub hb.2.2.1] using
        (show (((blockDepth N B i-n):ℕ):ℝ) ≤ (B:ℝ) by exact_mod_cast hb.2.2.2.1))
  have hmu := sourceProfile_short_increment μ hN hB p hwidth
    (Nat.cast_nonneg (blockDepth N B (i+1))) (Nat.cast_le.mpr hb.2.1) (Nat.cast_le.mpr hn) (by
      simpa only [Nat.cast_sub hb.2.1] using
        (show (((n-blockDepth N B (i+1)):ℕ):ℝ) ≤ (B:ℝ) by exact_mod_cast hb.2.2.2.2))
  exact profile_bracket_mass_bound (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
    (by positivity) hlarge hml hmu hgp.1 hgm.2
    (ENNReal.toReal_mono (measure_ne_top ρ _) hmono₁)
    (ENNReal.toReal_mono (measure_ne_top ρ _) hmono₀)

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
