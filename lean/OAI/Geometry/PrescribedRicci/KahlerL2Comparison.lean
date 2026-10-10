import Mathlib
import OAI.Geometry.PrescribedRicci.KahlerLocalL2Comparison
import OAI.Geometry.PrescribedRicci.MongeAmpereEnergy

namespace OAI

/-! Kahler L2 Comparison. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped SchwartzMap ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X}

lemma finite_norm_sq_le_sum {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] (f : ∀ i, E i) : ‖f‖ ^ 2 ≤ ∑ i, ‖f i‖ ^ 2 := by
  have hn : 0 ≤ ∑ i, ‖f i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : ‖f‖ ≤ Real.sqrt (∑ i, ‖f i‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    exact (Real.le_sqrt (norm_nonneg _) hn).2
      (Finset.single_le_sum (fun j _ => sq_nonneg ‖f j‖) (Finset.mem_univ i))
  exact (Real.le_sqrt (norm_nonneg _) hn).1 hb

omit [T2Space X] in
lemma smooth_square_bounded (ρ : Smooth A) : ∃ M : ℝ, 0 < M ∧ ∀ x, ‖ρ x‖ ^ 2 ≤ M := by
  obtain ⟨b,hb⟩ := isCompact_univ.bddAbove_image (ρ.continuous.norm.pow 2).continuousOn
  refine ⟨max b 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun x => ?_⟩
  exact (hb (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)

namespace Localizers
variable {ι : Type*} [Fintype ι] (D : Localizers A ι)

lemma norm_coordinate_le (f : Smooth A) (i : ι) :
    ‖schwartzCoord 0 (localize A (D.index i) (D.weight i) (D.support_sub i) f)‖ ≤
      ‖D.embed 0 f‖ := norm_le_pi_norm (D.coordinates 0 f) i

 
theorem kahler_L2_comparison (g : KaehlerMetric A) : ∃ C B : ℝ, 0 < C ∧ 0 < B ∧
    ∀ f : Smooth A,
      ‖D.embed 0 f‖ ^ 2 ≤ C * g.integral (fun x => ‖f x‖ ^ 2) ∧
      g.integral (fun x => ‖f x‖ ^ 2) ≤ B * ‖D.embed 0 f‖ ^ 2 := by
  have hl (i : ι) := local_weighted_L2_comparison g (D.index i) (D.weight i) (D.support_sub i)
  choose a b ha hb hab using hl
  choose M hM hMb using (fun i : ι => smooth_square_bounded (D.weight i))
  let c := coordinateVolumeFactor d
  have hc : 0 < c := coordinateVolumeFactor_pos d
  let C := 1 + ∑ i, c * M i / a i
  let B := 1 + (Fintype.card ι : ℝ) * ∑ i, b i / c
  have hC : 0 < C := by
    have hh : 0 ≤ ∑ i, c * M i / a i := Finset.sum_nonneg
      (fun i _ => div_nonneg (mul_nonneg hc.le (hM i).le) (ha i).le)
    dsimp [C]; linarith
  have hB : 0 < B := by
    have hh : 0 ≤ (Fintype.card ι : ℝ) * ∑ i, b i / c := mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun i _ => div_nonneg (hb i).le hc.le))
    dsimp [B]; linarith
  refine ⟨C,B,hC,hB,fun f => ?_⟩
  let I := g.integral (fun x => ‖f x‖ ^ 2)
  let Iw (i : ι) := g.integral (fun x => ‖D.weight i x * f x‖ ^ 2)
  have hI : 0 ≤ I := g.integral_nonneg (fun _ => sq_nonneg _)
  have hIw (i : ι) : Iw i ≤ M i * I := by
    rw [← g.integral_const_mul]
    apply g.integral_mono ((D.weight i).continuous.fun_mul f.continuous |>.norm.pow 2)
      (continuous_const.mul (f.continuous.norm.pow 2))
    intro x
    change ‖D.weight i x * f x‖ ^ 2 ≤ M i * ‖f x‖ ^ 2
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hMb i x) (sq_nonneg _)
  have hp (i : ι) :
      ‖schwartzCoord 0 (localize A (D.index i) (D.weight i) (D.support_sub i) f)‖ ^ 2 ≤
        (c * M i / a i) * I := by
    calc
      _ ≤ (c * Iw i) / a i := (le_div_iff₀ (ha i)).2 (by rw [mul_comm]; exact (hab i f).1)
      _ ≤ (c * (M i * I)) / a i := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hIw i) hc.le) (ha i).le
      _ = _ := by ring
  have hq (i : ι) : Iw i ≤ (b i / c) * ‖D.embed 0 f‖ ^ 2 := by
    calc
      _ ≤ (b i * ‖schwartzCoord 0 (localize A (D.index i) (D.weight i) (D.support_sub i) f)‖ ^ 2) / c :=
        (le_div_iff₀ hc).2 (by rw [mul_comm]; exact (hab i f).2)
      _ ≤ (b i * ‖D.embed 0 f‖ ^ 2) / c := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
          (D.norm_coordinate_le f i)) (hb i).le) hc.le
      _ = _ := by ring
  constructor
  · calc
      _ = ‖D.coordinates 0 f‖ ^ 2 := rfl
      _ ≤ ∑ i, ‖D.coordinates 0 f i‖ ^ 2 := finite_norm_sq_le_sum _
      _ ≤ ∑ i, (c * M i / a i) * I := Finset.sum_le_sum (fun i _ => hp i)
      _ = (∑ i, c * M i / a i) * I := (Finset.sum_mul _ _ _).symm
      _ ≤ C * I := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hI
  · have hi : I ≤ (Fintype.card ι : ℝ) * ∑ i, Iw i := by
      dsimp only [I, Iw]
      rw [← g.integral_sum Finset.univ (fun i x => ‖D.weight i x * f x‖ ^ 2) (fun i _ =>
        ((D.weight i).continuous.fun_mul f.continuous).norm.pow 2), ← g.integral_const_mul]
      apply g.integral_mono (f.continuous.norm.pow 2)
        (continuous_const.mul (continuous_finsetSum _ (fun i _ =>
          ((D.weight i).continuous.fun_mul f.continuous).norm.pow 2)))
      intro x
      have hs : ∑ i, D.weight i x * f x = f x := by rw [← Finset.sum_mul, D.sum_one, one_mul]
      calc
        ‖f x‖ ^ 2 = ‖∑ i, D.weight i x * f x‖ ^ 2 := by rw [hs]
        _ ≤ (∑ i, ‖D.weight i x * f x‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))).2 (norm_sum_le _ _)
        _ ≤ _ := sq_sum_le_card_mul_sum_sq
    calc
      I ≤ (Fintype.card ι : ℝ) * ∑ i, Iw i := hi
      _ ≤ (Fintype.card ι : ℝ) * ∑ i, (b i / c) * ‖D.embed 0 f‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hq i)) (Nat.cast_nonneg _)
      _ = ((Fintype.card ι : ℝ) * ∑ i, b i / c) * ‖D.embed 0 f‖ ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ B * ‖D.embed 0 f‖ ^ 2 := mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (sq_nonneg _)

end Localizers
end GlobalElliptic

end
end

end OAI
