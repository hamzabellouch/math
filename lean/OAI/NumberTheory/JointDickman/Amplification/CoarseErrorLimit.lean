import OAI.NumberTheory.JointDickman.Probability.PublishedCoarseChannel
import OAI.NumberTheory.JointDickman.Amplification.CoarseGrid

namespace OAI

/-! # Vanishing fine-grid errors in the coarse channel -/

namespace JointDickman

open Filter
open scoped Topology

theorem polynomial_error_div_tendsto {δ : ℕ → ℝ} {C p s : ℝ}
    (hC : 0 ≤ C) (hps : s < p)
    (hδ : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-s) ≤ δ B) :
    Tendsto (fun B : ℕ => C * (B : ℝ) ^ (-p) / δ B) atTop (𝓝 0) := by
  have hlim : Tendsto (fun B : ℕ => C * (B : ℝ) ^ (-(p - s))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop (sub_pos.mpr hps)).comp tendsto_natCast_atTop_atTop).const_mul C
  have hb : ∀ᶠ B : ℕ in atTop,
      0 ≤ C * (B : ℝ) ^ (-p) / δ B ∧
        C * (B : ℝ) ^ (-p) / δ B ≤ C * (B : ℝ) ^ (-(p - s)) := by
    filter_upwards [hδ, eventually_gt_atTop 0] with B hδB hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have hlow : 0 < (B : ℝ) ^ (-s) := Real.rpow_pos_of_pos hB0 _
    have hn : 0 ≤ C * (B : ℝ) ^ (-p) := mul_nonneg hC (Real.rpow_nonneg hB0.le _)
    refine ⟨div_nonneg hn (hlow.trans_le hδB).le, ?_⟩
    calc
      _ ≤ C * (B : ℝ) ^ (-p) / (B : ℝ) ^ (-s) := div_le_div_of_nonneg_left hn hlow hδB
      _ = _ := by
        rw [mul_div_assoc, ← Real.rpow_sub hB0]
        congr 2
        ring
  exact squeeze_zero' (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2) hlim

theorem channelMesh_fine_tendsto {m : ℕ} (hm : 0 < m) :
    Tendsto (fun B : ℕ => channelMesh (channelFineCount m B)) atTop (𝓝 0) := by
  have ht : Tendsto (fun B : ℕ => (5 / 2 : ℝ) / B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun B => by unfold channelMesh; positivity) _ ht
  filter_upwards [eventually_ge_atTop 1] with B hB
  exact channelMesh_fine_upper hm hB

theorem channelMesh_fine_lower {m : ℕ} (hm : 0 < m) :
    ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(3 : ℝ)) ≤ channelMesh (channelFineCount m B) := by
  filter_upwards [channelFineCount_eventually_le_square hm, eventually_gt_atTop 0] with B hn hB
  simpa only [Nat.totient_one, Nat.cast_one, div_one] using
    (channel_atom_lower (q := 1) hB (channelFineCount_pos hm hB) hn (by omega : 1 ≤ B))

theorem coarseChannelError_fine_tendsto (A T M L θ mesh : ℝ) {C : ℝ} (hC : 0 ≤ C)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun B : ℕ => coarseChannelError A C T M L θ B
      (channelMesh (channelFineCount m B)) mesh (5 / 2)) atTop
      (𝓝 (8 * T * (2 * θ) ^ (1 / 4 : ℝ) * A + 20 * M * L * mesh)) := by
  let δ : ℕ → ℝ := fun B => channelMesh (channelFineCount m B)
  have hδ := channelMesh_fine_tendsto hm
  have hlow := channelMesh_fine_lower hm
  have hδsq : ∀ᶠ B : ℕ in atTop, (B : ℝ) ^ (-(6 : ℝ)) ≤ δ B * δ B := by
    filter_upwards [hlow, eventually_gt_atTop 0] with B hlowB hB
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have heq : (B : ℝ) ^ (-(6 : ℝ)) = (B : ℝ) ^ (-(3 : ℝ)) * (B : ℝ) ^ (-(3 : ℝ)) := by
      rw [← Real.rpow_add hB0]
      norm_num
    rw [heq]
    exact mul_self_le_mul_self (Real.rpow_nonneg hB0.le _) hlowB
  have hE := polynomial_error_div_tendsto hC (by norm_num : (3 : ℝ) < 80) hlow
  have hκ : Tendsto (fun B : ℕ => (9 / (8 * (auxiliaryCutoff B : ℝ))) / δ B) atTop (𝓝 0) := by
    apply (polynomial_error_div_tendsto (by norm_num : (0 : ℝ) ≤ 9 / 8)
      (by norm_num : (3 : ℝ) < 1000) hlow).congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    rw [primeComparisonError_power hB]
  have hκsq : Tendsto (fun B : ℕ => (9 / (8 * (auxiliaryCutoff B : ℝ))) / (δ B * δ B)) atTop (𝓝 0) := by
    apply (polynomial_error_div_tendsto (by norm_num : (0 : ℝ) ≤ 9 / 8)
      (by norm_num : (6 : ℝ) < 1000) hδsq).congr'
    filter_upwards [eventually_gt_atTop 0] with B hB
    rw [primeComparisonError_power hB]
  have hη : Tendsto (fun B : ℕ => C * (B : ℝ) ^ (-(80 : ℝ)) / δ B + L * δ B) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hE.add (hδ.const_mul L)
  have hrow : Tendsto (fun B : ℕ => A +
      (C * (B : ℝ) ^ (-(80 : ℝ)) + 9 / (8 * (auxiliaryCutoff B : ℝ))) / δ B)
      atTop (𝓝 A) := by
    simpa only [add_div, add_zero] using (hE.add hκ).const_add A
  have hinv : Tendsto (fun B : ℕ => 1 / auxiliaryRatio B) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop auxiliaryRatio_tendsto
  have htail := (hinv.const_add (2 * θ)).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
  have hfirst := ((htail.const_mul T).const_mul 8).mul hrow
  have hsecond := (((hη.const_mul (2 * M)).add (hη.pow 2)).add hκsq).const_add (2 * M * L * mesh)
  convert hfirst.add ((hsecond.const_mul 4).mul_const (5 / 2)) using 1
  · funext B
    unfold coarseChannelError
    dsimp only [δ]
    ring
  · norm_num
    ring

end JointDickman

end OAI
