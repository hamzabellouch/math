import OAI.NumberTheory.TotientAsymptotic.AdditiveShellUnion
import OAI.NumberTheory.TotientAsymptotic.TailCutScale

namespace OAI

/-! Additive boundary slices vanish after the smooth-cofactor cost. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def normalizedShellLoss (K C J : ℝ) (H : ℕ) : ℝ :=
  (4*C)*Real.exp (C*boxErrorTail (P H))*projectedEnvelope J (P H)*
    (Real.exp (K*cofactorScale H)*boxErrorTail H)

lemma normalizedShellLoss_tendsto (K C : ℝ) {J : ℝ} (hJ : 0 < J) :
    Tendsto (normalizedShellLoss K C J) atTop (nhds 0) := by
  have ht0 : Tendsto (fun H => C*boxErrorTail (P H)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using (boxErrorTail_tendsto.comp P_tendsto).const_mul C
  have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp ht0
  have hp := (summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto
  have ht := cofactor_boxErrorTail_tendsto K
  change Tendsto (fun H => normalizedShellLoss K C J H) atTop (nhds 0)
  simpa only [normalizedShellLoss, Function.comp_def, mul_zero, Real.exp_zero] using
    ((he.const_mul (4*C)).mul hp).mul ht

/-- All retained boundary slices have negligible normalized volume, even
after paying for every admissible smooth cofactor. -/
theorem normalized_additive_shell_loss (hren : FordRenewalInput) (K : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ hRN : R x H ≤ L x H,
      Real.exp (K*cofactorScale H)*
        volume.real (additiveBoxShell x (R x H) (L x H) hRN)/G x (m x) ≤ δ H := by
  obtain ⟨C, hC, hcost⟩ := uniform_box_error_cost hren
  obtain ⟨D, hD, hambient⟩ := ambient_box_error_cost hren
  obtain ⟨J, hJ, hproj⟩ := uniform_projected_volume_bound hren
  let A := C+D
  have hA : 0 < A := add_pos hC hD
  refine ⟨normalizedShellLoss K A J, normalizedShellLoss_tendsto K A hJ, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with H hH
  have hPH := P_lt_self hH
  filter_upwards [hcost, hambient, hproj,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (2*H))] with x hx ha hp hB hm
  intro hRN
  have hHm : H ≤ m x := by omega
  have hPm : P H ≤ m x := hPH.le.trans hHm
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H ≤ m x := Nat.sub_le _ _
  have hb := additiveBoxShell_volume_bound hB hL hRN
  have hE : 0 ≤ (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) := by
    apply mul_nonneg (by positivity)
    exact add_nonneg (boxTopError_nonneg hB.le) (Finset.sum_nonneg
      (fun i _ => mul_nonneg (g_pos _).le (boxSlackError_nonneg _ _)))
  have hEc : (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ A*boxErrorTail (P H) := by
    have hh := hx (P H) hPm
    change (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ C*boxErrorTail (P H) at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (boxErrorTail_nonneg _))
  have hRc := ha H (L x H) hm hLm
  have hRc' : 2*(L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ 4*A*boxErrorTail H := by
    calc
      _ = 2*((L x H : ℝ)/B x*(boxTopError x+
          ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1))) := by ring
      _ ≤ 2*(2*D*boxErrorTail H) := mul_le_mul_of_nonneg_left hRc (by norm_num)
      _ ≤ _ := by
        have hh : D ≤ A := by dsimp [A]; linarith
        have hmul := mul_le_mul_of_nonneg_right hh (boxErrorTail_nonneg H)
        nlinarith
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp (P H) hPm)
  change G x (L x H) ≤ projectedEnvelope J (P H)*G x (m x) at hG
  have hvol : volume.real (additiveBoxShell x (R x H) (L x H) hRN) ≤
      (4*A*boxErrorTail H)*Real.exp (A*boxErrorTail (P H))*
        (projectedEnvelope J (P H)*G x (m x)) := by
    apply hb.trans
    apply mul_le_mul (mul_le_mul hRc' (Real.exp_le_exp.mpr hEc) (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) hA.le) (boxErrorTail_nonneg H))) hG (G_pos hB _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.le)
      (boxErrorTail_nonneg H)) (Real.exp_pos _).le
  apply (div_le_iff₀ (G_pos hB (m x))).mpr
  apply (mul_le_mul_of_nonneg_left hvol (Real.exp_pos _).le).trans_eq
  dsimp [normalizedShellLoss]
  ring

end TotientAsymptotic

end

end OAI
