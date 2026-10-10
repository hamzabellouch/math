import OAI.NumberTheory.TotientAsymptotic.StrictSlackShell

namespace OAI

/-! Strict-slack slices remain negligible after summing the smooth cofactors. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

def normalizedStrictSlackLoss (K A D J : ℝ) (H : ℕ) : ℝ :=
  Real.exp (A*boxErrorTail (P H))*projectedEnvelope J (P H)*
    (4*A*(Real.exp (K*cofactorScale H)*boxErrorTail H)+
      D*(Real.exp (K*cofactorScale H)/(H : ℝ)))

lemma normalizedStrictSlackLoss_tendsto (K A D : ℝ) {J : ℝ} (hJ : 0 < J) :
    Tendsto (normalizedStrictSlackLoss K A D J) atTop (nhds 0) := by
  have h1 : Tendsto (fun H => Real.exp (A*boxErrorTail (P H))) atTop (nhds 1) := by
    simpa only [mul_zero, Real.exp_zero, Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp
        ((boxErrorTail_tendsto.comp P_tendsto).const_mul A)
  have h2 := (summable_projectedEnvelope hJ).tendsto_atTop_zero.comp P_tendsto
  have h3 := ((cofactor_boxErrorTail_tendsto K).const_mul (4*A)).add
    ((cofactor_inverse_cutoff_tendsto K).const_mul D)
  change Tendsto (fun H => normalizedStrictSlackLoss K A D J H) atTop (nhds 0)
  simpa only [normalizedStrictSlackLoss, Function.comp_def, mul_zero, add_zero] using
    (h1.mul h2).mul h3

theorem normalized_strict_slack_shell (hren : FordRenewalInput) (K : ℝ) :
    ∃ δ : ℕ → ℝ, Tendsto δ atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ hRN : R x H ≤ L x H,
      Real.exp (K*cofactorScale H)*
        volume.real (strictSlackShell x (R x H) (L x H) hRN)/G x (m x) ≤ δ H := by
  obtain ⟨C,hC,hcost⟩ := uniform_box_error_cost hren
  obtain ⟨D,hD,hambient⟩ := ambient_box_error_cost hren
  obtain ⟨E,hE,hstrict⟩ := uniform_strict_slack_cost hren
  obtain ⟨J,hJ,hproj⟩ := uniform_projected_volume_bound hren
  let A := C+D
  have hA : 0 < A := add_pos hC hD
  refine ⟨normalizedStrictSlackLoss K A E J,
    normalizedStrictSlackLoss_tendsto K A E hJ,?_⟩
  filter_upwards [eventually_ge_atTop 2] with H hH
  have hPH := P_lt_self hH
  filter_upwards [hcost,hambient,hstrict,hproj,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (2*H))] with x hc ha hs hp hB hm
  intro hRN
  have hHm : H ≤ m x := by omega
  have hPm : P H ≤ m x := hPH.le.trans hHm
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H ≤ m x := Nat.sub_le _ _
  have hW : (L x H : ℝ)/B x*(strictTopWidth x+
      ∑ i : Fin (R x H), g (i.val+1)*strictSlackWidth x (i.val+1)) ≤
      4*A*boxErrorTail H+E/(H : ℝ) := by
    have heq : (L x H : ℝ)/B x*(strictTopWidth x+
        ∑ i : Fin (R x H), g (i.val+1)*strictSlackWidth x (i.val+1)) =
        2*((L x H : ℝ)/B x*(boxTopError x+
          ∑ i : Fin (R x H), g (i.val+1)*boxSlackError x (i.val+1)))+
        (L x H : ℝ)/B x*(B x/(m x : ℝ)^4+
          ∑ i : Fin (R x H), g (i.val+1)*
            ((11/10 : ℝ)*bandScale x (i.val+1)/((m x-(i.val+1) : ℕ) : ℝ)^4)) := by
      simp only [strictTopWidth,strictSlackWidth,mul_add,Finset.sum_add_distrib]
      simp_rw [show ∀ i : Fin (R x H), g (i.val+1)*(2*boxSlackError x (i.val+1)) =
        2*(g (i.val+1)*boxSlackError x (i.val+1)) by intro i; ring]
      rw [← Finset.mul_sum]
      ring
    rw [heq]
    have hr := ha H (L x H) hm hLm
    have ht := hs H (L x H) (by omega) hHm hLm
    have hh : D ≤ A := by dsimp [A]; linarith
    have hh' := mul_le_mul_of_nonneg_right hh (boxErrorTail_nonneg H)
    linarith
  have hExp : (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤
      A*boxErrorTail (P H) := by
    have hh := hc (P H) hPm
    change (L x H : ℝ)/B x*(boxTopError x+
      ∑ i : Fin (L x H), g (i.val+1)*boxSlackError x (i.val+1)) ≤ C*boxErrorTail (P H) at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith)
      (boxErrorTail_nonneg _))
  have hG := (div_le_iff₀ (G_pos hB (m x))).mp (hp (P H) hPm)
  change G x (L x H) ≤ projectedEnvelope J (P H)*G x (m x) at hG
  have hnon : 0 ≤ 4*A*boxErrorTail H+E/(H : ℝ) := by
    exact add_nonneg (mul_nonneg (by positivity) (boxErrorTail_nonneg _)) (by positivity)
  have hvol : volume.real (strictSlackShell x (R x H) (L x H) hRN) ≤
      (4*A*boxErrorTail H+E/(H : ℝ))*Real.exp (A*boxErrorTail (P H))*
        (projectedEnvelope J (P H)*G x (m x)) := by
    apply (strictSlackShell_volume_bound hB hL hRN).trans
    exact mul_le_mul
      (mul_le_mul hW (Real.exp_le_exp.mpr hExp) (Real.exp_pos _).le hnon)
      hG (G_pos hB _).le (mul_nonneg hnon (Real.exp_pos _).le)
  apply (div_le_iff₀ (G_pos hB (m x))).mpr
  apply (mul_le_mul_of_nonneg_left hvol (Real.exp_pos _).le).trans_eq
  dsimp [normalizedStrictSlackLoss]
  ring

end TotientAsymptotic

end

end OAI
