import OAI.Dynamics.StandardMap.BridgeScalar

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma transferProduct_back_step (v : ℕ → ℝ) (i : ℕ) (M : ℝ)
    (hv : |v (i+1)|+1 ≤ M) (z : ℂ) :
    ‖transferProduct v i z‖ ≤ M*‖transferProduct v (i+1) z‖ := by
  have he : transferStepInv (v (i+1)) (transferProduct v (i+1) z)=transferProduct v i z := by
    simp [transferProduct]
  rw [← he]
  exact ((transferStepInv _).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right ((transferStepInv_norm _).trans hv) (norm_nonneg _))

lemma prefix_stable_vector (v : ℕ → ℝ) (M : ℝ) (B : ℕ) (_hB : 1 ≤ B)
    (hM : 1 < M) (hq : M^(-(49/25:ℝ)) ≤ 1/2)
    (hv : ∀ i, 1 ≤ i → i ≤ B → |v i|+1 ≤ M)
    (hg : ∀ i, 1 ≤ i → i ≤ B → M^((49/50:ℝ)*(i:ℝ)) ≤ ‖transferProduct v i‖) :
    ∃ s : ℂ, ‖s‖=1 ∧ ‖transferProduct v B s‖=‖transferProduct v B‖⁻¹ ∧
      ∀ l, 1 ≤ l → l ≤ B → ‖transferProduct v l s‖ ≤ 3*M^(-(47/50:ℝ)*(l:ℝ)) := by
  choose a ha hmax horth hstable hnorm using fun i => (transferProduct_area v i).singular_pair
  refine ⟨quarterTurn (a B),by rw [norm_quarterTurn,ha],hstable B,?_⟩
  intro l hl hlB
  have hb:=stable_prefix_finite_bound (transferProduct v) a (fun i => ‖transferProduct v i‖) M l B hl hlB
    (fun i _ _ => transferProduct_area v i) (fun i _ _ => ha i) (fun _ _ _ => rfl)
    (fun i _ _ => hmax i) (fun i _ _ => hstable i)
    (fun i hi hiB z => transferProduct_back_step v i M (hv (i+1) (by omega) (by omega)) z)
  apply hb.trans
  apply stable_prefix_power_bound M _ l B hM hq hl hlB
  · exact fun i hli hiB => hg i (by omega) hiB
  · simpa only [Real.rpow_natCast] using (transferProduct_norm_bounds v M l (by linarith)
      (fun i hi hil => hv i hi (by omega))).2
lemma Complex.norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re|+|z.im| := by
  have he : z = (z.re : ℂ)+z.im*Complex.I := by apply Complex.ext <;> simp
  calc
    ‖z‖ = ‖(z.re : ℂ)+z.im*Complex.I‖ := congrArg norm he
    _ ≤ ‖(z.re : ℂ)‖+‖(z.im : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = _ := by simp
lemma vertical_im_lower (s : ℂ) (hu : ‖s‖=1) (hs : |s.re| ≤ 1/4) : 3/4 ≤ |s.im| := by
  have hh:=Complex.norm_le_abs_re_add_abs_im s
  rw [hu] at hh
  linarith
end StandardMapEntropy

end OAI
