import OAI.Dynamics.StandardMap.CosineNull

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma transferStep_cone (v : ℝ) (B : ℝ) (hB : 2 ≤ B) (hv : B ≤ |v|) (z : ℂ)
    (hz : |z.im| ≤ |z.re|) :
    (B-1)*|z.re| ≤ |(transferStep v z).re| ∧ |(transferStep v z).im| ≤ |(transferStep v z).re| := by
  have htri := abs_sub_abs_le_abs_sub (v*z.re) z.im
  rw [abs_mul] at htri
  have hm := mul_le_mul_of_nonneg_right hv (abs_nonneg z.re)
  simp only [transferStep_re,transferStep_im]
  constructor <;> nlinarith [abs_nonneg z.re]
lemma transferProduct_cone (v : ℕ → ℝ) (B : ℝ) (hB : 2 ≤ B) (n : ℕ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → B ≤ |v i|) :
    (B-1)^n ≤ |(transferProduct v n 1).re| ∧ |(transferProduct v n 1).im| ≤ |(transferProduct v n 1).re| := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
      obtain ⟨hg,hc⟩ := ih (fun i hi hin => hv i hi (by omega))
      obtain ⟨h1,h2⟩ := transferStep_cone (v (n+1)) B hB (hv _ (by omega) le_rfl) (transferProduct v n 1) hc
      simp only [transferProduct,ContinuousLinearMap.comp_apply]
      refine ⟨?_,h2⟩
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ B-1 by linarith)
      nlinarith
lemma transferProduct_norm_lower_of_coefficients (v : ℕ → ℝ) (B : ℝ) (hB : 2 ≤ B) (n : ℕ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → B ≤ |v i|) : (B-1)^n ≤ ‖transferProduct v n‖ := by
  calc
    _  ≤  |(transferProduct v n 1).re| := (transferProduct_cone v B hB n hv).1
    _  ≤  ‖transferProduct v n 1‖ := Complex.abs_re_le_norm _
    _  ≤  ‖transferProduct v n‖ := by simpa using (transferProduct v n).le_opNorm (1:ℂ)
end StandardMapEntropy

end OAI
