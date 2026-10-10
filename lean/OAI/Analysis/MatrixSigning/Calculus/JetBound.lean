import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.IteratedNormCompLinear

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open Set

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def JetBound (f : E → F) (x : E) (B : ℝ) : Prop :=
  ∀ n : ℕ, n ≤ 3 → ‖iteratedFDeriv ℝ n f x‖ ≤ B

lemma JetBound.nonneg {f : E → F} {x : E} {B : ℝ} (h : JetBound f x B) : 0 ≤ B :=
  (norm_nonneg _).trans (h 0 (by omega))

lemma JetBound.value {f : E → F} {x : E} {B : ℝ} (h : JetBound f x B) : ‖f x‖ ≤ B := by
  simpa only [norm_iteratedFDeriv_zero] using h 0 (by omega)

lemma JetBound.mono {f : E → F} {x : E} {B C : ℝ} (h : JetBound f x B) (hBC : B ≤ C) :
    JetBound f x C := fun n hn => (h n hn).trans hBC

lemma JetBound.add {f g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => f y+g y) x (B+C) := by
  intro n hn
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast hn)) (hg.of_le (by exact_mod_cast hn))]
  exact (norm_add_le _ _).trans (add_le_add (hB n hn) (hC n hn))

lemma JetBound.neg {f : E → F} {x : E} {B : ℝ} (hB : JetBound f x B) :
    JetBound (fun y => -f y) x B := by
  intro n hn
  change ‖iteratedFDeriv ℝ n (-f) x‖ ≤ B
  rw [iteratedFDeriv_neg_apply,norm_neg]
  exact hB n hn

lemma JetBound.sub {f g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => f y-g y) x (B+C) := by
  simpa only [sub_eq_add_neg] using hB.add hf hg.neg hC.neg

lemma JetBound.linear_comp {f : E → F} {x : E} {B C : ℝ} (L : F →L[ℝ] G)
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hL : ‖L‖ ≤ C) :
    JetBound (L ∘ f) x (C*B) := by
  intro n hn
  exact (iterated_norm_linear_comp L (hf.of_le (by exact_mod_cast hn))).trans
    (mul_le_mul hL (hB n hn) (norm_nonneg _) ((norm_nonneg L).trans hL))

lemma JetBound.comp_linear {f : F → G} {x : E} {B : ℝ} (L : E →L[ℝ] F)
    (hf : ContDiffAt ℝ 3 f (L x)) (hB : JetBound f (L x) B) (hL : ‖L‖ ≤ 1) :
    JetBound (f ∘ L) x B := by
  intro n hn
  exact (iterated_norm_comp_contraction L hL (hf.of_le (by exact_mod_cast hn))).trans (hB n hn)

lemma JetBound.prod {f : E → F} {g : E → G} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => (f y,g y)) x (B+C) := by
  intro n hn
  rw [iteratedFDeriv_prodMk hf hg (by exact_mod_cast hn),ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact (hB n hn).trans (le_add_of_nonneg_right hC.nonneg)
  · exact (hC n hn).trans (le_add_of_nonneg_left hB.nonneg)

lemma JetBound.const (v : F) (x : E) : JetBound (fun _ : E => v) x ‖v‖ := by
  intro n _
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ n => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,norm_nonneg]

lemma JetBound.linear (L : E →L[ℝ] F) (x : E) {B : ℝ} (hLB : ‖L‖ ≤ B) (hx : ‖L x‖ ≤ B) :
    JetBound L x B := by
  intro n hn
  interval_cases n
  · simpa only [norm_iteratedFDeriv_zero] using hx
  · simpa only [norm_iteratedFDeriv_one,L.fderiv] using hLB
  · rw [iterated_norm_linear_ge_two L x 0]
    exact (norm_nonneg L).trans hLB
  · rw [iterated_norm_linear_ge_two L x 1]
    exact (norm_nonneg L).trans hLB

lemma JetBound.sum {ι : Type*} (s : Finset ι) {f : ι → E → F} {x : E} {B : ι → ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 3 (f i) x) (hB : ∀ i ∈ s, JetBound (f i) x (B i)) :
    JetBound (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, B i) := by
  intro n hn
  rw [iteratedFDeriv_fun_sum_apply fun i hi => (hf i hi).of_le (by exact_mod_cast hn)]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hB i hi n hn))

lemma JetBound.bilinear (L : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    {x : E} {B C : ℝ} (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) (hL : ‖L‖ ≤ 1) :
    JetBound (fun y => L (f y) (g y)) x (8*B*C) := by
  have hB0 := hB.value
  have hC0 := hC.value
  have hB1 := hB 1 (by omega)
  have hC1 := hC 1 (by omega)
  have hB2 := hB 2 (by omega)
  have hC2 := hC 2 (by omega)
  have hB3 := hB 3 (by omega)
  have hC3 := hC 3 (by omega)
  have hBn := hB.nonneg
  have hCn := hC.nonneg
  have hBC := mul_nonneg hBn hCn
  intro n hn
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    calc
      _ ≤ ‖L‖*‖f x‖*‖g x‖ := L.le_opNorm₂ _ _
      _ ≤ 1*B*C := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 1 f x‖*‖g x‖ :=
        bilinear_one L (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hL
      _ ≤ B*C+B*C := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
          ‖iteratedFDeriv ℝ 2 f x‖*‖g x‖ := bilinear_two L (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hL
      _ ≤ B*C+2*B*C+B*C := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
          3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 3 f x‖*‖g x‖ :=
        bilinear_three L hf hg hL
      _ ≤ B*C+3*B*C+3*B*C+B*C := by gcongr
      _ = _ := by ring
end
end CurrentKS.Calculus

end OAI
