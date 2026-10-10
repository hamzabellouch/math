import Mathlib
import OAI.Analysis.MatrixSigning.Calculus.BilinearIteratedBound

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Calculus

section
open Set
open scoped Topology

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma iterated_norm_comp_linear (L : E →L[ℝ] F) {f : F → G} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f (L x)) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖*‖L‖^n := by
  obtain ⟨u,hu,hxu,hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  have hfu : ContDiffOn ℝ n f u := by simpa using hfu
  have hpre : IsOpen (L ⁻¹' u) := hu.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfu hu.uniqueDiffOn hpre.uniqueDiffOn hxu (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn (hf.comp x L.contDiff.contDiffAt) hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn hf hxu] at he
  rw [he]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

lemma iterated_norm_comp_contraction (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {f : F → G} {x : E} {n : ℕ} (hf : ContDiffAt ℝ n f (L x)) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  apply (iterated_norm_comp_linear L hf).trans
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

lemma iterated_norm_linear_ge_two (L : E →L[ℝ] F) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n+2) L x‖=0 := by
  rw [show n+2=(n+1)+1 by omega, ← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ => L := by funext y; exact L.fderiv
  rw [he,iteratedFDeriv_succ_const]
  simp

lemma bilinear_one (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 1 f x‖*‖g x‖ := by
  have h := bilinear_iterated_bound B hf hg hB
  simp only [Finset.sum_range_succ,Finset.sum_range_one,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,one_mul] at h
  change ‖iteratedFDeriv ℝ 1 (fun y => B (f y) (g y)) x‖ ≤
    ‖iteratedFDeriv ℝ 0 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
    ‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at h
  simpa only [norm_iteratedFDeriv_zero] using h

lemma bilinear_two (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 2 (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 2 f x‖*‖g x‖ := by
  have h := bilinear_iterated_bound B hf hg hB
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add] at h
  change ‖iteratedFDeriv ℝ 2 (fun y => B (f y) (g y)) x‖ ≤
    ‖iteratedFDeriv ℝ 0 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
    2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
    ‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at h
  simpa only [norm_iteratedFDeriv_zero] using h

lemma bilinear_three (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 3 (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 3 f x‖*‖g x‖ := by
  have h := bilinear_iterated_bound B hf hg hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_one,Finset.sum_range_zero,Nat.choose,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add] at h
  change ‖iteratedFDeriv ℝ 3 (fun y => B (f y) (g y)) x‖ ≤
    ‖iteratedFDeriv ℝ 0 f x‖*‖iteratedFDeriv ℝ 3 g x‖+
    3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
    3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
    ‖iteratedFDeriv ℝ 3 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at h
  simpa only [norm_iteratedFDeriv_zero] using h

end

open Set

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

lemma iterated_norm_linear_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : E → F} {x : E}
    {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n (L ∘ f) x‖ ≤ ‖L‖*‖iteratedFDeriv ℝ n f x‖ := by
  rw [L.iteratedFDeriv_comp_left hf le_rfl]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

lemma inverse_linear_first_three (X : E →L[ℝ] R) (hX : ‖X‖ ≤ 1) {z : E}
    (hz : IsUnit (X z)) {a : ℝ} (ha : ‖Ring.inverse (X z)‖ ≤ a) :
    ‖iteratedFDeriv ℝ 1 (fun v => Ring.inverse (X v)) z‖ ≤ a^2 ∧
    ‖iteratedFDeriv ℝ 2 (fun v => Ring.inverse (X v)) z‖ ≤ 2*a^3 ∧
    ‖iteratedFDeriv ℝ 3 (fun v => Ring.inverse (X v)) z‖ ≤ 6*a^4 := by
  have h₀ : 0 ≤ a := (norm_nonneg _).trans ha
  have h := inverse_first_three hz
  have hc (n : ℕ) := iterated_norm_comp_contraction X hX
    (contDiffAt_inverse_of_unit (n := n) hz)
  refine ⟨(hc 1).trans ?_,(hc 2).trans ?_,(hc 3).trans ?_⟩
  · rw [norm_iteratedFDeriv_one]
    exact h.1.trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
  · exact h.2.1.trans (by gcongr)
  · exact h.2.2.trans (by gcongr)

theorem inverse_sandwich_first_three (X P : E →L[ℝ] R)
    (hX : ‖X‖ ≤ 1) (hP : ‖P‖ ≤ 1) {z : E} (hz : IsUnit (X z))
    {a : ℝ} (ha₁ : 1 ≤ a) (ha : ‖Ring.inverse (X z)‖ ≤ a) (hp : ‖P z‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) z‖ ≤ 3*a^3 ∧
    ‖iteratedFDeriv ℝ 2 (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) z‖ ≤ 10*a^4 ∧
    ‖iteratedFDeriv ℝ 3 (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) z‖ ≤ 42*a^5 := by
  let f : E → R := fun v => Ring.inverse (X v)
  let g : E → R := fun v => P v*f v
  have hf (n : ℕ) : ContDiffAt ℝ n f z :=
    (contDiffAt_inverse_of_unit hz).comp z X.contDiff.contDiffAt
  have hg (n : ℕ) : ContDiffAt ℝ n g z := P.contDiff.contDiffAt.mul (hf n)
  have hB : ‖ContinuousLinearMap.mul ℝ R‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ R
  have h₀ : 0 ≤ a := by linarith
  have ha₂ : a ≤ a^2 := by nlinarith
  have ha₃ : a^2 ≤ a^3 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr ha₂)]
  have ha₄ : a^3 ≤ a^4 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr ha₃)]
  obtain ⟨hi₁,hi₂,hi₃⟩ := inverse_linear_first_three X hX hz ha
  have hp₁ : ‖iteratedFDeriv ℝ 1 P z‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_one,P.fderiv] using hP
  have hp₂ : ‖iteratedFDeriv ℝ 2 P z‖=0 := iterated_norm_linear_ge_two P z 0
  have hp₃ : ‖iteratedFDeriv ℝ 3 P z‖=0 := iterated_norm_linear_ge_two P z 1
  have hg₀ : ‖g z‖ ≤ a := (norm_mul_le _ _).trans (by simpa using mul_le_mul hp ha (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
  have hg₁ : ‖iteratedFDeriv ℝ 1 g z‖ ≤ 2*a^2 := by
    calc
      _ ≤ ‖P z‖*‖iteratedFDeriv ℝ 1 f z‖+‖iteratedFDeriv ℝ 1 P z‖*‖f z‖ :=
        bilinear_one (ContinuousLinearMap.mul ℝ R) P.contDiff.contDiffAt (hf 1) hB
      _ ≤ 1*a^2+1*a := by gcongr
      _ ≤ _ := by nlinarith
  have hg₂ : ‖iteratedFDeriv ℝ 2 g z‖ ≤ 4*a^3 := by
    have h := bilinear_two (ContinuousLinearMap.mul ℝ R) P.contDiff.contDiffAt (hf 2) hB
    rw [hp₂,zero_mul,add_zero] at h
    calc
      _ ≤ ‖P z‖*‖iteratedFDeriv ℝ 2 f z‖+2*‖iteratedFDeriv ℝ 1 P z‖*‖iteratedFDeriv ℝ 1 f z‖ := h
      _ ≤ 1*(2*a^3)+2*1*a^2 := by gcongr
      _ ≤ _ := by nlinarith
  have hg₃ : ‖iteratedFDeriv ℝ 3 g z‖ ≤ 12*a^4 := by
    have h := bilinear_three (ContinuousLinearMap.mul ℝ R) P.contDiff.contDiffAt (hf 3) hB
    rw [hp₂,hp₃,mul_zero,zero_mul,zero_mul,add_zero,add_zero] at h
    calc
      _ ≤ ‖P z‖*‖iteratedFDeriv ℝ 3 f z‖+3*‖iteratedFDeriv ℝ 1 P z‖*‖iteratedFDeriv ℝ 2 f z‖ := h
      _ ≤ 1*(6*a^4)+3*1*(2*a^3) := by gcongr
      _ ≤ _ := by nlinarith
  have he : (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) =
      (fun v => f v*g v) := by funext v; exact mul_assoc _ _ _
  rw [he]
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ ‖f z‖*‖iteratedFDeriv ℝ 1 g z‖+‖iteratedFDeriv ℝ 1 f z‖*‖g z‖ :=
        bilinear_one (ContinuousLinearMap.mul ℝ R) (hf 1) (hg 1) hB
      _ ≤ a*(2*a^2)+a^2*a := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ‖f z‖*‖iteratedFDeriv ℝ 2 g z‖+2*‖iteratedFDeriv ℝ 1 f z‖*‖iteratedFDeriv ℝ 1 g z‖+
          ‖iteratedFDeriv ℝ 2 f z‖*‖g z‖ := bilinear_two (ContinuousLinearMap.mul ℝ R) (hf 2) (hg 2) hB
      _ ≤ a*(4*a^3)+2*a^2*(2*a^2)+(2*a^3)*a := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ‖f z‖*‖iteratedFDeriv ℝ 3 g z‖+3*‖iteratedFDeriv ℝ 1 f z‖*‖iteratedFDeriv ℝ 2 g z‖+
          3*‖iteratedFDeriv ℝ 2 f z‖*‖iteratedFDeriv ℝ 1 g z‖+
          ‖iteratedFDeriv ℝ 3 f z‖*‖g z‖ := bilinear_three (ContinuousLinearMap.mul ℝ R) (hf 3) (hg 3) hB
      _ ≤ a*(12*a^4)+3*a^2*(4*a^3)+3*(2*a^3)*(2*a^2)+(6*a^4)*a := by gcongr
      _ = _ := by ring
end CurrentKS.Calculus

end

end OAI
