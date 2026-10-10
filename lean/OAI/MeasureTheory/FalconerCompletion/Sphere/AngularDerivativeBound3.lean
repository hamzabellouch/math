import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.AngularDerivativeBound2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set Metric
open scoped ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fintype ι]

theorem angularDerivativeND_bound (T : V →L[ℝ] V) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : V → ℂ) (A : ℝ) (s : ℕ), ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ j ≤ m+1, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (angularDerivativeND T b) w‖ ≤ D*A^(j+(s+1)) := by
  obtain ⟨M,hM,hMb⟩ := compact_contDiffOn_derivative_bound isOpen_univ
    (isCompact_sphere (0:V) 1) (subset_univ _) T.contDiff.contDiffOn m
  refine ⟨2^m*C*M,by positivity,?_⟩
  intro b A s hb hA hderiv j hj w hw
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hh := norm_iteratedFDeriv_clm_apply (N := ∞) (n := j) (hb.fderiv_right (by simp)) T.contDiff w
    (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ j (angularDerivativeND T b) w‖ ≤ _ at hh
  apply hh.trans
  have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = 2^j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ) * (C*A^(j+(s+1))) * M := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := by simpa using Finset.mem_range.mp hi
      rw [norm_iteratedFDeriv_fderiv]
      gcongr
      · exact (hderiv (i+1) (by omega) w hw).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega)) hC)
      · simpa only [iteratedFDerivWithin_univ] using
          hMb (j-i) (by omega) w (by simpa [mem_sphere,dist_zero_right] using hw)
    _ = 2^j*C*M*A^(j+(s+1)) := by rw [← Finset.sum_mul,← Finset.sum_mul,hsum]; ring
    _ ≤ 2^m*C*M*A^(j+(s+1)) := by gcongr; norm_num

omit [FiniteDimensional ℝ V] in
lemma sphere_derivative_sum_bound {κ : Type*} (u : Finset κ) (b : κ → V → ℂ)
    (hb : ∀ i ∈ u, ContDiff ℝ ∞ (b i)) (D : κ → ℝ) (_hD : ∀ i ∈ u, 0 ≤ D i)
    (A : ℝ) (_hA : 0 ≤ A) (s m : ℕ)
    (hbound : ∀ i ∈ u, ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b i) w‖ ≤ D i*A^(j+s)) :
    ∀ j ≤ m, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (fun w => ∑ i ∈ u, b i w) w‖ ≤ (∑ i ∈ u, D i)*A^(j+s) := by
  intro j hj w hw
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hb i hi).of_le (show (j:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt)]
  exact (norm_sum_le _ _).trans (by rw [Finset.sum_mul]; exact Finset.sum_le_sum fun i hi => hbound i hi j hj w hw)

omit [FiniteDimensional ℝ V] in
lemma sphere_derivative_const_mul_bound (c : ℂ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b)
    {D A : ℝ} {s m : ℕ}
    (hbound : ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ D*A^(j+s)) :
    ∀ j ≤ m, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (fun w => c*b w) w‖ ≤ (‖c‖*D)*A^(j+s) := by
  intro j hj w hw
  change ‖iteratedFDeriv ℝ j (fun w => c • b w) w‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' ((hb.of_le (show (j:ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt),norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbound j hj w hw) (norm_nonneg c)

theorem sphereCasimirND_bound (B : OrthonormalBasis ι ℝ V) (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : V → ℂ) (A : ℝ) (s : ℕ), ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ j ≤ m+2, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^(j+s)) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (sphereCasimirND B b) w‖ ≤ D*A^(j+(s+2)) := by
  classical
  have hd (i j : ι) : ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : V → ℂ) (A : ℝ) (s : ℕ),
      ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ k ≤ m+2, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖ ≤ C*A^(k+s)) →
      ∀ k ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ k (angularDerivativeND (angularGeneratorND (B i) (B j))
          (angularDerivativeND (angularGeneratorND (B i) (B j)) b)) w‖ ≤ D*A^(k+(s+2)) := by
    let T := angularGeneratorND (B i) (B j)
    obtain ⟨D,hD,hDb⟩ := angularDerivativeND_bound T (m+1) C hC
    obtain ⟨F,hF,hFb⟩ := angularDerivativeND_bound T m D hD
    refine ⟨F,hF,?_⟩
    intro b A s hb hA hderiv
    simpa only [Nat.add_assoc] using hFb (angularDerivativeND T b) A (s+1)
      (angularDerivativeND_contDiff T hb) hA (hDb b A s hb hA (by simpa only [Nat.add_assoc] using hderiv))
  choose D hD hDb using hd
  refine ⟨‖(1/2:ℂ)‖ * (∑ i, ∑ j, D i j),mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hD i j),?_⟩
  intro b A s hb hA hderiv
  apply sphere_derivative_const_mul_bound _ (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    angularDerivativeND_contDiff _ (angularDerivativeND_contDiff _ hb))
  apply sphere_derivative_sum_bound _ _ (fun i _ => ContDiff.sum fun j _ =>
    angularDerivativeND_contDiff _ (angularDerivativeND_contDiff _ hb)) (fun i => ∑ j, D i j)
    (fun i _ => Finset.sum_nonneg fun j _ => hD i j) A (by linarith) (s+2) m
  intro i _
  exact sphere_derivative_sum_bound _ _ (fun j _ => angularDerivativeND_contDiff _
      (angularDerivativeND_contDiff _ hb)) (D i) (fun j _ => hD i j) A (by linarith) (s+2) m
      (fun j _ => hDb i j b A s hb hA hderiv)

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
