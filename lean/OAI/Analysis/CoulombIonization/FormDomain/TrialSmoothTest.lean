import Mathlib
import OAI.Analysis.CoulombIonization.Model
import OAI.Analysis.CoulombIonization.FormDomain.WeakDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section TrialSmoothTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma integrable_norm_sq_div_of_support {f : E → ℂ}
    (hf : Continuous f) (hcf : HasCompactSupport f) {k : E → ℝ}
    (hk : Measurable k) (hkn : ∀ x, 0 ≤ k x) {ε : ℝ} (hε : 0 < ε)
    (hb : ∀ x, f x ≠ 0 → ε ≤ k x) : Integrable (fun x => ‖f x‖ ^ 2 / k x) := by
  have hsq : Integrable (fun x => ‖f x‖ ^ 2) :=
    (hf.norm.pow 2).integrable_of_hasCompactSupport (compact_norm_sq hcf)
  apply (hsq.div_const ε).mono' ((hf.norm.measurable.pow_const 2).div hk).aestronglyMeasurable
  filter_upwards [] with x
  change |‖f x‖ ^ 2 / k x| ≤ ‖f x‖ ^ 2 / ε
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (hkn x))]
  by_cases hx : f x = 0
  · simp [hx]
  · exact div_le_div_of_nonneg_left (sq_nonneg _) hε (hb x hx)
end TrialSmoothTest

def smoothForm {N : ℕ} (f : Configuration N → ℂ) : FormVector N where
  value := fun _ => f
  gradient := fun _ i a x => fderiv ℝ f x (direction i a)

theorem smoothForm_admissible {N : ℕ} {f : Configuration N → ℂ}
    (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (ha : ∀ (π : Equiv.Perm (Fin N)) x,
      f (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * f x))
    (hn : (Fintype.card (Spins N) : ℝ) * (∫ x, ‖f x‖ ^ 2) = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hnuc : ∀ x, f x ≠ 0 → ∀ i, ε ≤ ‖x i‖)
    (hpair : ∀ x, f x ≠ 0 → ∀ i j, i ≠ j → ε ≤ ‖x i - x j‖) :
    FormAdmissible (smoothForm f) := by
  refine ⟨fun _ => hf.continuous.memLp_of_hasCompactSupport hcf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a
    exact (smooth_derivative_continuous hf _).memLp_of_hasCompactSupport (compact_derivative hcf _)
  · intro s i a φ hφ hcφ
    exact smooth_weak_gradient hf hcf hφ hcφ _
  · intro π s
    exact Eventually.of_forall (ha π)
  · simpa only [smoothForm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hn
  · intro s i
    exact integrable_norm_sq_div_of_support hf.continuous hcf
      (continuous_apply i).norm.measurable (fun _ => norm_nonneg _) hε (fun x hx => hnuc x hx i)
  · intro s i j hij
    exact integrable_norm_sq_div_of_support hf.continuous hcf
      ((continuous_apply i).sub (continuous_apply j)).norm.measurable
      (fun _ => norm_nonneg _) hε (fun x hx => hpair x hx i j hij)

def antisymmetrize {N : ℕ} (g : Configuration N → ℂ) (x : Configuration N) : ℂ :=
  ∑ π : Equiv.Perm (Fin N), (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π))

lemma complex_sign_sq {N : ℕ} (π : Equiv.Perm (Fin N)) :
    (((Equiv.Perm.sign π : ℤ) : ℂ)) ^ 2 = 1 := by
  have h : (Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ) = 1 :=
    congrArg (fun u : ℤˣ => (u : ℤ)) (Int.units_mul_self (Equiv.Perm.sign π))
  have hc : (((Equiv.Perm.sign π : ℤ) : ℂ)) * (((Equiv.Perm.sign π : ℤ) : ℂ)) = 1 := by
    exact_mod_cast h
  simpa only [pow_two] using hc

lemma antisymmetrize_perm {N : ℕ} (g : Configuration N → ℂ)
    (σ : Equiv.Perm (Fin N)) (x : Configuration N) :
    antisymmetrize g (x ∘ σ) =
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * antisymmetrize g x) := by
  classical
  unfold antisymmetrize
  calc
    _ = (((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ π : Equiv.Perm (Fin N),
          (((Equiv.Perm.sign (σ * π) : ℤ) : ℂ) * g (x ∘ (σ * π : Equiv.Perm (Fin N))))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro π _
      have heq : (x ∘ σ) ∘ π = x ∘ (σ * π : Equiv.Perm (Fin N)) := rfl
      rw [heq, Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]
      have hs := complex_sign_sq σ
      linear_combination -(Equiv.Perm.sign π : ℤ) * g (x ∘ (σ * π : Equiv.Perm (Fin N))) * hs
    _ = _ := by
      congr 1
      simpa only [Equiv.coe_mulLeft] using
        Equiv.sum_comp (Equiv.mulLeft σ)
          (fun π : Equiv.Perm (Fin N) => (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π)))

lemma antisymmetrize_smooth {N : ℕ} {g : Configuration N → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (antisymmetrize g) := by
  classical
  apply ContDiff.sum
  intro π _
  apply contDiff_const.mul
  exact hg.comp (contDiff_pi.mpr (fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Space) (π i)).contDiff))

def permuteConfig {N : ℕ} (π : Equiv.Perm (Fin N)) :
    Configuration N ≃ₜ Configuration N where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  continuous_toFun := continuous_pi (fun i => continuous_apply (π i))
  continuous_invFun := continuous_pi (fun i => continuous_apply (π.symm i))

lemma antisymmetrize_compact {N : ℕ} {g : Configuration N → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (antisymmetrize g) := by
  classical
  have h (π : Equiv.Perm (Fin N)) : HasCompactSupport
      (fun x => (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π))) :=
    (hg.comp_homeomorph (permuteConfig π)).mul_left
  have hs := HasCompactSupport.finset_sum (s := Finset.univ) (fun π _ => h π)
  have heq : (∑ π : Equiv.Perm (Fin N),
      fun x => (((Equiv.Perm.sign π : ℤ) : ℂ) * g (x ∘ π))) = antisymmetrize g := by
    ext x
    simp only [Finset.sum_apply, antisymmetrize]
  exact heq ▸ hs

def trialCenter (N : ℕ) : Configuration N :=
  fun i => EuclideanSpace.single 0 (4 * ((i.val : ℝ) + 1))

lemma trialCenter_norm {N : ℕ} (i : Fin N) : 4 ≤ ‖trialCenter N i‖ := by
  rw [trialCenter, PiLp.norm_single 2 (fun _ : Fin 3 => ℝ), Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  have hi : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
  linarith

lemma trialCenter_separated {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    4 ≤ ‖trialCenter N i - trialCenter N j‖ := by
  change 4 ≤ ‖PiLp.single (β := fun _ : Fin 3 => ℝ) 2 (0 : Fin 3) (4 * ((i.val : ℝ) + 1)) -
    PiLp.single (β := fun _ : Fin 3 => ℝ) 2 (0 : Fin 3) (4 * ((j.val : ℝ) + 1))‖
  rw [← PiLp.single_sub, PiLp.norm_single 2 (fun _ : Fin 3 => ℝ), Real.norm_eq_abs]
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hd : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

def trialBump (N : ℕ) : ContDiffBump (trialCenter N) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def trialSeed (N : ℕ) (x : Configuration N) : ℂ := ((trialBump N x : ℝ) : ℂ)

lemma trialSeed_smooth (N : ℕ) : ContDiff ℝ ∞ (trialSeed N) :=
  Complex.ofRealCLM.contDiff.comp (trialBump N).contDiff

lemma trialSeed_compact (N : ℕ) : HasCompactSupport (trialSeed N) :=
  (trialBump N).hasCompactSupport.comp_left (g := Complex.ofReal) (by rfl)

lemma trialSeed_support {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0) :
    ‖x - trialCenter N‖ < 1 := by
  have hn : trialBump N x ≠ 0 := by simpa only [trialSeed, ne_eq, Complex.ofReal_eq_zero] using hx
  have hm : x ∈ Function.support (trialBump N) := hn
  rw [(trialBump N).support_eq] at hm
  exact hm

lemma trialSeed_dist {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0) (i : Fin N) :
    ‖x i - trialCenter N i‖ < 1 :=
  (norm_le_pi_norm (x - trialCenter N) i).trans_lt (trialSeed_support hx)

lemma trialSeed_nucleus {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0) (i : Fin N) :
    1 ≤ ‖x i‖ := by
  have hd := trialSeed_dist hx i
  have hc := trialCenter_norm i
  have ht := norm_sub_norm_le (trialCenter N i) (x i)
  rw [norm_sub_rev] at ht
  linarith

lemma trialSeed_pair {N : ℕ} {x : Configuration N} (hx : trialSeed N x ≠ 0)
    (i j : Fin N) (hij : i ≠ j) : 1 ≤ ‖x i - x j‖ := by
  have hd := trialSeed_dist hx i
  have he := trialSeed_dist hx j
  have hc := trialCenter_separated i j hij
  have ht : ‖trialCenter N i - trialCenter N j‖ ≤
      ‖x i - trialCenter N i‖ + ‖x i - x j‖ + ‖x j - trialCenter N j‖ := by
    calc
      _ = ‖(trialCenter N i - x i) + (x i - x j) + (x j - trialCenter N j)‖ := by
        congr 1; abel
      _ ≤ ‖trialCenter N i - x i‖ + ‖x i - x j‖ + ‖x j - trialCenter N j‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by rw [norm_sub_rev (trialCenter N i)]
  linarith

lemma trialSeed_center (N : ℕ) : trialSeed N (trialCenter N) = 1 := by
  have h : trialBump N (trialCenter N) = 1 :=
    (trialBump N).one_of_mem_closedBall (by simp [trialBump])
  simp only [trialSeed, h, Complex.ofReal_one]

lemma trialSeed_center_permuted {N : ℕ} {π : Equiv.Perm (Fin N)} (hπ : π ≠ 1) :
    trialSeed N (trialCenter N ∘ π) = 0 := by
  by_contra hn
  have hi : ∃ i, π i ≠ i := by
    by_contra hh
    push Not at hh
    exact hπ (Equiv.ext hh)
  obtain ⟨i, hi⟩ := hi
  have hd := trialSeed_dist hn i
  have hc := trialCenter_separated (π i) i hi
  change ‖trialCenter N (π i) - trialCenter N i‖ < 1 at hd
  linarith

lemma antisymmetrize_trialSeed_nonzero (N : ℕ) :
    antisymmetrize (trialSeed N) (trialCenter N) = 1 := by
  classical
  unfold antisymmetrize
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin N))]
  · simpa using trialSeed_center N
  · intro π _ hπ
    rw [trialSeed_center_permuted hπ, mul_zero]
  · simp

lemma antisymmetrize_has_nonzero_term {N : ℕ} {g : Configuration N → ℂ}
    {x : Configuration N} (hx : antisymmetrize g x ≠ 0) :
    ∃ π : Equiv.Perm (Fin N), g (x ∘ π) ≠ 0 := by
  classical
  obtain ⟨π, _, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact ⟨π, (mul_ne_zero_iff.mp hπ).2⟩

lemma antisymmetrize_trialSeed_nucleus {N : ℕ} {x : Configuration N}
    (hx : antisymmetrize (trialSeed N) x ≠ 0) (i : Fin N) : 1 ≤ ‖x i‖ := by
  obtain ⟨π, hπ⟩ := antisymmetrize_has_nonzero_term hx
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using trialSeed_nucleus hπ (π.symm i)

lemma antisymmetrize_trialSeed_pair {N : ℕ} {x : Configuration N}
    (hx : antisymmetrize (trialSeed N) x ≠ 0) (i j : Fin N) (hij : i ≠ j) : 1 ≤ ‖x i - x j‖ := by
  obtain ⟨π, hπ⟩ := antisymmetrize_has_nonzero_term hx
  have hn : π.symm i ≠ π.symm j := fun h => hij (π.symm.injective h)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    trialSeed_pair hπ (π.symm i) (π.symm j) hn

lemma norm_real_mul_sq (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem exists_normalized_smoothForm {N : ℕ} {g : Configuration N → ℂ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (ha : ∀ (π : Equiv.Perm (Fin N)) x,
      g (x ∘ π) = (((Equiv.Perm.sign π : ℤ) : ℂ) * g x))
    {x₀ : Configuration N} (hx : g x₀ ≠ 0)
    {ε : ℝ} (hε : 0 < ε)
    (hnuc : ∀ x, g x ≠ 0 → ∀ i, ε ≤ ‖x i‖)
    (hpair : ∀ x, g x ≠ 0 → ∀ i j, i ≠ j → ε ≤ ‖x i - x j‖) :
    ∃ ψ : FormVector N, FormAdmissible ψ := by
  classical
  let n : ℝ := Fintype.card (Spins N)
  let I : ℝ := ∫ x, ‖g x‖ ^ 2
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hI : 0 < I :=
    (hg.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (compact_norm_sq hcg) (fun x => sq_nonneg _) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have hnI : 0 < n * I := mul_pos hn hI
  let r : ℝ := (Real.sqrt (n * I))⁻¹
  have hr : r ^ 2 * (n * I) = 1 := by
    dsimp only [r]
    rw [inv_pow, Real.sq_sqrt hnI.le, inv_mul_cancel₀ hnI.ne']
  let f : Configuration N → ℂ := fun x => (r : ℂ) * g x
  refine ⟨smoothForm f, smoothForm_admissible (contDiff_const.mul hg) hcg.mul_left ?_ ?_ hε ?_ ?_⟩
  · intro π x
    dsimp only [f]
    rw [ha π x]
    ring
  · change n * (∫ x, ‖(r : ℂ) * g x‖ ^ 2) = 1
    simp_rw [norm_real_mul_sq]
    rw [integral_const_mul]
    change n * (r ^ 2 * I) = 1
    linarith only [hr]
  · intro x hf i
    exact hnuc x (fun h => hf (by simp only [f, h, mul_zero])) i
  · intro x hf i j hij
    exact hpair x (fun h => hf (by simp only [f, h, mul_zero])) i j hij

theorem formDomain_nonempty (N : ℕ) : ∃ ψ : FormVector N, FormAdmissible ψ := by
  apply exists_normalized_smoothForm
    (antisymmetrize_smooth (trialSeed_smooth N))
    (antisymmetrize_compact (trialSeed_compact N))
    (antisymmetrize_perm (trialSeed N))
    (x₀ := trialCenter N)
    (by rw [antisymmetrize_trialSeed_nonzero]; norm_num)
    (ε := 1) (by norm_num)
  · exact fun _ hx i => antisymmetrize_trialSeed_nucleus hx i
  · exact fun _ hx i j hij => antisymmetrize_trialSeed_pair hx i j hij

lemma formValues_nonempty (Z : ℝ) (N : ℕ) :
    Set.Nonempty {e | ∃ ψ : FormVector N, FormAdmissible ψ ∧ formEnergy Z ψ = e} := by
  obtain ⟨ψ, hψ⟩ := formDomain_nonempty N
  exact ⟨formEnergy Z ψ, ψ, hψ, rfl⟩

end CoulombAtom

end

end OAI
