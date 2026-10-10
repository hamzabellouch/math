import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! # Logarithmic bounds for the actual radial ODE coefficient recurrence

Differentiation in logarithmic radius preserves an exponential order. This
small calculus is used for the finite recurrence of high radial derivatives.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

structure HasLogJetBound (σ : ℝ) (f : ℝ → A) : Prop where
  smooth : ∃ L : ℝ, ContDiffOn ℝ ∞ f (Ioi L)
  bound : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in atTop,
    ‖iteratedDeriv k f t‖ ≤ C * Real.exp (σ * t)

namespace HasLogJetBound

variable {σ τ : ℝ} {f g : ℝ → A}

theorem mono (hf : HasLogJetBound σ f) (hστ : σ ≤ τ) : HasLogJetBound τ f := by
  refine ⟨hf.smooth, ?_⟩
  intro k
  obtain ⟨C, hC, hb⟩ := hf.bound k
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hστ ht0)) hC)

theorem const (c : A) : HasLogJetBound 0 (fun _ : ℝ => c) := by
  refine ⟨⟨0, contDiffOn_const⟩, ?_⟩
  intro k
  refine ⟨‖c‖, norm_nonneg _, Filter.Eventually.of_forall ?_⟩
  intro t
  by_cases hk : k = 0
  · subst k
    simp
  · simp [iteratedDeriv_const, hk]

theorem zero (σ : ℝ) : HasLogJetBound σ (fun _ : ℝ => (0 : A)) := by
  refine ⟨⟨0, contDiffOn_const⟩, ?_⟩
  intro k
  exact ⟨0, le_rfl, Filter.Eventually.of_forall (fun t => by simp)⟩

theorem exponential (σ : ℝ) (c : A) :
    HasLogJetBound σ (fun t : ℝ => Real.exp (σ * t) • c) := by
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (σ * t) • c) :=
    (contDiff_const.mul contDiff_id).exp.smul contDiff_const
  have hd (k : ℕ) : iteratedDeriv k (fun t : ℝ => Real.exp (σ * t) • c) =
      fun t => σ ^ k • (Real.exp (σ * t) • c) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        have hh := ((((hasDerivAt_id t).const_mul σ).exp).smul_const c).const_smul (σ ^ k)
        change HasDerivAt (fun s : ℝ => σ ^ k • (Real.exp (σ * s) • c)) _ t at hh
        rw [hh.deriv]
        simp only [id_eq, mul_one, smul_smul, pow_succ]
        congr 1
        ring
  refine ⟨⟨0, hs.contDiffOn⟩, ?_⟩
  intro k
  refine ⟨‖σ‖ ^ k * ‖c‖, mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _),
    Filter.Eventually.of_forall ?_⟩
  intro t
  rw [hd]
  simp only [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact le_of_eq (by ring)

theorem neg (hf : HasLogJetBound σ f) : HasLogJetBound σ (fun t => -f t) := by
  obtain ⟨L, hL⟩ := hf.smooth
  refine ⟨⟨L, hL.neg⟩, ?_⟩
  intro k
  obtain ⟨C, hC, hb⟩ := hf.bound k
  exact ⟨C, hC, by simpa only [iteratedDeriv_fun_neg, norm_neg] using hb⟩

theorem add (hf : HasLogJetBound σ f) (hg : HasLogJetBound σ g) :
    HasLogJetBound σ (fun t => f t + g t) := by
  obtain ⟨L, hL⟩ := hf.smooth
  obtain ⟨M, hM⟩ := hg.smooth
  have hLf : ContDiffOn ℝ ∞ f (Ioi (max L M)) :=
    hL.mono (Ioi_subset_Ioi (le_max_left _ _))
  have hMg : ContDiffOn ℝ ∞ g (Ioi (max L M)) :=
    hM.mono (Ioi_subset_Ioi (le_max_right _ _))
  refine ⟨⟨max L M, hLf.add hMg⟩, ?_⟩
  intro k
  obtain ⟨C, hC, hb⟩ := hf.bound k
  obtain ⟨D, hD, hd⟩ := hg.bound k
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [hb, hd, eventually_gt_atTop (max L M)] with t ht hu htm
  rw [iteratedDeriv_fun_add
    (((hLf t htm).contDiffAt (Ioi_mem_nhds htm)).of_le (by simp))
    (((hMg t htm).contDiffAt (Ioi_mem_nhds htm)).of_le (by simp))]
  exact (norm_add_le _ _).trans ((add_le_add ht hu).trans_eq (by ring))

theorem sub (hf : HasLogJetBound σ f) (hg : HasLogJetBound σ g) :
    HasLogJetBound σ (fun t => f t - g t) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem deriv (hf : HasLogJetBound σ f) : HasLogJetBound σ (deriv f) := by
  obtain ⟨L, hL⟩ := hf.smooth
  refine ⟨⟨L, hL.deriv_of_isOpen isOpen_Ioi (by simp)⟩, ?_⟩
  intro k
  simpa only [← iteratedDeriv_succ'] using hf.bound (k + 1)

theorem smul (hf : HasLogJetBound σ f) (c : ℝ) :
    HasLogJetBound σ (fun t => c • f t) := by
  obtain ⟨L, hL⟩ := hf.smooth
  refine ⟨⟨L, hL.const_smul c⟩, ?_⟩
  intro k
  obtain ⟨C, hC, hb⟩ := hf.bound k
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hb] with t ht
  simpa only [iteratedDeriv_fun_const_smul_field, norm_smul, mul_assoc] using
    mul_le_mul_of_nonneg_left ht (norm_nonneg c)

end HasLogJetBound

namespace HasLogJetBound

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
variable {σ τ : ℝ} {f g : ℝ → R}

theorem mul (hf : HasLogJetBound σ f) (hg : HasLogJetBound τ g) :
    HasLogJetBound (σ + τ) (fun t => f t * g t) := by
  obtain ⟨L, hL⟩ := hf.smooth
  obtain ⟨M, hM⟩ := hg.smooth
  have hLf : ContDiffOn ℝ ∞ f (Ioi (max L M)) :=
    hL.mono (Ioi_subset_Ioi (le_max_left _ _))
  have hMg : ContDiffOn ℝ ∞ g (Ioi (max L M)) :=
    hM.mono (Ioi_subset_Ioi (le_max_right _ _))
  refine ⟨⟨max L M, hLf.mul hMg⟩, ?_⟩
  intro k
  choose C hC hb using hf.bound
  choose D hD hd using hg.bound
  let K := ∑ i ∈ Finset.range (k + 1), ‖(k.choose i : R)‖ * C i * D (k - i)
  refine ⟨K, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (hC i)) (hD _)), ?_⟩
  have hfb : ∀ᶠ t in atTop, ∀ i ∈ Finset.range (k + 1),
      ‖iteratedDeriv i f t‖ ≤ C i * Real.exp (σ * t) :=
    (eventually_all_finset _).mpr (fun i _ => hb i)
  have hgb : ∀ᶠ t in atTop, ∀ i ∈ Finset.range (k + 1),
      ‖iteratedDeriv (k - i) g t‖ ≤ D (k - i) * Real.exp (τ * t) :=
    (eventually_all_finset _).mpr (fun i _ => hd (k - i))
  filter_upwards [hfb, hgb, eventually_gt_atTop (max L M)] with t ht hu htm
  rw [iteratedDeriv_fun_mul
    (((hLf t htm).contDiffAt (Ioi_mem_nhds htm)).of_le (by simp))
    (((hMg t htm).contDiffAt (Ioi_mem_nhds htm)).of_le (by simp))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        (‖(k.choose i : R)‖ * C i * D (k - i)) * Real.exp ((σ + τ) * t) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul (ht i hi) (hu i hi) (norm_nonneg _)
        (mul_nonneg (hC _) (Real.exp_pos _).le)
      have hh := mul_le_mul_of_nonneg_left h (norm_nonneg (k.choose i : R))
      apply ((norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))).trans
      convert hh using 1
      · ring
      · rw [add_mul, Real.exp_add]
        ring
    _ = K * Real.exp ((σ + τ) * t) := by rw [← Finset.sum_mul]

end HasLogJetBound

end DefocusingNLS

end OAI
