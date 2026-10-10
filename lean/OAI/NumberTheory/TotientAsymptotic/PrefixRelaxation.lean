import OAI.NumberTheory.TotientAsymptotic.WitnessPrefix
import OAI.NumberTheory.TotientAsymptotic.SimplexShell

namespace OAI

/-! Quantitative control of simultaneous perturbations of all prefix inequalities. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma prefixRegion_subset_relaxation {N : ℕ} (B C₀ : ℝ) (C δ : Fin N → ℝ)
    {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ : ∀ i, 0 ≤ δ i) :
    prefixRegion N B C₀ C ⊆ prefixRegion N (B+δ₀) C₀ (C-δ) := by
  intro u hu
  exact ⟨fun i => (sub_le_self _ (hδ i)).trans (hu.1 i), by have := hu.2; linarith⟩

/-- Relaxing several inequalities at once costs their sum with the exact
renewal weights. This avoids multiplying an error by the dimension. -/
theorem prefix_relaxation_volume_bound {N : ℕ} (hN : 0 < N)
    (B C₀ : ℝ) (C δ : Fin N → ℝ) {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hδ : ∀ i, 0 ≤ δ i)
    (hT : 0 ≤ B-C₀-∑ i, g (i.val+1)*C i) :
    (volume (prefixRegion N (B+δ₀) C₀ (C-δ) \ prefixRegion N B C₀ C)).toReal ≤
      ((δ₀+∑ i, g (i.val+1)*δ i)*N*
        (B+δ₀-C₀-∑ i, g (i.val+1)*(C-δ) i)^(N-1)) /
        ((N.factorial : ℝ)*∏ i : Fin N, g (i.val+1)) := by
  let T := B-C₀-∑ i, g (i.val+1)*C i
  let w := δ₀+∑ i, g (i.val+1)*δ i
  have hw : 0 ≤ w := add_nonneg hδ₀ (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (g_pos _).le (hδ i)))
  have he : B+δ₀-C₀-∑ i, g (i.val+1)*(C-δ) i = T+w := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, T, w]
    ring
  have hden : 0 < (N.factorial : ℝ)*∏ i : Fin N, g (i.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun i _ => g_pos _))
  have hf : volume (prefixRegion N (B+δ₀) C₀ (C-δ)) ≠ ⊤ := by
    rw [volume_prefixRegion_explicit _ hN]
    exact ENNReal.ofReal_ne_top
  change volume.real _ ≤ _
  rw [measureReal_sdiff (prefixRegion_subset_relaxation B C₀ C δ hδ₀ hδ)
    (measurableSet_prefixRegion _ _ _ _) hf]
  change (volume (prefixRegion N (B+δ₀) C₀ (C-δ))).toReal-
    (volume (prefixRegion N B C₀ C)).toReal ≤ _
  rw [volume_prefixRegion_explicit _ hN, volume_prefixRegion_explicit _ hN,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), he]
  change (max (T+w) 0)^N / _ - (max T 0)^N / _ ≤ _
  rw [max_eq_left (add_nonneg hT hw), max_eq_left hT, ← sub_div]
  apply (div_le_div_iff_of_pos_right hden).mpr
  have hh := pow_sub_positivePart_le (add_nonneg hT hw) hw N
  simpa only [add_sub_cancel_right, max_eq_left hT] using hh

def prefixBandRegion (x : ℝ) (H : ℕ) : Set (Fin (R x H) → ℝ) :=
  {u | ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ u i ∧
    u i ≤ (11/10 : ℝ)*bandScale x (i.val+1)}

def prefixPerturbation (x : ℝ) (H : ℕ) : Fin (R x H) → ℝ :=
  fun i => (xi x (i.val+1)-1)*((11/10 : ℝ)*bandScale x (i.val+1))

def topPerturbation (x : ℝ) : ℝ := (xi x 0-1)*B x

lemma xi_sub_one_pos (x : ℝ) (i : ℕ) : 0 < xi x i-1 := by
  dsimp [xi]
  have := Real.exp_pos (-((m x-i : ℕ) : ℝ)/40)
  linarith

lemma bandScale_nonneg (x : ℝ) (i : ℕ) : 0 ≤ bandScale x i := by
  unfold bandScale
  exact mul_nonneg (mul_nonneg (alpha_pos _).le (Nat.cast_nonneg _))
    (inv_nonneg.mpr (pow_nonneg rho_pos.le _))

lemma prefixPerturbation_nonneg (x : ℝ) (H : ℕ) (i : Fin (R x H)) :
    0 ≤ prefixPerturbation x H i := by
  exact mul_nonneg (xi_sub_one_pos _ _).le
    (mul_nonneg (by norm_num) (bandScale_nonneg _ _))

lemma topPerturbation_nonneg {x : ℝ} (hB : 0 ≤ B x) : 0 ≤ topPerturbation x :=
  mul_nonneg (xi_sub_one_pos _ _).le hB

lemma banded_tailRegion_subset_perturbed {x : ℝ} {H : ℕ} (η : TailDatum H)
    (hB : 0 ≤ B x) :
    tailPrefixRegion x H η ∩ prefixBandRegion x H ⊆ perturbedTailPrefixRegion x H η := by
  rintro u ⟨hu, hb⟩
  constructor
  · intro i
    have h0 : 0 ≤ u i :=
      (mul_nonneg (by norm_num) (bandScale_nonneg x (i.val+1))).trans (hb i).1
    exact (hu.1 i).trans (le_add_of_nonneg_right (mul_nonneg (xi_sub_one_pos _ _).le h0))
  · have hh := hu.2
    have he : B x ≤ xi x 0*B x := by nlinarith [xi_sub_one_pos x 0]
    linarith

lemma perturbed_banded_subset_relaxation {x : ℝ} {H : ℕ} (η : TailDatum H) :
    perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H ⊆
      prefixRegion (R x H) (B x+topPerturbation x) (D (m x) η)
        ((fun i => D (m x-(i.val+1)) η)-prefixPerturbation x H) := by
  rintro u ⟨hu, hb⟩
  constructor
  · intro i
    have he : (xi x (i.val+1)-1)*u i ≤ prefixPerturbation x H i :=
      mul_le_mul_of_nonneg_left (hb i).2 (xi_sub_one_pos _ _).le
    have hh := hu.1 i
    change D (m x-(i.val+1)) η-prefixPerturbation x H i ≤ prefixLinear (R x H) u i
    linarith
  · have hh := hu.2
    dsimp [topPerturbation]
    nlinarith

end TotientAsymptotic

end

end OAI
