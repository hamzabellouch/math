import OAI.NumberTheory.Ostmann.Construction.InitialLogGeometry
import OAI.NumberTheory.Ostmann.SchwartzCutoff
import OAI.NumberTheory.Ostmann.Section07SmoothPartition

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Ostmann.Construction
open scoped FourierTransform SchwartzMap

def realLeafBins {b s k : ℕ} (x : InitialCoordinates b s k) (tb td : ℝ) : ℝ :=
  ∏ h : Bool, smoothPartition ((∑ i, Real.log (x.bulk h i)) - tb) *
    smoothPartition ((∑ i, Real.log (x.spectator h i)) - td)

def realLeafScalar {b s k : ℕ} (x : InitialCoordinates b s k) (X : ℝ) (freq : ℤ)
    (tb td : ℝ) : ℂ :=
  (Real.sqrt (X / x.product) : ℂ) *
    𝓕 SchwartzCutoff.psi (-(freq : ℝ) * X / x.product) * (realLeafBins x tb td : ℂ)

def leafFourierBound : ℝ := (SchwartzMap.seminorm ℝ 0 0) (𝓕 SchwartzCutoff.psi) + 1

theorem leafFourierBound_pos : 0 < leafFourierBound := by
  have h := apply_nonneg ((SchwartzMap.seminorm ℝ 0 0)) (𝓕 SchwartzCutoff.psi)
  dsimp [leafFourierBound]
  linarith

theorem norm_fourier_psi_le (ξ : ℝ) : ‖𝓕 SchwartzCutoff.psi ξ‖ ≤ leafFourierBound :=
  (SchwartzMap.norm_le_seminorm ℝ (𝓕 SchwartzCutoff.psi) ξ).trans
    (le_add_of_nonneg_right zero_le_one)

theorem realLeafBins_bounds {b s k : ℕ} (x : InitialCoordinates b s k) (tb td : ℝ) :
    0 ≤ realLeafBins x tb td ∧ realLeafBins x tb td ≤ 1 := by
  have hn (h : Bool) : 0 ≤ smoothPartition ((∑ i, Real.log (x.bulk h i)) - tb) *
      smoothPartition ((∑ i, Real.log (x.spectator h i)) - td) :=
    mul_nonneg (smoothPartition_nonneg _) (smoothPartition_nonneg _)
  have hle (h : Bool) : smoothPartition ((∑ i, Real.log (x.bulk h i)) - tb) *
      smoothPartition ((∑ i, Real.log (x.spectator h i)) - td) ≤ 1 :=
    (mul_le_mul (smoothPartition_le_one _) (smoothPartition_le_one _)
      (smoothPartition_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact ⟨Finset.prod_nonneg (fun h _ => hn h), Finset.prod_le_one₀ (fun h _ => hn h) (fun h _ => hle h)⟩

theorem realLeafBins_support {b s k : ℕ} (x : InitialCoordinates b s k) (tb td : ℝ)
    (hb : realLeafBins x tb td ≠ 0) :
    (∀ h, |(∑ i, Real.log (x.bulk h i)) - tb| ≤ 1) ∧
      (∀ h, |(∑ i, Real.log (x.spectator h i)) - td| ≤ 1) := by
  have hterm (h : Bool) := (Finset.prod_ne_zero_iff.mp hb) h (Finset.mem_univ h)
  have hφ (y : ℝ) (hy : smoothPartition y ≠ 0) : |y| ≤ 1 := by
    have h := smoothPartition_support_subset hy
    exact abs_le.mpr ⟨h.1.le, h.2.le⟩
  exact ⟨fun h => hφ _ (mul_ne_zero_iff.mp (hterm h)).1,
    fun h => hφ _ (mul_ne_zero_iff.mp (hterm h)).2⟩

theorem positive_initial_product {b s k : ℕ} (x : InitialCoordinates b s k) (hx : x.Positive) :
    0 < x.product := by
  rcases hx with ⟨hg, hb, hs, ht, hc⟩
  unfold InitialCoordinates.product
  exact mul_pos (mul_pos (mul_pos (mul_pos
    (Finset.prod_pos (fun h _ => hg h))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun i _ => hb h i))))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun i _ => hs h i))))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun i _ => ht h i))))
    (Finset.prod_pos (fun h _ => Finset.prod_pos (fun j _ => Finset.prod_pos (fun i _ => hc h j i))))

theorem sqrt_ratio_le_of_log_lower (X P Δ W : ℝ) (hX : 0 < X) (hP : 0 < P)
    (hlog : Real.log X + Δ - W ≤ Real.log P) :
    Real.sqrt (X / P) ≤ Real.exp ((-Δ + W) / 2) := by
  have hratio : X / P ≤ Real.exp (-Δ + W) := by
    apply (Real.log_le_iff_le_exp (div_pos hX hP)).mp
    rw [Real.log_div hX.ne' hP.ne']
    linarith
  have heq : Real.exp ((-Δ + W) / 2) ^ 2 = Real.exp (-Δ + W) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.sq_sqrt (div_nonneg hX.le hP.le), Real.sqrt_nonneg (X / P),
    Real.exp_pos ((-Δ + W) / 2)]

theorem realLeafScalar_norm_le {b s k : ℕ} (x : InitialCoordinates b s k)
    (X : ℝ) (freq : ℤ) (tb td Δ W : ℝ) (hX : 0 < X) (hx : x.Positive)
    (hlog : Real.log X + Δ - W ≤ Real.log x.product) :
    ‖realLeafScalar x X freq tb td‖ ≤ leafFourierBound * Real.exp ((-Δ + W) / 2) := by
  rw [realLeafScalar, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realLeafBins_bounds x tb td).1]
  calc
    _ ≤ (Real.sqrt (X / x.product) * leafFourierBound) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (norm_fourier_psi_le _) (Real.sqrt_nonneg _))
        (realLeafBins_bounds x tb td).2 (realLeafBins_bounds x tb td).1
        (mul_nonneg (Real.sqrt_nonneg _) leafFourierBound_pos.le)
    _ ≤ _ := by
      rw [mul_one, mul_comm]
      exact mul_le_mul_of_nonneg_left
        (sqrt_ratio_le_of_log_lower X x.product Δ W hX (positive_initial_product x hx) hlog)
        leafFourierBound_pos.le

theorem realLeafScalar_norm_le_of_source_cells {b s k : ℕ} (x : InitialCoordinates b s k)
    (hx : x.Positive) (X : ℝ) (hX : 0 < X) (freq : ℤ) (G tb td Δ E : ℝ)
    (topCenter : Bool → Fin 3 → ℝ) (compCenter : Bool → Fin k → Fin 2 → ℝ)
    (hg : ∀ h, |Real.log (x.giant h) - G| ≤ 1)
    (ht : ∀ h i, |Real.log (x.top h i) - topCenter h i| ≤ 1)
    (hc : ∀ h j i, |Real.log (x.compensation h j i) - compCenter h j i| ≤ 1)
    (hcenter : Real.log X + Δ - E ≤ 2 * G + 2 * tb + 2 * td +
      (∑ h, ∑ i, topCenter h i) + (∑ h, ∑ j, ∑ i, compCenter h j i)) :
    ‖realLeafScalar x X freq tb td‖ ≤
      leafFourierBound * Real.exp ((-Δ + (E + 12 + 4 * (k : ℝ))) / 2) := by
  by_cases hb : realLeafBins x tb td = 0
  · simp only [realLeafScalar, hb, Complex.ofReal_zero, mul_zero, norm_zero]
    exact mul_nonneg leafFourierBound_pos.le (Real.exp_pos _).le
  · obtain ⟨hbulk, hspec⟩ := realLeafBins_support x tb td hb
    have hwindow := initial_log_product_support x hx G tb td topCenter compCenter hg hbulk hspec ht hc
    apply realLeafScalar_norm_le x X freq tb td Δ (E + 12 + 4 * (k : ℝ)) hX hx
    have hl := (abs_le.mp hwindow).1
    linarith

end Ostmann.Arithmetic

end

end OAI
