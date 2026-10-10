import OAI.Analysis.LipschitzHilbert.Fourier.LineProductSpectrum
import OAI.Analysis.LipschitzHilbert.Estimates.FiniteEnergySchur
import Mathlib.Data.Int.Interval

namespace OAI

/-! Fixed annular Fourier overlap controls sums of the actual line
Schwartz functions appearing in the commutator proof. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem line_annular_nonzero_count (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) (eta : ℝ) :
    (I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)).card≤3 := by
  classical
  let A := I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)
  change A.card≤3
  have hsep (j : ℤ) (hj : j∈A) (k : ℤ) (hk : k∈A) (hjk : j+2≤k) : False := by
    have hjb := hband j (Finset.mem_filter.mp hj).1 eta (Finset.mem_filter.mp hj).2
    have hkb := hband k (Finset.mem_filter.mp hk).1 eta (Finset.mem_filter.mp hk).2
    have hp : (2:ℝ)^j*4≤(2:ℝ)^k := by
      calc
        _ = (2:ℝ)^(j+2) := by rw [zpow_add₀ (by norm_num)]; norm_num
        _ ≤ _ := zpow_le_zpow_right₀ (by norm_num) hjk
    have hh := mul_le_mul_of_nonneg_right hp (abs_nonneg eta)
    nlinarith only [hh,hjb.1,hkb.2]
  by_cases hne : A.Nonempty
  · obtain ⟨j,hj⟩ := hne
    have hsub : A⊆Finset.Icc (j-1) (j+1) := by
      intro k hk
      apply Finset.mem_Icc.mpr
      constructor
      · by_contra hn
        exact hsep k hk j hj (by omega)
      · by_contra hn
        exact hsep j hj k hk (by omega)
    apply (Finset.card_le_card hsub).trans
    rw [Int.card_Icc]
    omega
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty]
    omega

theorem line_annular_pointwise_square (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) (eta : ℝ) :
    ‖∑ k∈I, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2≤3*∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
  classical
  let A := I.filter (fun k => (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0)
  have he : (∑ k∈I, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta)=∑ k∈A, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkA
    by_contra h
    exact hkA (Finset.mem_filter.mpr ⟨hk,h⟩)
  have hs : (∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2)=∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hkA
    have hz : (𝓕 (f k) : SchwartzMap ℝ ℂ) eta=0 := by
      by_contra h
      exact hkA (Finset.mem_filter.mpr ⟨hk,h⟩)
    simp only [hz,norm_zero,zero_pow (by decide : 2≠0)]
  have hc : (A.card:ℝ)≤3 := by exact_mod_cast line_annular_nonzero_count I f hband eta
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
    (f:=fun _ => (1:ℝ)) (g:=fun k => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) (r:=fun k => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖)
    (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  rw [he]
  calc
    _ ≤ (∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (A.card:ℝ)*(∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) := hcs
    _ ≤ 3*(∑ k∈A, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) :=
      mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [hs]

theorem line_annular_sum_energy (I : Finset ℤ) (f : ℤ → SchwartzMap ℝ ℂ)
    (hband : ∀ k∈I, ∀ eta, (𝓕 (f k) : SchwartzMap ℝ ℂ) eta≠0 →
      11/12≤(2:ℝ)^k*|eta| ∧ (2:ℝ)^k*|eta|≤9/4) :
    (∫ x, ‖(∑ k∈I, f k) x‖^2)≤3*∑ k∈I, ∫ x, ‖f k x‖^2 := by
  have hi (k : ℤ) : Integrable (fun eta => ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2) :=
    ((𝓕 (f k) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  calc
    _ = ∫ eta, ‖(𝓕 (∑ k∈I, f k) : SchwartzMap ℝ ℂ) eta‖^2 :=
      (SchwartzMap.integral_norm_sq_fourier _).symm
    _ ≤ ∫ eta, 3*∑ k∈I, ‖(𝓕 (f k) : SchwartzMap ℝ ℂ) eta‖^2 := by
      apply integral_mono
        (((𝓕 (∑ k∈I, f k) : SchwartzMap ℝ ℂ).memLp 2 volume).integrable_norm_pow (by decide : 2≠0))
        ((integrable_finsetSum _ (fun k _ => hi k)).const_mul 3)
      intro eta
      simpa only [FourierTransform.fourier_sum,sum_apply] using line_annular_pointwise_square I f hband eta
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun k _ => hi k)]
      simp_rw [SchwartzMap.integral_norm_sq_fourier]

end LipschitzHilbert.PacketRepresentation

end

end OAI
