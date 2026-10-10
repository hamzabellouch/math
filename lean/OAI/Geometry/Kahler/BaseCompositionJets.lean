import OAI.Geometry.Kahler.BaseCauchyJets

namespace OAI

universe uKahler8418_1 uKahler8418_2 uKahler8437_1 uKahler8437_2 uKahler8437_3 uKahler8458_1 uKahler8458_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
open Set Filter Topology
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma analytic_real_jet_norm {E : Type uKahler8418_1} {F : Type uKahler8418_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {x : E} (hf : AnalyticAt ℂ f x) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖=‖iteratedFDeriv ℂ n f x‖ := by
  rw [← (hf.contDiffAt : ContDiffAt ℂ n f x).restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  exact ContinuousMultilinearMap.norm_restrictScalars _

lemma small_power_bound {t B : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hB : 1 ≤ B)
    {i n : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    B*t ≤ (B*t^((n:ℝ)⁻¹))^i := by
  have hn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [mul_pow,← Real.rpow_mul_natCast ht.le]
  have hex : (n:ℝ)⁻¹*(i:ℝ) ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hn).mpr (by exact_mod_cast hin)
  have hp : t ≤ t^((n:ℝ)⁻¹*(i:ℝ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hex
  exact mul_le_mul (by simpa using pow_le_pow_right₀ hB hi) hp ht.le (by positivity)

lemma norm_composition_jet_linear {E : Type uKahler8437_1} {F : Type uKahler8437_2} {G : Type uKahler8437_3}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {g : F → G} {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    {n : ℕ} (hn : 1 ≤ n) (hf : ContDiffOn ℝ n f s) (hg : ContDiff ℝ n g)
    {B C t : ℝ} (hB : 1 ≤ B) (ht : 0 < t) (ht1 : t ≤ 1)
    (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hbound : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ B*t) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ n.factorial*C*B^n*t := by
  have hh := norm_iteratedFDerivWithin_comp_le hg.contDiffOn hf le_rfl uniqueDiffOn_univ
    (hs.uniqueDiffOn) (mapsTo_univ f s) hx
    (C := C) (D := B*t^((n:ℝ)⁻¹))
    (by simpa only [iteratedFDerivWithin_univ] using hC)
    (fun i hi hin => by
      rw [iteratedFDerivWithin_of_isOpen i hs hx]
      exact (hbound i hi hin).trans (small_power_bound ht ht1 hB hi hin))
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at hh
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [mul_pow,← Real.rpow_mul_natCast ht.le,inv_mul_cancel₀ hn0,Real.rpow_one] at hh
  exact hh.trans_eq (by ring)

lemma smooth_jet_bound_compact {E : Type uKahler8458_1} {F : Type uKahler8458_2} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} (hg : ContDiff ℝ ∞ g)
    {s : Set E} (hs : IsCompact s) (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i, i ≤ n → ∀ x ∈ s, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
  have hex (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ s, ‖iteratedFDeriv ℝ i g x‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ i g) := ContDiff.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (i:ℕ∞) ≤ ⊤)) hg
    obtain ⟨C,hC⟩ := hs.bddAbove_image hc.norm.continuousOn
    exact ⟨max C 0,le_max_right _ _,fun x hx => (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩
  choose C hC hbound using hex
  refine ⟨1+∑ j ∈ Finset.range (n+1), C j,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.range (n+1)) (fun j _ => hC j)
    linarith
  · intro i hi x hx
    have hh := Finset.single_le_sum (s := Finset.range (n+1)) (fun j _ => hC j) (show i ∈ Finset.range (n+1) by simp; omega)
    exact (hbound i x hx).trans (by linarith)

end PinchedHartogs.BaseConstruction

end

end OAI
