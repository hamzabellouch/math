import OAI.NumberTheory.Ostmann.ZeroDensity.DensitySobolevPoint

namespace OAI

/-! # Disjoint unit windows for separated height samples -/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators Classical

 theorem density_disjoint_sample_windows {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) :
    Set.Pairwise (↑S) (fun i j => Disjoint (Ioc (t i - 1 / 2) (t i + 1 / 2))
      (Ioc (t j - 1 / 2) (t j + 1 / 2))) := by
  intro i hi j hj hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hh := hsep i hi j hj hij
  have hn : |t i - t j| < 1 := abs_lt.mpr ⟨by linarith [hx.2, hy.1], by linarith [hy.2, hx.1]⟩
  linarith

 theorem density_sample_window_integrals {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (T : ℝ) (hT : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (F : ℝ → ℝ) (hF : Continuous F) (hFnon : ∀ x, 0 ≤ F x) :
    (∑ i ∈ S, ∫ x in t i - 1 / 2..t i + 1 / 2, F x) ≤
      ∫ x in Icc (-T - 1) (T + 1), F x := by
  have he : (∑ i ∈ S, ∫ x in t i - 1 / 2..t i + 1 / 2, F x) =
      ∫ x in ⋃ i ∈ S, Ioc (t i - 1 / 2) (t i + 1 / 2), F x := by
    have horder (i : ι) : t i - 1 / 2 ≤ t i + 1 / 2 := by linarith
    simp_rw [intervalIntegral.integral_of_le (horder _)]
    exact (integral_biUnion_finset S (fun _ _ => measurableSet_Ioc)
      (density_disjoint_sample_windows S t hsep)
      (fun i _ => hF.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).symm
  rw [he]
  apply setIntegral_mono_set hF.integrableOn_Icc (Filter.Eventually.of_forall hFnon)
  apply Filter.Eventually.of_forall
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have ht := abs_le.mp (hT i hi)
  exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

 theorem density_separated_samples {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (T : ℝ) (hT : ∀ i ∈ S, |t i| ≤ T)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (f g : ℝ → ℂ) (hf : ∀ x, HasDerivAt f (g x) x) (hg : Continuous g) :
    (∑ i ∈ S, ‖f (t i)‖ ^ 2) ≤
      2 * (∫ x in Icc (-T - 1) (T + 1), ‖f x‖ ^ 2) +
        ∫ x in Icc (-T - 1) (T + 1), ‖g x‖ ^ 2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hs := Finset.sum_le_sum (s := S) (fun i _ => density_unit_interval_sample f g hf hg (t i))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  apply hs.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (density_sample_window_integrals S t T hT hsep
      (fun x => ‖f x‖ ^ 2) (hfc.norm.pow 2) (fun _ => sq_nonneg _)) (by norm_num))
    (density_sample_window_integrals S t T hT hsep
      (fun x => ‖g x‖ ^ 2) (hg.norm.pow 2) (fun _ => sq_nonneg _))

end Ostmann

end OAI
