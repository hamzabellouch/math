import OAI.NumberTheory.Ostmann.Dirichlet.CompactZeroFree
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaDisk

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open Set Filter
open scoped Topology
namespace Ostmann.Dirichlet

theorem exists_regularZeta_compact_zero_free_strip (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ,
      1 - δ ≤ s.re → |s.im| ≤ T → regularZeta s ≠ 0 := by
  let K : Set ℂ := (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) '' Icc (-T) T
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hopen : IsOpen {s : ℂ | regularZeta s ≠ 0} :=
    isOpen_ne.preimage (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).continuous
  have hKne : K ⊆ {s : ℂ | regularZeta s ≠ 0} := by
    rintro _ ⟨t, ht, rfl⟩
    exact regularZeta_ne_zero_of_one_le_re (by simp)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hopen hKne
  refine ⟨δ, hδ, ?_⟩
  intro s hs him
  by_cases hre : 1 ≤ s.re
  · exact regularZeta_ne_zero_of_one_le_re hre
  · apply hsub
    apply Metric.mem_cthickening_of_dist_le s (1 + (s.im : ℂ) * Complex.I) δ K
    · exact ⟨s.im, abs_le.mp him, rfl⟩
    · have he : s - (1 + (s.im : ℂ) * Complex.I) = ((s.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith : s.re - 1 ≤ 0)]
      linarith

lemma differentiableAt_zeta_log_derivative {s : ℂ} (hs : s ≠ 1)
    (hn : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (fun z => deriv riemannZeta z / riemannZeta z) s := by
  have ha := analyticOn_riemannZeta s hs
  exact ha.deriv.differentiableAt.div ha.differentiableAt hn

theorem exists_zeta_log_derivative_compact_strip :
    ∃ sigma₂ : ℝ, sigma₂ < 1 ∧
      DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
        ((uIcc sigma₂ 2 ×ℂ uIcc (-3) 3) \ {1}) := by
  obtain ⟨δ, hδ, hb⟩ := exists_regularZeta_compact_zero_free_strip 3
  refine ⟨1 - δ, by linarith, ?_⟩
  intro s hs
  have hs1 : s ≠ 1 := hs.2
  have hre : 1 - δ ≤ s.re := by
    have h := hs.1.1
    rw [uIcc_of_le (by linarith : 1 - δ ≤ 2)] at h
    exact h.1
  have him : |s.im| ≤ 3 := by
    have h := hs.1.2
    rw [uIcc_of_le (by norm_num : (-3 : ℝ) ≤ 3)] at h
    exact abs_le.mpr h
  have hreg := hb s hre him
  have hn : riemannZeta s ≠ 0 := by
    intro hz
    apply hreg
    rw [regularZeta, DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1,
      DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq,
      hz, mul_zero]
  exact (differentiableAt_zeta_log_derivative hs1 hn).differentiableWithinAt

end Ostmann.Dirichlet

end OAI
