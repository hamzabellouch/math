import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.UnboundedSpectrum

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section ShiftedFormBottom
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shifted_form_spectral_infimum [Nontrivial H] (j : V →L[ℂ] H)
    (hj : Function.Injective j) (hd : DenseRange j) (A : V →L[ℂ] V)
    (hs : IsSelfAdjoint A) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (b : ℝ) :
    sInf {r : ℝ | (r : ℂ) ∈ unboundedSpectrum
      (inverseShift (formResolvent j A hc hA) b)} =
      sInf {e : ℝ | ∃ u : V, ‖j u‖ ^ 2 = 1 ∧ (⟪u, A u⟫_ℂ).re - b = e} := by
  let S := {e : ℝ | ∃ u : V, ‖j u‖ ^ 2 = 1 ∧ (⟪u, A u⟫_ℂ).re = e}
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := denseRange_exists_nonzero j hd
    let v : V := (‖j u‖⁻¹ : ℂ) • u
    refine ⟨(⟪v, A v⟫_ℂ).re, v, ?_, rfl⟩
    simp [v, norm_smul, hu]
  have hbb : BddBelow S := ⟨0, fun e ⟨u, _, he⟩ => he ▸ coercive_nonneg A hc hA u⟩
  have he : (OrderIso.addRight (-b)) '' S =
      {e : ℝ | ∃ u : V, ‖j u‖ ^ 2 = 1 ∧ (⟪u, A u⟫_ℂ).re - b = e} := by
    ext e
    constructor
    · rintro ⟨a, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨(⟪u, A u⟫_ℂ).re, ⟨u, hu, rfl⟩, rfl⟩
  have hi := (OrderIso.addRight (-b)).map_csInf' hne hbb
  rw [he] at hi
  change sInf S - b = _ at hi
  rw [form_infimum_eq_reciprocal j hj hd A hs hc hA] at hi
  rw [inverseShift_spectral_bottom _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (formResolvent_positive j A hs hc hA))
    (formResolvent_injective j hj hd A hc hA)]
  exact hi

end ShiftedFormBottom

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem shifted_representedOperator_graph (j : V →L[ℂ] H) (hj : Function.Injective j)
    (hd : DenseRange j) (A B : V →L[ℂ] V) (b : ℝ)
    (hAB : ∀ u v, ⟪v, A u⟫_ℂ = ⟪v, B u⟫_ℂ + (b : ℂ) * ⟪j v, j u⟫_ℂ)
    {c : ℝ} (hc : 0 < c) (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (x y : H) :
    (x, y) ∈ (inverseShift (formResolvent j A hc hA) b).graph ↔
      ∃ u : V, j u = x ∧ ∀ v : V, ⟪v, B u⟫_ℂ = ⟪j v, y⟫_ℂ := by
  have hi := formResolvent_injective j hj hd A hc hA
  have hg := representedOperator_graph j hj hd A hc hA x (y + (b : ℂ) • x)
  rw [representedOperator, inverseOperator_graph hi] at hg
  rw [inverseShift_graph _ hi, hg]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, fun v => ?_⟩
    have hh := he v
    rw [hAB, inner_add_right, inner_smul_right, hu] at hh
    exact add_right_cancel hh
  · rintro ⟨u, hu, he⟩
    refine ⟨u, hu, fun v => ?_⟩
    rw [hAB, he, inner_add_right, inner_smul_right, hu]

end CoulombAtom

end

end OAI
