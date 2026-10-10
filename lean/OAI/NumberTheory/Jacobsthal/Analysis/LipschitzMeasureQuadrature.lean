import OAI.NumberTheory.Jacobsthal.Estimates.WeightedMonotoneBound

namespace OAI

namespace Erdos970

section

open MeasureTheory Set
namespace ErdosContinuousBoundary
open ErdosMonotoneQuadrature

theorem lipschitz_add_linear_monotone {g : ℝ → ℝ} {L : NNReal}
    (hg : LipschitzOnWith L g (Icc 1 2)) :
    MonotoneOn (fun x => g x+(L:ℝ)*x) (Icc 1 2) := by
  intro x hx y hy hxy
  have h := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxy)] at h
  have hle := le_abs_self (g x-g y)
  dsimp only
  nlinarith

theorem lipschitz_measure_discrepancy
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : ℝ → ℝ) (L : NNReal) (D E : ℝ) (hD : 0 ≤ D)
    (hg : LipschitzOnWith L g (Icc 1 2)) (hbound : ∀ x ∈ Icc 1 2,|g x| ≤ D)
    (hd : ∀ S : Set ℝ,S.OrdConnected → S ⊆ Icc 1 2 → |μ.real S-ν.real S| ≤ E)
    {J : Set ℝ} (hJ : J.OrdConnected) (hsub : J ⊆ Icc 1 2) :
    |(∫ x in J,g x ∂μ)-(∫ x in J,g x ∂ν)| ≤ 3*E*(D+4*(L:ℝ)) := by
  let A : ℝ → ℝ := fun x => g x+(L:ℝ)*x
  let B : ℝ → ℝ := fun x => (L:ℝ)*x
  have hL : 0 ≤ (L:ℝ) := L.property
  have hA : MonotoneOn A (Icc 1 2) := lipschitz_add_linear_monotone hg
  have hB : MonotoneOn B (Icc 1 2) := fun x _ y _ hxy => mul_le_mul_of_nonneg_left hxy hL
  have hBb : ∀ x ∈ Icc 1 2,|B x| ≤ 2*(L:ℝ) := by
    intro x hx
    rw [abs_of_nonneg (mul_nonneg hL (by linarith [hx.1]))]
    nlinarith [hx.2]
  have hAb : ∀ x ∈ Icc 1 2,|A x| ≤ D+2*(L:ℝ) := by
    intro x hx
    exact (abs_add_le _ _).trans (add_le_add (hbound x hx) (hBb x hx))
  have hqa := signed_monotone_integral_discrepancy μ ν 1 2 (D+2*(L:ℝ)) E
    (by positivity) A (Or.inl hA) hAb hd hJ hsub
  have hqb := signed_monotone_integral_discrepancy μ ν 1 2 (2*(L:ℝ)) E
    (by positivity) B (Or.inl hB) hBb hd hJ hsub
  have hAm : IntegrableOn A J μ := (hA.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hAn : IntegrableOn A J ν := (hA.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hBm : IntegrableOn B J μ := (hB.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have hBn : IntegrableOn B J ν := (hB.integrableOn_isCompact isCompact_Icc).mono_set hsub
  have he : g = fun x => A x-B x := by funext x; dsimp [A,B]; ring
  have heq : (∫ x in J,g x ∂μ)-(∫ x in J,g x ∂ν) =
      ((∫ x in J,A x ∂μ)-(∫ x in J,A x ∂ν))-
        ((∫ x in J,B x ∂μ)-(∫ x in J,B x ∂ν)) := by
    rw [he,integral_sub hAm hBm,integral_sub hAn hBn]
    ring
  rw [heq]
  calc
    _ ≤ |(∫ x in J,A x ∂μ)-(∫ x in J,A x ∂ν)|+
        |(∫ x in J,B x ∂μ)-(∫ x in J,B x ∂ν)| := abs_sub _ _
    _ ≤ 3*E*(D+2*(L:ℝ))+3*E*(2*(L:ℝ)) := add_le_add hqa hqb
    _ = _ := by ring

end ErdosContinuousBoundary

end

end Erdos970

end OAI
