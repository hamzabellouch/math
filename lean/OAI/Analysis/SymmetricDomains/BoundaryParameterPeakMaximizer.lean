import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio
import OAI.Analysis.SymmetricDomains.ParameterPeakMaximizer

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter
open scoped Topology

theorem strict_peak_point_not_mem {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton)
    {p : Affine n} {h : Affine n → ℂ} (hh : AnalyticOnNhd ℂ h univ)
    (hpp : h p = 1)
    (hpeak : ∀ q ∈ U, ‖h q‖ ≤ Real.exp (-(dist q p)^2)) : p ∉ U := by
  intro hp
  let f : U → ℂ := fun q => h q.val
  have hg : ∀ (j : ℕ) (q : U), ScalarAnalyticAt (f) q := fun _ q =>
    (holomorphicOnSubset_val U).entire_scalar_comp hh q
  have hb : ∀ (j : ℕ) (q : U), ‖f q‖ ≤ 1 := by
    intro _ q
    exact (hpeak q.val q.property).trans
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hfc : Continuous f := hh.continuous.comp continuous_subtype_val
  have he : ∀ q : U, f q = 1 := scalar_maximum_of_holomorphy hV hUV hU hc
    (fun _ => f) hg hb f hfc (fun _ => tendsto_const_nhds) (q := ⟨p,hp⟩) hpp
  have hall : ∀ q ∈ U, q = p := by
    intro q hq
    have hle : 1 ≤ Real.exp (-(dist q p)^2) := by
      simpa only [show h q = 1 from he ⟨q,hq⟩,norm_one] using hpeak q hq
    have hsq : 0 ≤ -(dist q p)^2 := Real.exp_le_exp.mp (by simpa using hle)
    have hd : dist q p = 0 := by nlinarith [sq_nonneg (dist q p)]
    exact dist_eq_zero.mp hd
  exact hn (fun x hx y hy => (hall x hx).trans (hall y hy).symm)

theorem polynomial_supported_boundary_point {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton)
    (hb : Bornology.IsBounded U) (P : MvPolynomial (Fin n) ℂ)
    (hP : ∃ q ∈ U, MvPolynomial.eval q P ≠ 0) :
    ∃ p ∈ closure U \ U, MvPolynomial.eval p P ≠ 0 ∧
      ∃ h : Affine n → ℂ, AnalyticOnNhd ℂ h univ ∧ h p = 1 ∧
        ∀ q ∈ closure U, ‖h q‖ ≤ Real.exp (-(dist q p)^2) := by
  obtain ⟨q,hq,hqP⟩ := hP
  obtain ⟨p,hp,hpP,h,hh,hpp,hpeak⟩ := polynomial_compact_peak (closure U)
    hb.isCompact_closure P ⟨q,subset_closure hq,hqP⟩
  exact ⟨p,⟨hp,strict_peak_point_not_mem hV hUV hU hc hn hh hpp
    (fun x hx => hpeak x (subset_closure hx))⟩,hpP,h,hh,hpp,hpeak⟩

end

open Set

theorem parameterPeak_maximizer_boundary {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton)
    (P : MvPolynomial (Fin n) ℂ) (a : Affine n →L[ℂ] ℂ)
    {p : Affine n} (hp : p ∈ closure U) (hpP : MvPolynomial.eval p P ≠ 0)
    (hm : IsMaxOn (parameterPotential P a) (closure U) p) :
    p ∈ closure U \ U := by
  exact ⟨hp, strict_peak_point_not_mem hV hUV hU hc hn
    (parameterPeak_analytic P a p) (parameterPeak_self P a hpP)
    (fun q hq => parameterPeak_bound P a hpP hm q (subset_closure hq))⟩

theorem exists_boundary_parameterPeak_maximizer {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (P : MvPolynomial (Fin n) ℂ) (hP : ∃ q ∈ U, MvPolynomial.eval q P ≠ 0)
    (a : Affine n →L[ℂ] ℂ) :
    ∃ p ∈ closure U \ U, MvPolynomial.eval p P ≠ 0 ∧
      IsMaxOn (parameterPotential P a) (closure U) p := by
  obtain ⟨q,hq,hqP⟩ := hP
  obtain ⟨p,hp,hpP,hm⟩ := exists_parameterPeak_maximizer P a hb.isCompact_closure
    ⟨q,subset_closure hq,hqP⟩
  exact ⟨p,parameterPeak_maximizer_boundary hV hUV hU hc hn P a hp hpP hm,hpP,hm⟩
end Release061

end

end OAI
