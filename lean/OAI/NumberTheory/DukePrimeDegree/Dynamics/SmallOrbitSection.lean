import OAI.NumberTheory.DukePrimeDegree.Dynamics.SeparatedOrbitCover
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! # Small complete sections without a map-ergodicity hypothesis -/

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] [BorelSpace Y] in
lemma measurePreserving_homeomorph_pow (μ : Measure Y) (e : Y ≃ₜ Y)
    (he : MeasurePreserving e μ μ) (n : ℕ) : MeasurePreserving (e^n) μ μ := by
  induction n with
  | zero =>
    rw [pow_zero]
    change MeasurePreserving id μ μ
    exact MeasurePreserving.id μ
  | succ n ih =>
    rw [pow_succ]
    change MeasurePreserving ((e^n) ∘ e) μ μ
    exact ih.comp he

omit [T2Space Y] [SecondCountableTopology Y] in
lemma separated_section_mass_bound (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ) (N : ℕ)
    {S : Set Y} (hS : MeasurableSet S)
    (hfree : ∀ x ∈ S, ∀ k : Fin N, (e^(k.val+1)) x ≠ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, finiteOrbitNeighbor e N x y → x=y) :
    (N+1:ℝ≥0∞)*μ S ≤ 1 := by
  have hdis {i j : ℕ} (hj : j ≤ N) (hij : i < j) :
      Disjoint ((e^i) '' S) ((e^j) '' S) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have hdiff : i+(j-i)=j := Nat.add_sub_of_le hij.le
    have hxy : x=(e^(j-i)) y := by
      apply (e^i).injective
      rw [←Homeomorph.mul_apply,←pow_add,hdiff]
      exact hxz.trans hyz.symm
    let k : Fin N := ⟨j-i-1,by omega⟩
    have hk : k.val+1=j-i := by dsimp only [k]; omega
    have heq : x=y := hsep x hx y hy (Or.inr ⟨k,Or.inr (by simpa only [hk] using hxy.symm)⟩)
    subst y
    exact hfree x hx k (by simpa only [hk] using hxy.symm)
  have hpair : Pairwise (Disjoint on (fun i : Fin (N+1) => (e^i.val) '' S)) := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hdis (by omega) h
    · exact (hdis (by omega) h).symm
  have hm (i : Fin (N+1)) : MeasurableSet ((e^i.val) '' S) :=
    (e^i.val).measurableEmbedding.measurableSet_image.mpr hS
  have hv (i : Fin (N+1)) : μ ((e^i.val) '' S)=μ S := by
    have hp := measurePreserving_homeomorph_pow μ e he i.val
    calc
      μ ((e^i.val) '' S) = (μ.map (e^i.val)) ((e^i.val) '' S) := by rw [hp.map_eq]
      _ = μ ((e^i.val) ⁻¹' ((e^i.val) '' S)) := Measure.map_apply hp.measurable (hm i)
      _ = μ S := congrArg μ ((e^i.val).injective.preimage_image S)
  have H : (∑' i : Fin (N+1), μ ((e^i.val) '' S)) ≤ μ univ := by
    rw [←measure_iUnion hpair hm]
    exact measure_mono (subset_univ _)
  simpa only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_add,Nat.cast_one,measure_univ] using H

/-- Inside an aperiodic measurable set, complete sections can have
arbitrarily small measure. Completeness refers to the represented orbits,
so no ergodicity of e is needed. -/
theorem exists_small_complete_orbit_section
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ n : ℕ, 0 < n → (e^n) x ≠ x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set Y, MeasurableSet S ∧ S ⊆ A ∧ μ.real S < ε ∧
      ∀ x ∈ A, ∃ y ∈ S, (homeomorphOrbitSetoid e).r x y := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  obtain ⟨S,hS,hSA,hsep,hmeet⟩ := exists_finite_orbit_section e N hA
    (fun x hx k => hfree x hx (k.val+1) (by omega))
  refine ⟨S,hS,hSA,?_,hmeet⟩
  have H := separated_section_mass_bound μ e he N hS
    (fun x hx k => hfree x (hSA hx) (k.val+1) (by omega)) hsep
  have Hr := ENNReal.toReal_mono (by simp) H
  rw [ENNReal.toReal_mul,ENNReal.toReal_add (by simp) (by simp)] at Hr
  simp only [ENNReal.toReal_natCast,ENNReal.toReal_one] at Hr
  change (N+1:ℝ)*μ.real S ≤ 1 at Hr
  have hS0 : 0 ≤ μ.real S := measureReal_nonneg
  have hN0 : (0:ℝ) < N+1 := by positivity
  have hNε : 1 < (N+1:ℝ)*ε := by
    have ht : 1 < (N:ℝ)*ε := (div_lt_iff₀ hε).mp hN
    nlinarith
  nlinarith

end DukePrimeDegree

end

end OAI
