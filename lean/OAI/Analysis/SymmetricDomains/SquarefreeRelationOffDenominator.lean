import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

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
open Polynomial
open scoped nonZeroDivisors

theorem polynomial_clear_denominators
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (p : K[X]) :
    ∃ a : R, a ≠ 0 ∧ ∃ q : R[X],
      q.map (algebraMap R K) = C (algebraMap R K a) * p := by
  obtain ⟨a,ha,hq⟩ := IsLocalization.integerNormalization_spec R⁰ p
  refine ⟨a,mem_nonZeroDivisors_iff_ne_zero.mp ha,
    IsLocalization.integerNormalization R⁰ p,?_⟩
  rw [hq,← algebraMap_smul K a p,Polynomial.smul_eq_C_mul]

theorem squarefree_relation_off_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [CharZero K]
    [Algebra R K] [IsFractionRing R K]
    (p : R[X]) (hp : p ≠ 0) :
    ∃ q : R[X], q ≠ 0 ∧ (q.map (algebraMap R K)).Separable ∧
      ∃ D : R, D ≠ 0 ∧
        ∀ {F : Type*} [Field F] (e : R →+* F), e D ≠ 0 →
          ∀ z : F, p.eval₂ e z = 0 ↔ q.eval₂ e z = 0 := by
  classical
  let e := algebraMap R K
  have hei : Function.Injective e := IsFractionRing.injective R K
  have hmap : Function.Injective (Polynomial.map e) := Polynomial.map_injective e hei
  have hp' : p.map e ≠ 0 := fun hz => hp (hmap (by simpa only [Polynomial.map_zero] using hz))
  obtain ⟨v,m,hv,hvp,hpv⟩ := exists_squarefree_dvd_pow_of_ne_zero hp'
  have hv0 : v ≠ 0 := by rintro rfl; exact hp' (by simpa using hvp)
  have hvsep : v.Separable := PerfectField.separable_iff_squarefree.mpr hv
  obtain ⟨w,hw⟩ := hvp
  obtain ⟨j,hj⟩ := hpv
  obtain ⟨a,ha,q,hq⟩ := polynomial_clear_denominators (R := R) v
  obtain ⟨b,hb,W,hW⟩ := polynomial_clear_denominators (R := R) w
  obtain ⟨c,hc,J,hJ⟩ := polynomial_clear_denominators (R := R) j
  have haK : e a ≠ 0 := by simpa only [map_zero] using hei.ne_iff.mpr ha
  have hq0 : q ≠ 0 := by
    intro hz
    rw [hz,Polynomial.map_zero] at hq
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr haK) hv0) hq.symm
  have hqs : (q.map e).Separable := by
    rw [hq]
    exact Polynomial.Separable.unit_mul (IsUnit.map C (isUnit_iff_ne_zero.mpr haK)) hvsep
  have h₁ : q*W = C (a*b)*p := by
    apply hmap
    simp only [Polynomial.map_mul,Polynomial.map_C,map_mul]
    rw [hq,hW,hw]
    dsimp only [e]
    ring
  have h₂ : C c*q^m = C (a^m)*p*J := by
    apply hmap
    simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,map_pow]
    rw [hq,hJ,mul_pow,← Polynomial.C_pow,hj]
    dsimp only [e]
    ring
  refine ⟨q,hq0,hqs,a*b*c,mul_ne_zero (mul_ne_zero ha hb) hc,?_⟩
  intro F _ f hf z
  have hab : f (a*b) ≠ 0 := fun hz => hf (by simp only [map_mul,hz,zero_mul])
  have hc' : f c ≠ 0 := fun hz => hf (by simp only [map_mul,hz,mul_zero])
  constructor
  · intro hz
    have he := congrArg (Polynomial.eval₂ f z) h₂
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,hz,mul_zero,zero_mul] at he
    have hpw : (q.eval₂ f z)^m = 0 := (mul_eq_zero.mp he).resolve_left hc'
    by_contra hn
    exact pow_ne_zero m hn hpw
  · intro hz
    have he := congrArg (Polynomial.eval₂ f z) h₁
    simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C,hz,zero_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hab

end Release061

end

end OAI
