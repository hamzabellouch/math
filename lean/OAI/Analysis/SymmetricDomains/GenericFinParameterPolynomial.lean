import Mathlib
import OAI.Analysis.SymmetricDomains.GenericPolynomialParameterFactor

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
open Set Filter Topology MeasureTheory Metric

theorem generic_polynomial_parameter_nonzero {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → Polynomial.eval₂ (MvPolynomial.eval z) t P ≠ 0 := by
  obtain ⟨E,hE,hfactor⟩ := generic_polynomial_parameter_factor P hP
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨k,g,_,_,he,hunit⟩ := hfactor s hs
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hunit
  refine ⟨r,hr,?_⟩
  intro z hz t ht ht0
  have hzt : (z,t) ∈ ball ((fun i => (s i : ℂ)),(0 : ℂ)) r := by
    simpa only [mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hz ht
  rw [he (z,t)]
  exact mul_ne_zero (pow_ne_zero k ht0) (hsub hzt)

theorem separable_map_of_leading_resultant_ne_zero
    {R K : Type*} [CommRing R] [Field K] (P : Polynomial R) (e : R →+* K)
    (hl : e P.leadingCoeff ≠ 0)
    (hd : e (P.resultant P.derivative) ≠ 0) : (P.map e).Separable := by
  by_cases hdeg : P.natDegree = 0
  · have hP : P = Polynomial.C P.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff,hdeg] using Polynomial.eq_C_of_natDegree_eq_zero hdeg
    rw [hP,Polynomial.map_C]
    exact (Polynomial.separable_C _).mpr (isUnit_iff_ne_zero.mpr hl)
  · obtain ⟨a,b,_,_,hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
      P P.derivative le_rfl le_rfl (Or.inl hdeg)
    have hh := congrArg (Polynomial.map e) hab
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C] at hh
    refine ⟨Polynomial.C ((e (P.resultant P.derivative))⁻¹) * a.map e,
      Polynomial.C ((e (P.resultant P.derivative))⁻¹) * b.map e,?_⟩
    rw [Polynomial.derivative_map]
    calc
      _ = Polynomial.C ((e (P.resultant P.derivative))⁻¹) *
          (P.map e * a.map e + P.derivative.map e * b.map e) := by ring
      _ = 1 := by rw [hh,← Polynomial.C_mul,inv_mul_cancel₀ hd,Polynomial.C_1]

theorem generic_mvpolynomial_parameter_nonzero {n : ℕ}
    (P : MvPolynomial (Option (Fin n)) ℂ) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → MvPolynomial.eval (fun o => Option.elim o t z) P ≠ 0 := by
  obtain ⟨E,hE,hn⟩ := generic_polynomial_parameter_nonzero
    (MvPolynomial.optionEquivLeft ℂ (Fin n) P)
    ((MvPolynomial.optionEquivLeft ℂ (Fin n)).injective.ne hP)
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨r,hr,hn⟩ := hn s hs
  refine ⟨r,hr,?_⟩
  intro z hz t ht ht0
  simpa only [MvPolynomial.optionEquivLeft_elim_eval,Polynomial.eval_map] using hn z hz t ht ht0

theorem generic_parameter_polynomial_separable {n : ℕ}
    (P : Polynomial (MvPolynomial (Option (Fin n)) ℂ))
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 →
          MvPolynomial.eval (fun o => Option.elim o t z) P.leadingCoeff ≠ 0 ∧
          (P.map (MvPolynomial.eval (fun o => Option.elim o t z))).Separable := by
  obtain ⟨E₁,hE₁,h₁⟩ := generic_mvpolynomial_parameter_nonzero P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP)
  obtain ⟨E₂,hE₂,h₂⟩ := generic_mvpolynomial_parameter_nonzero (P.resultant P.derivative) hres
  refine ⟨E₁ ∪ E₂,measure_union_null hE₁ hE₂,?_⟩
  intro s hs
  have hs₁ : s ∉ E₁ := fun h => hs (Or.inl h)
  have hs₂ : s ∉ E₂ := fun h => hs (Or.inr h)
  obtain ⟨r₁,hr₁,hn₁⟩ := h₁ s hs₁
  obtain ⟨r₂,hr₂,hn₂⟩ := h₂ s hs₂
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro z hz t ht ht0
  have hz₁ := ball_subset_ball (min_le_left r₁ r₂) hz
  have hz₂ := ball_subset_ball (min_le_right r₁ r₂) hz
  have ht₁ := ball_subset_ball (min_le_left r₁ r₂) ht
  have ht₂ := ball_subset_ball (min_le_right r₁ r₂) ht
  have hl := hn₁ z hz₁ t ht₁ ht0
  exact ⟨hl,separable_map_of_leading_resultant_ne_zero P _ hl (hn₂ z hz₂ t ht₂ ht0)⟩

theorem generic_fin_polynomial_parameter_nonzero {n : ℕ}
    (P : MvPolynomial (Fin (n+1)) ℂ) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 → MvPolynomial.eval (Fin.cons t z) P ≠ 0 := by
  obtain ⟨E,hE,hn⟩ := generic_polynomial_parameter_nonzero
    (MvPolynomial.finSuccEquiv ℂ n P)
    ((MvPolynomial.finSuccEquiv ℂ n).injective.ne hP)
  refine ⟨E,hE,?_⟩
  intro s hs
  obtain ⟨r,hr,hn⟩ := hn s hs
  refine ⟨r,hr,?_⟩
  intro z hz t ht ht0
  rw [MvPolynomial.eval_eq_eval_mv_eval' z t P,Polynomial.eval_map]
  exact hn z hz t ht ht0

theorem generic_fin_parameter_polynomial_separable {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin (n+1)) ℂ))
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ r > 0, ∀ z ∈ ball (fun i => (s i : ℂ)) r,
        ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 →
          MvPolynomial.eval (Fin.cons t z) P.leadingCoeff ≠ 0 ∧
          (P.map (MvPolynomial.eval (Fin.cons t z))).Separable := by
  obtain ⟨E₁,hE₁,h₁⟩ := generic_fin_polynomial_parameter_nonzero P.leadingCoeff
    (Polynomial.leadingCoeff_ne_zero.mpr hP)
  obtain ⟨E₂,hE₂,h₂⟩ := generic_fin_polynomial_parameter_nonzero (P.resultant P.derivative) hres
  refine ⟨E₁ ∪ E₂,measure_union_null hE₁ hE₂,?_⟩
  intro s hs
  have hs₁ : s ∉ E₁ := fun h => hs (Or.inl h)
  have hs₂ : s ∉ E₂ := fun h => hs (Or.inr h)
  obtain ⟨r₁,hr₁,hn₁⟩ := h₁ s hs₁
  obtain ⟨r₂,hr₂,hn₂⟩ := h₂ s hs₂
  refine ⟨min r₁ r₂,lt_min hr₁ hr₂,?_⟩
  intro z hz t ht ht0
  have hz₁ := ball_subset_ball (min_le_left r₁ r₂) hz
  have hz₂ := ball_subset_ball (min_le_right r₁ r₂) hz
  have ht₁ := ball_subset_ball (min_le_left r₁ r₂) ht
  have ht₂ := ball_subset_ball (min_le_right r₁ r₂) ht
  have hl := hn₁ z hz₁ t ht₁ ht0
  exact ⟨hl,separable_map_of_leading_resultant_ne_zero P _ hl (hn₂ z hz₂ t ht₂ ht0)⟩

end Release061

end

end OAI
