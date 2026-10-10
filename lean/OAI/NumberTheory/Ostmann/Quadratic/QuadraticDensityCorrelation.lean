import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDensitySum
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSupportCount

namespace OAI

/-! # The large-kernel correlation of the original centered-density quadratic sums -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

/-- This is the finite, explicit form of the manuscript's correlation (src12).
The cutoff hypotheses give both the support pair count and smooth scaling;
all Fourier and nonunit conditions are supplied by the centered densities. -/
theorem quadratic_density_correlation_bound (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (S : ∀ p : ℕ, Finset (ZMod p)) (W V : Finset ℕ)
    (a : ZMod ps.prod) (b : ZMod qs.prod) (Φ Ψ : 𝓢(ℝ, ℂ))
    (θ η R v C : ℝ) (M N : ℕ) (hR : 0 < R) (hv : 0 < v) (hC : 0 ≤ C)
    (hM : 0 < M) (hN : 0 < N) (hperiod : rs.prod ^ 2 ≤ N)
    (hW : ∀ w ∈ W, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * ps.prod / ((N : ℝ) * v))
    (hV : ∀ w ∈ V, 0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * qs.prod / ((N : ℝ) * v)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N,
      quadraticDensitySum (densityFourier (densityCRTList ps hp hcp S).value) W a θ Φ R v (n + M) *
      conj (quadraticDensitySum (densityFourier (densityCRTList qs hq hcq S).value) V b η Ψ R v (n + M)) /
        ((n + M : ℕ) : ℂ)‖ ≤
      C * (4 * correlationWeightBudget Φ Ψ C C) *
        (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod := by
  intro _ _
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let f : ∀ p : ℕ, ZMod p → ℂ := fun p x => (centeredDensity (S p) x : ℂ)
  have hfnorm (p : ℕ) (hp' : p ∈ rs) (x : ZMod p) : ‖f p x‖ ≤ 1 := by
    let : NeZero p := ⟨(hr p hp').ne_zero⟩
    simpa only [f, Complex.norm_real, Real.norm_eq_abs] using centeredDensity_abs_le (S p) x
  have hep := densityCRTList_value_eq_primeCRTFunction ps hp hcp S
  have heq := densityCRTList_value_eq_primeCRTFunction qs hq hcq S
  have hgp : ∀ x, ¬IsUnit x → densityFourier (primeCRTFunction ps hp hcp f) x = 0 := by
    rw [← hep]
    exact (densityCRTList ps hp hcp S).fourier_nonunit
  have hgq : ∀ x, ¬IsUnit x → densityFourier (primeCRTFunction qs hq hcq f) x = 0 := by
    rw [← heq]
    exact (densityCRTList qs hq hcq S).fourier_nonunit
  have hpR : (0 : ℝ) < ps.prod := by exact_mod_cast prime_list_prod_pos ps hp
  have hqR : (0 : ℝ) < qs.prod := by exact_mod_cast prime_list_prod_pos qs hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let W' := unitQuadraticSupport W a
  let V' := unitQuadraticSupport V b
  have hW' (w : ℕ) (hw : w ∈ W') :
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * ps.prod / ((N : ℝ) * v) :=
    hW w (((mem_unitQuadraticSupport W a w).mp hw).1)
  have hV' (w : ℕ) (hw : w ∈ V') :
      0 < w ∧ (w : ℝ) ^ 2 ≤ C * R * qs.prod / ((N : ℝ) * v) :=
    hV w (((mem_unitQuadraticSupport V b w).mp hw).1)
  have hwp (s : ℕ) := quadraticDensitySum_eq_unit_waves
    (densityFourier (primeCRTFunction ps hp hcp f)) hgp W a θ Φ R v s
      (fun w hw => (hW w hw).1) hR hv
  have hwq (s : ℕ) := quadraticDensitySum_eq_unit_waves
    (densityFourier (primeCRTFunction qs hq hcq f)) hgq V b η Ψ R v s
      (fun w hw => (hV w hw).1) hR hv
  rw [hep, heq]
  change ‖∑ n ∈ Finset.range N,
    quadraticDensitySum (densityFourier (primeCRTFunction ps hp hcp f)) W a θ Φ R v (n + M) *
    conj (quadraticDensitySum (densityFourier (primeCRTFunction qs hq hcq f)) V b η Ψ R v (n + M)) /
      ((n + M : ℕ) : ℂ)‖ ≤ _
  simp_rw [hwp, hwq]
  apply truncated_quadratic_correlation_bound ps qs rs hp hq hr hcp hcq hcr hrs f hfnorm
    W' V' (quadraticUnitScalar a) (quadraticUnitScalar b) Φ Ψ
    (fun w => θ * v * (w : ℝ) ^ 2 / ps.prod) (fun w => R * ps.prod / (v * (w : ℝ) ^ 2))
    (fun w => η * v * (w : ℝ) ^ 2 / qs.prod) (fun w => R * qs.prod / (v * (w : ℝ) ^ 2))
    R v C C C M N hR hv hC hC hM hN hperiod
  · intro w hw
    exact (quadratic_support_scale R ps.prod v N C w hR hpR hv hNR (hW' w hw).1 (hW' w hw).2).1
  · intro w hw
    exact (quadratic_support_scale R qs.prod v N C w hR hqR hv hNR (hV' w hw).1 (hV' w hw).2).1
  · intro w hw
    exact (quadratic_support_scale R ps.prod v N C w hR hpR hv hNR (hW' w hw).1 (hW' w hw).2).2
  · intro w hw
    exact (quadratic_support_scale R qs.prod v N C w hR hqR hv hNR (hV' w hw).1 (hV' w hw).2).2
  · exact quadratic_support_pair_count W' V' R ps.prod qs.prod v N C hR hpR hv hNR hC hW' hV'

end Ostmann

end OAI
