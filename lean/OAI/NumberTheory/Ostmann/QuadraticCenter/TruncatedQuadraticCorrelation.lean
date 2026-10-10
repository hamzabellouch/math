import OAI.NumberTheory.Ostmann.ZeroDensity.SchwartzDensityCorrelation
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrelationExpansion

namespace OAI

/-! # The complete finite correlation bound after quadratic normalization -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def densityWave {q : ℕ} [NeZero q] (g : ZMod q → ℂ) (u : (ZMod q)ˣ)
    (Φ : 𝓢(ℝ, ℂ)) (α Y : ℝ) (n : ℕ) : ℂ :=
  Φ ((n : ℝ) / Y) * g ((u : ZMod q) * (n : ZMod q)) * realAdditivePhase α ^ n

noncomputable def normalizedDensityWaveSum {q : ℕ} [NeZero q] {ι : Type*}
    (g : ZMod q → ℂ) (W : Finset ι) (u : ι → (ZMod q)ˣ) (Φ : 𝓢(ℝ, ℂ))
    (α Y : ι → ℝ) (R v : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt (R * q / ((n : ℝ) * v)) : ℝ) : ℂ)⁻¹ *
    ∑ w ∈ W, densityWave g (u w) Φ (α w) (Y w) n

/-- The normalized large-kernel correlation estimate, with the finite support
pair count and the two smooth scaling bounds made explicit. -/
theorem truncated_quadratic_correlation_bound {ι κ : Type*}
    (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1)
    (W : Finset ι) (V : Finset κ) (u : ι → (ZMod ps.prod)ˣ) (v' : κ → (ZMod qs.prod)ˣ)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (α Y : ι → ℝ) (β Z : κ → ℝ)
    (R v C D H : ℝ) (M N : ℕ) (hR : 0 < R) (hv : 0 < v)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hM : 0 < M) (hN : 0 < N)
    (hperiod : rs.prod ^ 2 ≤ N)
    (hY : ∀ w ∈ W, 0 < Y w) (hZ : ∀ z ∈ V, 0 < Z z)
    (hNY : ∀ w ∈ W, (N : ℝ) ≤ C * Y w) (hNZ : ∀ z ∈ V, (N : ℝ) ≤ D * Z z)
    (hcount : (W.card : ℝ) * V.card ≤
      H * R * Real.sqrt ((ps.prod : ℝ) * qs.prod) / ((N : ℝ) * v)) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N,
      normalizedDensityWaveSum (densityFourier (primeCRTFunction ps hp hcp f)) W u Φ α Y R v (n + M) *
      conj (normalizedDensityWaveSum (densityFourier (primeCRTFunction qs hq hcq f)) V v' Ψ β Z R v (n + M)) /
        ((n + M : ℕ) : ℂ)‖ ≤
      H * (4 * correlationWeightBudget Φ Ψ C D) *
        (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod := by
  intro _ _
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let A := (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod
  let B := correlationWeightBudget Φ Ψ C D
  have hA : 0 ≤ A := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact correlationPrimeBound_nonneg _ p
  have hB : 0 ≤ B := by
    have hΦ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := (norm_nonneg _).trans (Φ.norm_le_seminorm ℝ 0)
    have hΨ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Ψ := (norm_nonneg _).trans (Ψ.norm_le_seminorm ℝ 0)
    have hΦ1 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Φ :=
      (norm_nonneg _).trans (Φ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
    have hΨ1 : 0 ≤ SchwartzMap.seminorm ℝ 0 1 Ψ :=
      (norm_nonneg _).trans (Ψ.norm_iteratedFDeriv_le_seminorm ℝ 1 0)
    dsimp [B, correlationWeightBudget]
    positivity
  have hpR : (0 : ℝ) < ps.prod := by exact_mod_cast prime_list_prod_pos ps hp
  have hqR : (0 : ℝ) < qs.prod := by exact_mod_cast prime_list_prod_pos qs hq
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpair (w : ι) (hw : w ∈ W) (z : κ) (hz : z ∈ V) :
      ‖∑ n ∈ Finset.range N,
        densityWave (densityFourier (primeCRTFunction ps hp hcp f)) (u w) Φ (α w) (Y w) (n + M) *
        conj (densityWave (densityFourier (primeCRTFunction qs hq hcq f)) (v' z) Ψ (β z) (Z z) (n + M))‖ ≤
          B * (4 * A * N) := by
    exact schwartz_density_correlation_bound ps qs rs hp hq hr hcp hcq hcr hrs (u w) (v' z) f hf
      Φ Ψ (α w) (β z) (Y w) (Z z) C D M N (hY w hw) (hZ z hz) (hNY w hw) (hNZ z hz) hperiod
  have hnorm := normalized_quadratic_pair_bound (Finset.range N) W V
    (fun n => ((n + M : ℕ) : ℝ))
    (fun w n => densityWave (densityFourier (primeCRTFunction ps hp hcp f)) (u w) Φ (α w) (Y w) (n + M))
    (fun z n => densityWave (densityFourier (primeCRTFunction qs hq hcq f)) (v' z) Ψ (β z) (Z z) (n + M))
    R (ps.prod : ℝ) (qs.prod : ℝ) v (B * (4 * A * N)) hR hpR hqR hv
    (fun n _ => by exact_mod_cast (show 0 < n + M by omega)) hpair
  change _ ≤ H * (4 * B) * A
  apply hnorm.trans
  have hc := quadratic_pair_count_cancellation R (ps.prod : ℝ) (qs.prod : ℝ) v N (4 * B) A H
    hR hpR hqR hv hNR (by positivity) hA W.card V.card hcount
  convert hc using 1
  ring

end Ostmann

end OAI
