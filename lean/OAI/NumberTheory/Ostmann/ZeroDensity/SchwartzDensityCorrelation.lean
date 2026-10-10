import OAI.NumberTheory.Ostmann.Arithmetic.PeriodicIntervalPhase
import OAI.NumberTheory.Ostmann.Characters.CorrelationWeightVariation

namespace OAI

/-! # The single expanded pair in the large-kernel correlation -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap

noncomputable def correlationWeightBudget (Φ Ψ : 𝓢(ℝ, ℂ)) (C D : ℝ) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 Φ *
    (SchwartzMap.seminorm ℝ 0 0 Ψ + SchwartzMap.seminorm ℝ 0 1 Ψ * D) +
  SchwartzMap.seminorm ℝ 0 0 Ψ *
    (SchwartzMap.seminorm ℝ 0 0 Φ + SchwartzMap.seminorm ℝ 0 1 Φ * C)

/-- Each expanded pair is bounded by its exact exclusive-prime factor times
the interval length and a fixed Schwartz seminorm budget. -/
theorem schwartz_density_correlation_bound (ps qs rs : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hq : ∀ p ∈ qs, p.Prime) (hr : ∀ p ∈ rs, p.Prime)
    (hcp : ps.Pairwise Nat.Coprime) (hcq : qs.Pairwise Nat.Coprime) (hcr : rs.Pairwise Nat.Coprime)
    (hrs : rs.toFinset = ps.toFinset ∪ qs.toFinset)
    (vp : (ZMod ps.prod)ˣ) (vq : (ZMod qs.prod)ˣ)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ rs, ∀ x, ‖f p x‖ ≤ 1)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (α β Y Z C D : ℝ) (M N : ℕ)
    (hY : 0 < Y) (hZ : 0 < Z) (hNY : (N : ℝ) ≤ C * Y) (hNZ : (N : ℝ) ≤ D * Z)
    (hN : rs.prod ^ 2 ≤ N) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
    ‖∑ n ∈ Finset.range N,
      (Φ (((n + M : ℕ) : ℝ) / Y) *
        densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n + M : ℕ)) *
          realAdditivePhase α ^ (n + M)) *
      conj (Ψ (((n + M : ℕ) : ℝ) / Z) *
        densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n + M : ℕ)) *
          realAdditivePhase β ^ (n + M))‖ ≤
      correlationWeightBudget Φ Ψ C D *
        (4 * (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod * N) := by
  intro _ _
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  let : NeZero qs.prod := ⟨(prime_list_prod_pos qs hq).ne'⟩
  let : NeZero rs.prod := ⟨(prime_list_prod_pos rs hr).ne'⟩
  obtain ⟨F, hF, hbound⟩ := original_density_correlation_model ps qs rs hp hq hr hcp hcq hcr hrs vp vq f hf
  let w : ℕ → ℂ := fun n => Φ (((n + M : ℕ) : ℝ) / Y) * conj (Ψ (((n + M : ℕ) : ℝ) / Z))
  have he (n : ℕ) : densityFourier (primeCRTFunction ps hp hcp f)
      ((vp : ZMod ps.prod) * (n + M : ℕ)) *
      conj (densityFourier (primeCRTFunction qs hq hcq f)
        ((vq : ZMod qs.prod) * (n + M : ℕ))) = F (n + M : ℕ) := by
    simpa only [Int.cast_natCast] using hF ((n + M : ℕ) : ℤ)
  have hphase (n : ℕ) : realAdditivePhase α ^ n * conj (realAdditivePhase β ^ n) =
      realAdditivePhase (α - β) ^ n := by
    rw [realAdditivePhase_sub, mul_pow, map_pow]
  have hsum : (∑ n ∈ Finset.range N,
      (Φ (((n + M : ℕ) : ℝ) / Y) *
        densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n + M : ℕ)) *
          realAdditivePhase α ^ (n + M)) *
      conj (Ψ (((n + M : ℕ) : ℝ) / Z) *
        densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n + M : ℕ)) *
          realAdditivePhase β ^ (n + M))) =
      ∑ n ∈ Finset.range N, w n * (F (n + M : ℕ) * realAdditivePhase (α - β) ^ (n + M)) := by
    apply Finset.sum_congr rfl
    intro n hn
    calc
      _ = w n * (densityFourier (primeCRTFunction ps hp hcp f) ((vp : ZMod ps.prod) * (n + M : ℕ)) *
        conj (densityFourier (primeCRTFunction qs hq hcq f) ((vq : ZMod qs.prod) * (n + M : ℕ)))) *
        (realAdditivePhase α ^ (n + M) * conj (realAdditivePhase β ^ (n + M))) := by
          simp only [w, map_mul]
          ring
      _ = _ := by rw [he, hphase]; ring
  have hA : 0 ≤ (rs.map (correlationPrimeBound (supportCorrelationSide ps.toFinset qs.toFinset))).prod := by
    apply List.prod_nonneg
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact correlationPrimeBound_nonneg _ p
  have hvar : discreteVariation w N ≤ correlationWeightBudget Φ Ψ C D := by
    simpa only [w, correlationWeightBudget, Nat.cast_add] using
      schwartz_correlation_variation Φ Ψ M M Y Z C D N hY hZ hNY hNZ
  rw [hsum]
  exact (weighted_periodic_linear_shift_long_bound rs.prod F _ (α - β) hA hbound w M N hN).trans
    (mul_le_mul_of_nonneg_right hvar (by positivity))

end Ostmann

end OAI
