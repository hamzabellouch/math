import OAI.NumberTheory.DirichletL.Descent.HybridReduction
import OAI.NumberTheory.DirichletL.Descent.Quotients

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_original_quotient_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L A H : ℝ,
      1 ≤ K → 1 ≤ X → 1 ≤ N → 1 ≤ A → 1 ≤ H →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (cset : Ideal Eis → Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧
        L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
      (∀ p ∈ pairs, p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1,
        c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta (r * c) p.1 p.2‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
          (∑ p ∈ pairs, quadraticRow k (primaryGenerator (p.1 * p.2)) *
            (∑ c ∈ cset p.1, hybridColumnCoefficient R r beta c p.1 p.2 *
              (∑ P ∈ quotientSupport R Pset,
                hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, hblock⟩ := hybrid_fixed_block_sieve_norm ε hε
  refine ⟨C * (128 * 128 * 256), by positivity, ?_⟩
  intro K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset pairs cset a beta
    hrows hn hP ha hpairs hhs hcs hbeta
  let Hset := pairs.image Prod.snd
  let mc := (pairs.image Prod.fst).biUnion fun m => (cset m).image fun c => (m, c)
  have hRr : R * r ≠ 0 := mul_ne_zero hR hr
  have hn0 : ∀ n ∈ nset, n ≠ 0 := fun n hn' => (hn n hn').1.1.ne_zero
  have hP0 : ∀ P ∈ Pset, P ≠ 0 := fun P hP' => (hP P hP').1.1.ne_zero
  have hHcount : (Hset.card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real Hset H hH
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).1
    · intro h hh
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hh
      exact (hhs p hp).2
  have hcCount : ∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ 128 * A := by
    intro p hp
    exact DescentFiberCost.finite_ideal_count_real (cset p.1) A hA
      (fun c hc => (hcs p hp c hc).1) (fun c hc => (hcs p hp c hc).2.1)
  have hmc : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc := by
    intro p hp c hc
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  have hmap : ∀ u ∈ mc, u.2 * (1 * u.1) ∈ quotientSupport r nset := by
    intro u hu
    obtain ⟨m, hm, cu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp cu
    apply (mem_quotientSupport r (c * (1 * p.1)) hr nset).mpr
    simpa only [one_mul, mul_assoc] using (hcs p hp c hc).2.2
  have he := hblock K X N (2 * L) hK hX hN
    (quotientSupport (R * r) rows) pairs mc Hset (quotientSupport r nset)
    (quotientSupport R Pset)
    (fun k hk => ⟨quotientSupport_quadratic_admissible (R * r) hRr rows
        (fun k hk => (hrows k hk).1) k hk,
      quotientSupport_norm_le (R * r) hRr rows K
        (fun k hk => (hrows k hk).1.1) (fun k hk => (hrows k hk).2) k hk⟩)
    hpairs 1 1 cset (fun h => hybridCubicCoefficient R r h t a)
    (hybridColumnCoefficient R r beta) (128 * A) 256 (by positivity) hcCount
    (fun p hp c hc => hybridColumnCoefficient_norm_le_one R r c p.1 p.2 beta (hbeta p hp c hc))
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩) hmc hmap
    (fun J hJ => ⟨quotientSupport_cubic_admissible r hr nset (fun n hn' => (hn n hn').1) J hJ,
      quotientSupport_norm_le r hr nset N hn0 (fun n hn' => (hn n hn').2) J hJ⟩)
    (fun P hP' => ⟨quotientSupport_cubic_admissible R hR Pset (fun P hP' => (hP P hP').1) P hP',
      quotientSupport_norm_le R hR Pset (2 * L) hP0 (fun P hP' => (hP P hP').2.2) P hP'⟩)
    (fun h _ => quotient_hybridCubicCoefficient_energy R r h t hR Pset L hP0
      (fun P hP' => (hP P hP').2) a ha)
  simp only [one_mul] at he
  have hsqrt : ‖(Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (Ideal.absNorm R : ℝ)⁻¹ := by
    rw [norm_inv, inv_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp_rw [norm_mul, mul_pow, hsqrt]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Nat.cast_nonneg _))).trans
  calc
    _ ≤ (Ideal.absNorm R : ℝ)⁻¹ *
      (C * (K * X * N) ^ ε * (K + X) * (128 * A) * (128 * H) *
        CubicSieve.sieveNorm N (2 * L) * 256) := by
      gcongr
      exact sq_nonneg _
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
