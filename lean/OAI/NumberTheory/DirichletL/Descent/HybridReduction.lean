import OAI.NumberTheory.DirichletL.Descent.Quadratic
import OAI.NumberTheory.DirichletL.Descent.Hybrid

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem finite_inverse_cubic_energy
    (Jset Pset : Finset (Ideal Eis)) (N L : ℝ)
    (hJ : ∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N)
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L)
    (a : Ideal Eis → ℂ) :
    (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
      CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  let A : Matrix Jset Pset ℂ := fun J P => CubicSieve.idealKernel P.val J.val
  have hnorm : CubicSieve.squaredNorm (fun J P => star (A J P)) =
      CubicSieve.squaredNorm A :=
    congrArg (fun z : ℝ => z ^ 2) (CubicSieve.operator_conjugate_norm A)
  have hfamily : CubicSieve.squaredNorm A ≤ CubicSieve.sieveNorm N L :=
    CubicSieve.family_squared_norm_le
      (fun J : Jset => J.val) (fun P : Pset => P.val)
      Subtype.val_injective Subtype.val_injective N L
      (fun J => hJ J.val J.property) (fun P => hP P.val P.property)
  have he := CubicSieve.energy_le_squaredNorm (fun J P => star (A J P)) (fun P => a P.val)
  rw [hnorm] at he
  have he' := he.trans (mul_le_mul_of_nonneg_right hfamily
    (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hinner (J : Jset) :
      (∑ P : Pset, star (A J P) * a P.val) =
        ∑ P ∈ Pset, a P * inverseCubicKernel P J.val := by
    simp only [A, inverseCubicKernel, CubicSieve.idealKernel, mul_comm]
    exact Finset.sum_coe_sort Pset
      (fun P => a P * star (ConcreteTraceCRT.eisEmbedding
        (CubicJacobiGlobal.idealSymbol P (primaryGenerator J.val))))
  simp_rw [hinner] at he'
  rw [Finset.sum_coe_sort Jset
    (fun J => ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2),
    Finset.sum_coe_sort Pset (fun P => ‖a P‖ ^ 2)] at he'
  exact he'

theorem hybrid_quadratic_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (Pset : Finset (Ideal Eis)) (coef : Ideal Eis → Ideal Eis → ℂ)
      (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (Cbound : ℝ),
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * Cbound *
        ∑ p ∈ pairs, ∑ c ∈ cset p.1,
          ‖∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))‖ ^ 2 := by
  obtain ⟨C, hC, hquadratic⟩ := quadratic_squarefree_product_energy_fixed_factor ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta Cbound hcount hbeta
  let F (p : Ideal Eis × Ideal Eis) (c : Ideal Eis) :=
    ∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))
  have he := hquadratic K X hK hX rows pairs hrows hpairs B
    (fun p => ∑ c ∈ cset p.1, beta c p.1 p.2 * F p c)
  apply he.trans
  have hlocal (p : Ideal Eis × Ideal Eis) (hp : p ∈ pairs) :
      ‖∑ c ∈ cset p.1, beta c p.1 p.2 * F p c‖ ^ 2 ≤
        Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
    exact (bounded_finset_coefficient_sum_sq (cset p.1)
      (fun c => beta c p.1 p.2) (F p) (hbeta p hp)).trans
        (mul_le_mul_of_nonneg_right (hcount p hp) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  calc
    _ ≤ C * (K * X) ^ ε * (K + X) *
        ∑ p ∈ pairs, Cbound * ∑ c ∈ cset p.1, ‖F p c‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
      positivity
    _ = _ := by rw [← Finset.mul_sum]; simp only [F]; ring

theorem cubic_product_row_bound_of_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis) (S : ℝ),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ a : Ideal Eis → ℂ,
        (∑ J ∈ Jset, ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2) ≤
          S * ∑ P ∈ Pset, ‖a P‖ ^ 2) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * S * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro N hN pairs Jset Pset mBad S hmap hJset hcubic a
  let E (J : Ideal Eis) := ‖∑ P ∈ Pset, a P * inverseCubicKernel P J‖ ^ 2
  have hfiber (J : Ideal Eis) (hJ : J ∈ Jset) :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤ D * N ^ ε := by
    have hJ0 := (hJset J hJ).1.1.ne_zero
    have hc : ((pairs.filter (fun p => p.2 * (mBad * p.1) = J)).card : ℝ) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ) :=
      Nat.cast_le.mpr (scaled_product_fiber_card pairs mBad J hJ0)
    have hd := (hdiv J hJ0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hJset J hJ).2 hε.le) hD.le)
    exact (by simpa using hc :
      (∑ _p ∈ pairs with _p.2 * (mBad * _p.1) = J, (1 : ℝ)) ≤
        ((IdealMobiusDivisorSum.idealDivisors J).card : ℝ)).trans hd
  have hf := fiber_energy_bound pairs Jset (fun p => p.2 * (mBad * p.1))
    (fun _ => 1) (fun _ => D * N ^ ε) E hmap (fun _ _ => sq_nonneg _) hfiber
  simp only [one_mul, ← Finset.mul_sum] at hf
  apply hf.trans
  calc
    _ ≤ (D * N ^ ε) * (S * ∑ P ∈ Pset, ‖a P‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (hcubic a) (by positivity)
    _ = _ := by ring

theorem cubic_product_row_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ N L : ℝ, 1 ≤ N →
    ∀ (pairs : Finset (Ideal Eis × Ideal Eis)) (Jset Pset : Finset (Ideal Eis))
      (mBad : Ideal Eis),
      (∀ p ∈ pairs, p.2 * (mBad * p.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      ∀ a : Ideal Eis → ℂ,
        (∑ p ∈ pairs, ‖∑ P ∈ Pset,
          a P * inverseCubicKernel P (p.2 * (mBad * p.1))‖ ^ 2) ≤
          D * N ^ ε * CubicSieve.sieveNorm N L * ∑ P ∈ Pset, ‖a P‖ ^ 2 := by
  obtain ⟨D, hD, hb⟩ := cubic_product_row_bound_of_sieve ε hε
  refine ⟨D, hD, ?_⟩
  intro N L hN pairs Jset Pset mBad hmap hJ hP a
  exact hb N hN pairs Jset Pset mBad (CubicSieve.sieveNorm N L) hmap hJ
    (finite_inverse_cubic_energy Jset Pset N L hJ hP) a

theorem hybrid_fixed_block_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X N L : ℝ, 1 ≤ K → 1 ≤ X → 1 ≤ N →
    ∀ (rows : Finset (Ideal Eis)) (pairs cubicPairs : Finset (Ideal Eis × Ideal Eis))
      (Hset Jset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B mBad : Ideal Eis) (cset : Ideal Eis → Finset (Ideal Eis))
      (coef : Ideal Eis → Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
      (Cbound Ebound : ℝ), 0 ≤ Cbound →
      (∀ p ∈ pairs, ((cset p.1).card : ℝ) ≤ Cbound) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, ‖beta c p.1 p.2‖ ≤ 1) →
      (∀ p ∈ pairs, p.2 ∈ Hset) →
      (∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ cubicPairs) →
      (∀ u ∈ cubicPairs, u.2 * (mBad * u.1) ∈ Jset) →
      (∀ J ∈ Jset, CubicSieve.Admissible J ∧ (Ideal.absNorm J : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ (Ideal.absNorm P : ℝ) ≤ L) →
      (∀ h ∈ Hset, (∑ P ∈ Pset, ‖coef h P‖ ^ 2) ≤ Ebound) →
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        quadraticRow k (primaryGenerator (B * (p.1 * p.2))) *
          (∑ c ∈ cset p.1, beta c p.1 p.2 *
            (∑ P ∈ Pset, coef p.2 P * inverseCubicKernel P (c * (mBad * p.1))))‖ ^ 2) ≤
      C * (K * X * N) ^ ε * (K + X) * Cbound * (Hset.card : ℝ) *
        CubicSieve.sieveNorm N L * Ebound := by
  obtain ⟨Cq, hCq, hquad⟩ := hybrid_quadratic_reduction ε hε
  obtain ⟨D, hD, hcube⟩ := cubic_product_row_sieve_norm ε hε
  refine ⟨Cq * D, mul_pos hCq hD, ?_⟩
  intro K X N L hK hX hN rows pairs cubicPairs Hset Jset Pset hrows hpairs
    B mBad cset coef beta Cbound Ebound hCbound hcount hbeta hH hmc hmap hJ hP hcoef
  let E (h m c : Ideal Eis) := ‖∑ P ∈ Pset,
    coef h P * inverseCubicKernel P (c * (mBad * m))‖ ^ 2
  have hnorm : 0 ≤ CubicSieve.sieveNorm N L := sq_nonneg _
  have he := hquad K X hK hX rows pairs hrows hpairs B mBad cset Pset coef beta
    Cbound hcount hbeta
  have hpos := positive_triple_enlarge pairs cset Hset cubicPairs E hH hmc
    (fun _ _ _ => sq_nonneg _)
  have htotal : (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      (Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound) := by
    apply hpos.trans
    calc
      _ ≤ ∑ _h ∈ Hset, D * N ^ ε * CubicSieve.sieveNorm N L * Ebound := by
        apply Finset.sum_le_sum
        intro h hh
        apply (hcube N L hN cubicPairs Jset Pset mBad hmap hJ hP (coef h)).trans
        exact mul_le_mul_of_nonneg_left (hcoef h hh)
          (mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)) hnorm)
      _ = _ := by simp
  apply he.trans
  calc
    _ ≤ (Cq * (K * X) ^ ε * (K + X) * Cbound) *
        ((Hset.card : ℝ) * (D * N ^ ε * CubicSieve.sieveNorm N L * Ebound)) := by
      apply mul_le_mul_of_nonneg_left htotal
      positivity
    _ = _ := by
      rw [Real.mul_rpow (show 0 ≤ K * X by positivity) (show 0 ≤ N by linarith)]
      ring

end
end SevenEighths.InverseMoment

end OAI
