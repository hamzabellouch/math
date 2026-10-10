import OAI.Analysis.OInfinity.TensorApproximation
import OAI.Analysis.OInfinity.VacuumCorner

namespace OAI

/-! # Simplicity of O∞ from finite vacuum corners

A nonzero Fock coefficient becomes a nonzero vacuum coefficient after a word
sandwich.  Compressing a polynomial by an unused generator gives exactly that
vacuum coefficient times the unit.  Polynomial approximation therefore puts an
invertible element in every nonzero two-sided ideal.
-/

noncomputable section
open scoped CStarAlgebra InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

local instance : SMulWithZero ℂ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℂ OInfinity _ _
    (@Module.toMulActionWithZero ℂ OInfinity _ _ inferInstance)
local instance : DistribSMul ℂ OInfinity :=
  @DistribMulAction.toDistribSMul ℂ OInfinity _ _
    (@Module.toDistribMulAction ℂ OInfinity _ _ inferInstance)

private lemma norm_complex_smul_one {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (c : ℂ) : ‖c • (1 : A)‖ = ‖c‖ := by
  rw [norm_smul, norm_one, mul_one]

private lemma norm_contraction_sandwich {A : Type*} [NonUnitalCStarAlgebra A]
    (s a : A) (hs : ‖s‖ ≤ 1) : ‖star s * a * s‖ ≤ ‖a‖ := by
  have hleft : ‖star s * a‖ ≤ ‖s‖ * ‖a‖ := by
    simpa only [norm_star] using norm_mul_le (star s) a
  calc
    _ ≤ (‖s‖ * ‖a‖) * ‖s‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hleft (norm_nonneg _))
    _ ≤ (1 * ‖a‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) hs
      (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by rw [one_mul, mul_one]

def fockVacuumCoefficient (a : OInfinity) : ℂ :=
  inner ℂ fockVacuum (fockOperatorRepresentation a fockVacuum)

lemma fockVacuumCoefficient_sub (a b : OInfinity) :
    fockVacuumCoefficient (a - b) = fockVacuumCoefficient a - fockVacuumCoefficient b := by
  simp only [fockVacuumCoefficient, map_sub, sub_apply, inner_sub_right]

lemma fockVacuumCoefficient_norm_le (a : OInfinity) : ‖fockVacuumCoefficient a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖fockVacuum‖ * ‖fockOperatorRepresentation a fockVacuum‖ := norm_inner_le_norm _ _
    _ ≤ ‖fockVacuum‖ * (‖fockOperatorRepresentation a‖ * ‖fockVacuum‖) :=
      mul_le_mul_of_nonneg_left ((fockOperatorRepresentation a).le_opNorm _) (norm_nonneg _)
    _ ≤ ‖fockVacuum‖ * (‖a‖ * ‖fockVacuum‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le fockOperatorRepresentation.toNonUnitalStarAlgHom a
    _ = ‖a‖ := by rw [fockVacuum_norm, one_mul, mul_one]

lemma finiteFockAlgebraWord_fock {N m : ℕ} (i : FiniteFockIndex N m) :
    fockOperatorRepresentation (finiteFockAlgebraWord i) fockVacuum = finiteFockVector i :=
  oInfinityPositiveWord_fock N i.1.val i.2

lemma fockVacuumCoefficient_word_sandwich {N m : ℕ} (a : OInfinity)
    (i j : FiniteFockIndex N m) :
    fockVacuumCoefficient (star (finiteFockAlgebraWord i) * a * finiteFockAlgebraWord j) =
      oInfinityFockCompression N m a i j := by
  unfold fockVacuumCoefficient
  rw [map_mul, map_mul, map_star]
  change inner ℂ fockVacuum
    ((fockOperatorRepresentation (finiteFockAlgebraWord i)).adjoint
      (fockOperatorRepresentation a
        (fockOperatorRepresentation (finiteFockAlgebraWord j) fockVacuum))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, finiteFockAlgebraWord_fock,
    finiteFockAlgebraWord_fock, oInfinityFockCompression_apply]

lemma exists_fock_coefficient_ne_zero {a : OInfinity} (ha : a ≠ 0) :
    ∃ n : ℕ, ∃ i j : FiniteFockIndex n (n + 1),
      oInfinityFockCompression n (n + 1) a i j ≠ 0 := by
  by_contra! h
  have hc (n : ℕ) : oInfinityFockCompression n (n + 1) a = 0 := by
    ext i j
    exact h n i j
  have happ (n : ℕ) : oInfinityApproximationSequence n a = 0 := by
    change oInfinityFockReturn n (n + 1) (oInfinityFockCompression n (n + 1) a) = 0
    rw [hc, map_zero]
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp (oInfinityApproximationSequence_tendsto a)
  simp only [happ, zero_sub, norm_neg] at ht
  have hn : ‖a‖ = 0 := tendsto_nhds_unique tendsto_const_nhds ht
  exact ha (norm_eq_zero.mp hn)

lemma unusedGenerator_polynomial (c : List (ℕ × Bool) →₀ ℂ) {N : ℕ}
    (hc : ∀ w ∈ c.support, ∀ p ∈ w, p.1 < N) :
    star (oInfinityIsometry N) * cuntzPolynomial oInfinityIsometry c * oInfinityIsometry N =
      fockVacuumCoefficient (cuntzPolynomial oInfinityIsometry c) • 1 := by
  let i : FiniteFockIndex N 0 := ⟨0, fun j => Fin.elim0 j⟩
  have hw : finiteVacuumCorner N 0 i = oInfinityIsometry N := by
    change oInfinityPositiveWord N (fun j : Fin 0 => Fin.elim0 j) * oInfinityIsometry N = _
    rw [oInfinityPositiveWord_zero, one_mul]
  have hv : finiteFockVector i = fockVacuum := rfl
  have h := finiteVacuumCorner_polynomial c hc i i
  rw [hw, oInfinityFockCompression_apply, hv] at h
  exact h

lemma oInfinityIsometry_norm_le_one (N : ℕ) : ‖oInfinityIsometry N‖ ≤ 1 := by
  have h := congrArg norm (oInfinityIsometry_relations N N)
  simp only [ite_true, CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (oInfinityIsometry N), cstar_norm_one_le_one (A := OInfinity)]

lemma unusedGenerator_error (a : OInfinity) (c : List (ℕ × Bool) →₀ ℂ) {N : ℕ}
    (hc : ∀ w ∈ c.support, ∀ p ∈ w, p.1 < N) :
    ‖star (oInfinityIsometry N) * a * oInfinityIsometry N - fockVacuumCoefficient a • 1‖ ≤
      2 * ‖a - cuntzPolynomial oInfinityIsometry c‖ := by
  let p := cuntzPolynomial oInfinityIsometry c
  let s := oInfinityIsometry N
  have hs : ‖s‖ ≤ 1 := oInfinityIsometry_norm_le_one N
  have he : star s * a * s - fockVacuumCoefficient a • 1 =
      star s * (a - p) * s + (fockVacuumCoefficient p - fockVacuumCoefficient a) • 1 := by
    dsimp [s, p]
    rw [mul_sub, sub_mul, unusedGenerator_polynomial c hc, sub_smul]
    abel
  have hfirst : ‖star s * (a - p) * s‖ ≤ ‖a - p‖ :=
    norm_contraction_sandwich s (a - p) hs
  have hsecond : ‖(fockVacuumCoefficient p - fockVacuumCoefficient a) • (1 : OInfinity)‖ ≤
      ‖a - p‖ := by
    calc
      _ = ‖fockVacuumCoefficient p - fockVacuumCoefficient a‖ := norm_complex_smul_one _
      _ = ‖fockVacuumCoefficient (p - a)‖ :=
        congrArg norm (fockVacuumCoefficient_sub p a).symm
      _ ≤ ‖p - a‖ := fockVacuumCoefficient_norm_le _
      _ = ‖a - p‖ := norm_sub_rev _ _
  exact (congrArg norm he).trans_le
    ((norm_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring)))

lemma twoSidedIdeal_eq_top_of_vacuumCoefficient_ne_zero (I : TwoSidedIdeal OInfinity)
    {a : OInfinity} (ha : a ∈ I) (hv : fockVacuumCoefficient a ≠ 0) : I = ⊤ := by
  let coeff := fockVacuumCoefficient a
  have hcoeff : 0 < ‖coeff‖ := norm_pos_iff.mpr hv
  obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp oInfinityPolynomial_denseRange a
    (‖coeff‖ / 4) (by positivity)
  have hac : ‖a - cuntzPolynomial oInfinityIsometry c‖ < ‖coeff‖ / 4 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hc
  obtain ⟨N, hN⟩ := exists_polynomial_alphabet_bound c
  let z := star (oInfinityIsometry N) * a * oInfinityIsometry N
  have hz : z ∈ I := I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)
  have he : ‖z - coeff • 1‖ < ‖coeff‖ := by
    exact (unusedGenerator_error a c hN).trans_lt (by dsimp [coeff] at *; linarith)
  let y := coeff⁻¹ • z
  have hy : y ∈ I := by
    change coeff⁻¹ • z ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ _ hz
  have hsmall : ‖1 - y‖ < 1 := by
    have hid : (1 : OInfinity) - y = coeff⁻¹ • (coeff • 1 - z) := by
      dsimp [y]
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hv, one_smul]
    rw [hid, norm_smul, norm_inv, norm_sub_rev]
    exact (inv_mul_lt_one₀ hcoeff).mpr he
  have hu : IsUnit y := by
    simpa only [Units.val_oneSub, sub_sub_cancel] using (Units.oneSub (1 - y) hsmall).isUnit
  obtain ⟨u, hu⟩ := hu
  have hone := I.mul_mem_left (↑u⁻¹) y hy
  rw [← hu, Units.inv_mul] at hone
  exact I.eq_top hone

/-- Every nonzero two-sided ideal of O∞ contains a unit. -/
theorem oInfinity_twoSidedIdeal_trivial (I : TwoSidedIdeal OInfinity) : I = ⊥ ∨ I = ⊤ := by
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ a : OInfinity, a ∈ I ∧ a ≠ 0 := by
    by_contra! h
    apply hI
    ext a
    change (a ∈ I ↔ a = 0)
    exact ⟨h a, fun he => by subst a; exact I.zero_mem⟩
  obtain ⟨a, ha, ha0⟩ := hex
  obtain ⟨n, i, j, hij⟩ := exists_fock_coefficient_ne_zero ha0
  let b := star (finiteFockAlgebraWord i) * a * finiteFockAlgebraWord j
  have hb : b ∈ I := I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)
  apply twoSidedIdeal_eq_top_of_vacuumCoefficient_ne_zero I hb
  simpa only [b, fockVacuumCoefficient_word_sandwich] using hij

theorem oInfinity_topologicallySimple : Pureness.TopologicallySimple OInfinity := by
  intro I _
  exact oInfinity_twoSidedIdeal_trivial I

end WeakPureInfiniteness

end

end OAI
