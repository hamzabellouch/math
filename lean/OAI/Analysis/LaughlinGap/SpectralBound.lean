import Mathlib
import OAI.Analysis.LaughlinGap.Basic

namespace OAI

/-! Spectral Bound. -/

noncomputable section


namespace LaughlinGap
open scoped BigOperators
namespace Chart
open MvPolynomial

noncomputable def splitPair {N : ℕ} (i j : Fin N) :
    MvPolynomial (Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N) (MvPolynomial Bool ℂ) :=
  aeval (fun k => if k = i then C (X false) else if k = j then C (X true) else X k)

@[simp] theorem splitPair_C {N : ℕ} (i j : Fin N) (c : ℂ) :
    splitPair i j (C c) = C (C c) := by
  simp [splitPair, algebraMap_eq]

@[simp] theorem splitPair_X {N : ℕ} (i j k : Fin N) :
    splitPair i j (X k) =
      if k = i then C (X false) else if k = j then C (X true) else X k := by
  simp [splitPair]

@[simp] theorem splitPair_difference {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    splitPair i j (difference i j) = C (difference false true) := by
  simp [difference, Ne.symm hij]

@[simp] theorem splitPair_rename {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (F : MvPolynomial Bool ℂ) :
    splitPair i j (rename (fun b : Bool => if b then j else i) F) = C F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add a b ha hb => simp [ha, hb]
  | mul_X p k hp => cases k <;> simp [hp, Ne.symm hij]

lemma spectatorMonomial_eq {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : PairSpectators (Q := Q) i j) :
    spectatorMonomial i j a = monomial (exponent a.val) (tensorMonomialScale a.val : ℂ) := by
  have hnorm : monomial (exponent a.val) (tensorMonomialScale a.val : ℂ) =
      ∏ k : Fin N, C (Real.sqrt (Q.choose (a.val k).val : ℝ) : ℂ) * X k ^ (a.val k).val := by
    rw [monomial_as_prod]
    simp only [tensorMonomialScale, Complex.ofReal_prod, map_prod, Finset.prod_mul_distrib]
  rw [hnorm]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase i) _
    (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)]
  simp [a.property.1, a.property.2, spectatorMonomial]

lemma splitPair_spectatorMonomial {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : PairSpectators (Q := Q) i j) :
    splitPair i j (spectatorMonomial i j a) =
      monomial (exponent a.val) (C (tensorMonomialScale a.val : ℂ)) := by
  rw [spectatorMonomial_eq i j hij a, monomial_as_prod]
  simp only [map_mul, map_prod, map_pow, splitPair_C]
  rw [monomial_eq]
  rw [Finsupp.prod_fintype _ _ (by intro; simp)]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  by_cases hki : k = i
  · subst k; simp [exponent, a.property.1]
  by_cases hkj : k = j
  · subst k; simp [exponent, a.property.2]
  simp [exponent, hki, hkj]

theorem coeff_splitPair_statePolynomial {N Q : ℕ} (ψ : State N Q)
    (i j : Fin N) (hij : i ≠ j) (a : PairSpectators (Q := Q) i j) :
    (splitPair i j (statePolynomial ψ)).coeff (exponent a.val) =
      C (tensorMonomialScale a.val : ℂ) *
        localPairPolynomial (fun x y => ψ (Function.update (Function.update a.val i x) j y)) := by
  classical
  rw [statePolynomial_pair_decomposition ψ i j hij]
  simp only [map_sum, map_mul, splitPair_spectatorMonomial i j hij,
    splitPair_rename i j hij, coeff_sum]
  rw [Finset.sum_eq_single a]
  · rw [mul_comm, coeff_C_mul, coeff_monomial]
    simp [mul_comm]
  · intro b hb hba
    have hab : exponent b.val ≠ exponent a.val := by
      intro h
      exact hba (Subtype.ext ((exponent_injective N Q) h))
    rw [mul_comm, coeff_C_mul, coeff_monomial, ite_eq_right hab, mul_zero]
  · simp

theorem localPairPolynomial_cube_dvd_of_statePolynomial_cube_dvd {N Q : ℕ}
    (ψ : State N Q) (i j : Fin N) (hij : i ≠ j)
    (hdiv : difference i j ^ 3 ∣ statePolynomial ψ)
    (a : PairSpectators (Q := Q) i j) :
    difference false true ^ 3 ∣
      localPairPolynomial (fun x y => ψ (Function.update (Function.update a.val i x) j y)) := by
  obtain ⟨G, hG⟩ := hdiv
  have h := congrArg (fun F => (splitPair i j F).coeff (exponent a.val)) hG
  rw [coeff_splitPair_statePolynomial ψ i j hij a, map_mul, map_pow,
    splitPair_difference i j hij, ← map_pow, coeff_C_mul] at h
  have hd : difference false true ^ 3 ∣ C (tensorMonomialScale a.val : ℂ) *
      localPairPolynomial (fun x y => ψ (Function.update (Function.update a.val i x) j y)) :=
    ⟨_, h⟩
  exact (IsUnit.dvd_mul_left ((isUnit_iff_ne_zero.mpr
    (Complex.ofReal_ne_zero.mpr (tensorMonomialScale_pos a.val).ne')).map C)).mp hd

theorem diagonal_derivative_eq_zero_of_cube_dvd {σ : Type*} [DecidableEq σ]
    (i j k : σ) (F : MvPolynomial σ ℂ) (hdiv : difference i j ^ 3 ∣ F) :
    diagonal i j (pderiv k F) = 0 := by
  obtain ⟨G, rfl⟩ := hdiv
  simp

end Chart

section LocalKernelConverse
open MvPolynomial

@[simp] theorem pairMoment_zero {Q : ℕ} (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    pairMoment φ 0 = 0 := by
  unfold pairMoment
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  split_ifs with hxy
  · have hx0 : x.val = 0 := by omega
    have hy0 : y.val = 0 := by omega
    simp [hx0, hy0]
  · rfl

theorem coeff_localPairPolynomial_diagonal_difference_derivative {Q p : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ) (hp : p < 2 * Q) :
    (Chart.diagonal false true
      (pderiv false (localPairPolynomial φ) - pderiv true (localPairPolynomial φ))).coeff
        (Finsupp.single false p) =
      pairMoment φ (p + 1) := by
  classical
  rw [localPairPolynomial_diagonal_difference_derivative, Finset.sum_range_succ']
  simp only [pairMoment_zero, map_zero, zero_mul, add_zero, Nat.add_sub_cancel,
    C_mul_X_pow_eq_monomial, coeff_sum, coeff_monomial,
    (Finsupp.single_injective false).eq_iff]
  simp [hp]

theorem pair_contraction_eq_zero_of_cubic_divisibility {Q : ℕ}
    (φ : Fin (Q + 1) → Fin (Q + 1) → ℂ)
    (hdiv : Chart.difference false true ^ 3 ∣ localPairPolynomial φ)
    (p : ℕ) (hp : p < 2 * Q - 1) :
    ∑ x, ∑ y, (pairCoefficient Q p x y : ℂ) * φ x y = 0 := by
  have hf := Chart.diagonal_derivative_eq_zero_of_cube_dvd false true false _ hdiv
  have ht := Chart.diagonal_derivative_eq_zero_of_cube_dvd false true true _ hdiv
  have he := coeff_localPairPolynomial_diagonal_difference_derivative φ (by omega : p < 2 * Q)
  rw [map_sub, hf, ht, sub_self, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he
  rw [pair_contraction_eq_moment, ← he, mul_zero]

end LocalKernelConverse

theorem energy_zero_of_difference_cubes_dvd {N Q : ℕ} (ψ : State N Q)
    (hdiv : ∀ i j : Fin N, i < j → Chart.difference i j ^ 3 ∣ Chart.statePolynomial ψ) :
    energy ψ = 0 := by
  apply (energy_eq_zero_iff ψ).mpr
  intro i j hij p hp a
  let a' : Chart.PairSpectators (Q := Q) i j :=
    ⟨Function.update (Function.update a i 0) j 0, by simp [ne_of_lt hij]⟩
  have hd := Chart.localPairPolynomial_cube_dvd_of_statePolynomial_cube_dvd
    ψ i j (ne_of_lt hij) (hdiv i j hij) a'
  have hc := pair_contraction_eq_zero_of_cubic_divisibility _ hd p hp
  exact (pairAmplitude_anchor ψ i j p a).symm.trans hc

namespace Chart

theorem difference_cube_dvd_laughlinPolynomial {N : ℕ} (i j : Fin N) (hij : i < j) :
    difference i j ^ 3 ∣ laughlinPolynomial N := by
  classical
  have hj := Finset.dvd_prod_of_mem (fun k : Fin N => if i < k then difference i k ^ 3 else 1)
    (Finset.mem_univ j)
  rw [ite_eq_left hij] at hj
  exact hj.trans (Finset.dvd_prod_of_mem
    (fun k : Fin N => ∏ l : Fin N, if k < l then difference k l ^ 3 else 1)
    (Finset.mem_univ i))

end Chart

theorem energy_scalar_laughlin (N : ℕ) (c : ℂ) :
    energy (c • laughlinVector N (3 * (N - 1))) = 0 := by
  apply energy_zero_of_difference_cubes_dvd
  intro i j hij
  rw [Chart.statePolynomial_smul, Chart.statePolynomial_laughlinVector,
    MvPolynomial.smul_eq_C_mul]
  exact dvd_mul_of_dvd_right (Chart.difference_cube_dvd_laughlinPolynomial i j hij) _

@[simp] theorem energy_laughlin (N : ℕ) :
    energy (laughlinVector N (3 * (N - 1))) = 0 := by
  simpa only [one_smul] using energy_scalar_laughlin N 1

theorem energy_zero_iff_laughlin {N : ℕ} (hN : 2 ≤ N)
    (ψ : State N (3 * (N - 1))) (hψ : Antisymmetric ψ) :
    energy ψ = 0 ↔ ∃ c : ℂ, ψ = c • laughlinVector N (3 * (N - 1)) := by
  constructor
  · exact energy_zero_imp_laughlin hN ψ hψ
  · rintro ⟨c, rfl⟩
    exact energy_scalar_laughlin N c

theorem sectorHamiltonian_ker_eq_laughlin {N : ℕ} (hN : 2 ≤ N) :
    (sectorHamiltonian N (3 * (N - 1))).ker =
      Submodule.span ℂ {(
        ⟨toTensorHilbert (laughlinVector N (3 * (N - 1))),
          laughlinVector_antisymmetric N (3 * (N - 1))⟩ : SectorHilbert N (3 * (N - 1)))} := by
  ext ψ
  rw [LinearMap.mem_ker, sectorHamiltonian_eq_zero_iff, energy_zero_iff_laughlin hN _ ψ.property,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, Subtype.ext ?_⟩
    exact congrArg (WithLp.toLp 2) hc.symm
  · rintro ⟨c, hc⟩
    exact ⟨c, congrArg (fun x : SectorHilbert N (3 * (N - 1)) => WithLp.ofLp x.val) hc.symm⟩

end LaughlinGap
namespace LaughlinGap
open scoped BigOperators Topology
open Filter

noncomputable def fallingRatio (Q z : ℕ) : ℝ :=
  (Q.descFactorial z : ℝ) / ((2 * Q - 2).descFactorial z : ℝ)

noncomputable def threeBodyGramCoefficient (Q z : ℕ) : ℝ :=
  (-1 : ℝ) ^ z * fallingRatio Q z *
    (3 * (z : ℝ) - 1 - (z : ℝ) * ((z : ℝ) + 1) / (Q : ℝ))

noncomputable def threeBodyDimensionRatio (Q z : ℕ) : ℝ :=
  (3 * (Q : ℝ) - 1 - 2 * (z : ℝ)) / (2 * (Q : ℝ) - 1)

noncomputable def threeBodyTailTerm (Q z : ℕ) : ℝ :=
  if 17 ≤ z ∧ Odd z ∧ z ≤ Q then
    threeBodyDimensionRatio Q z * |threeBodyGramCoefficient Q z| * ((z : ℝ) + 1)
  else 0

noncomputable def threeBodyTail (Q : ℕ) : ℝ :=
  ∑ z ∈ Finset.range (Q + 1), threeBodyTailTerm Q z

noncomputable def threeBodyTailStar (z : ℕ) : ℝ :=
  if 17 ≤ z ∧ Odd z then
    (3 / 2 : ℝ) * (3 * (z : ℝ) - 1) * ((z : ℝ) + 1) * (1 / 2 : ℝ) ^ z
  else 0

lemma fallingRatio_eq_prod (Q z : ℕ) :
    fallingRatio Q z = ∏ k ∈ Finset.range z,
      ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ) := by
  simp [fallingRatio, Nat.descFactorial_eq_prod_range, Nat.cast_prod, Finset.prod_div_distrib]

lemma fallingRatio_nonneg (Q z : ℕ) : 0 ≤ fallingRatio Q z := by
  unfold fallingRatio
  positivity

theorem fallingRatio_le_two_thirds_pow {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    fallingRatio Q z ≤ (2 / 3 : ℝ) ^ z := by
  rw [fallingRatio_eq_prod]
  calc
    (∏ k ∈ Finset.range z, ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ)) ≤
        ∏ _k ∈ Finset.range z, (2 / 3 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro k hk
        positivity
      · intro k hk
        have hkz := Finset.mem_range.mp hk
        have hkQ : k ≤ Q := by omega
        have hkden : k ≤ 2 * Q - 2 := by omega
        have hden : 0 < ((2 * Q - 2 - k : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < 2 * Q - 2 - k by omega)
        rw [div_le_iff₀ hden]
        rw [Nat.cast_sub hkQ, Nat.cast_sub hkden, Nat.cast_sub (by omega : 2 ≤ 2 * Q)]
        push_cast
        have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
        have hkR : (0 : ℝ) ≤ k := by positivity
        linarith
    _ = (2 / 3 : ℝ) ^ z := by rw [Finset.prod_const, Finset.card_range]

lemma fallingFactor_tendsto (k : ℕ) :
    Tendsto (fun Q : ℕ => ((Q - k : ℕ) : ℝ) / ((2 * Q - 2 - k : ℕ) : ℝ))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have ht : Tendsto (fun Q : ℕ => (1 - (k : ℝ) / Q) / (2 - ((k : ℝ) + 2) / Q))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_def, sub_zero] using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ) + 2)))
      (by norm_num : (2 : ℝ) - 0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (k + 3)] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [Nat.cast_sub (by omega : k ≤ Q), Nat.cast_sub (by omega : k ≤ 2 * Q - 2),
    Nat.cast_sub (by omega : 2 ≤ 2 * Q)]
  push_cast
  field_simp [hQ0]
  ring_nf

theorem fallingRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => fallingRatio Q z) atTop (𝓝 ((1 / 2 : ℝ) ^ z)) := by
  simpa only [fallingRatio_eq_prod, Finset.prod_const, Finset.card_range] using
    (tendsto_finsetProd (Finset.range z) (fun k _ => fallingFactor_tendsto k))

theorem threeBodyGramCoefficient_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyGramCoefficient Q z)
      atTop (𝓝 ((3 * (z : ℝ) - 1) * (-1 / 2 : ℝ) ^ z)) := by
  have h := ((tendsto_const_nhds (x := (-1 : ℝ) ^ z)).mul (fallingRatio_tendsto z)).mul
    ((tendsto_const_nhds (x := 3 * (z : ℝ) - 1)).sub
      (tendsto_const_div_atTop_nhds_zero_nat ((z : ℝ) * ((z : ℝ) + 1))))
  convert h using 1
  · rfl
  · 
    rw [sub_zero, div_pow, div_pow]
    ring_nf

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyDimensionRatio Q z) atTop (𝓝 (3 / 2 : ℝ)) := by
  have ht : Tendsto (fun Q : ℕ => (3 - (1 + 2 * (z : ℝ)) / Q) / (2 - (1 : ℝ) / Q))
      atTop (𝓝 (3 / 2 : ℝ)) := by
    simpa only [Pi.div_def, sub_zero] using ((tendsto_const_nhds (x := (3 : ℝ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 + 2 * (z : ℝ)))).div
      ((tendsto_const_nhds (x := (2 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)))
      (by norm_num : (2 : ℝ) - 0 ≠ 0)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  unfold threeBodyDimensionRatio
  field_simp [hQ0]
  ring_nf

theorem threeBodyBracket_nonneg {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) (hz16 : 16 ≤ z) :
    0 ≤ 3 * (z : ℝ) - 1 - (z : ℝ) * ((z : ℝ) + 1) / Q := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hzQ : (z : ℝ) ≤ Q := by exact_mod_cast hz
  have hzR : (16 : ℝ) ≤ z := by exact_mod_cast hz16
  have hdiv : (z : ℝ) * ((z : ℝ) + 1) / Q ≤ (z : ℝ) + 1 := by
    rw [div_le_iff₀ hQpos]
    exact mul_le_mul_of_nonneg_right hzQ (by positivity) |>.trans_eq (mul_comm _ _)
  linarith

theorem threeBodyGramCoefficient_abs_le {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q)
    (hz16 : 16 ≤ z) :
    |threeBodyGramCoefficient Q z| ≤ (2 / 3 : ℝ) ^ z * (3 * (z : ℝ)) := by
  rw [threeBodyGramCoefficient, abs_mul, abs_mul, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (fallingRatio_nonneg Q z),
    abs_of_nonneg (threeBodyBracket_nonneg hQ hz hz16)]
  apply mul_le_mul (fallingRatio_le_two_thirds_pow hQ hz)
  · have hn : (0 : ℝ) ≤ (z : ℝ) * ((z : ℝ) + 1) / Q := by positivity
    linarith
  · exact threeBodyBracket_nonneg hQ hz hz16
  · positivity

lemma threeBodyDimensionRatio_nonneg {Q z : ℕ} (hQ : 4 ≤ Q) (hz : z ≤ Q) :
    0 ≤ threeBodyDimensionRatio Q z := by
  have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hzR : (z : ℝ) ≤ Q := by exact_mod_cast hz
  exact div_nonneg (by linarith) (by linarith)

lemma threeBodyDimensionRatio_le_two {Q z : ℕ} (hQ : 4 ≤ Q) :
    threeBodyDimensionRatio Q z ≤ 2 := by
  have hQR : (4 : ℝ) ≤ Q := by exact_mod_cast hQ
  unfold threeBodyDimensionRatio
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Q - 1)]
  have hzR : (0 : ℝ) ≤ z := by positivity
  linarith

lemma threeBodyTailTerm_nonneg {Q : ℕ} (hQ : 4 ≤ Q) (z : ℕ) :
    0 ≤ threeBodyTailTerm Q z := by
  unfold threeBodyTailTerm
  split_ifs with hz
  · exact mul_nonneg (mul_nonneg (threeBodyDimensionRatio_nonneg hQ hz.2.2)
      (abs_nonneg _)) (by positivity)
  · rfl

theorem threeBodyTailTerm_norm_le {Q : ℕ} (hQ : 4 ≤ Q) (z : ℕ) :
    ‖threeBodyTailTerm Q z‖ ≤ 6 * (z : ℝ) * ((z : ℝ) + 1) * (2 / 3 : ℝ) ^ z := by
  rw [Real.norm_of_nonneg (threeBodyTailTerm_nonneg hQ z)]
  unfold threeBodyTailTerm
  split_ifs with hz
  · calc
      _ ≤ 2 * ((2 / 3 : ℝ) ^ z * (3 * (z : ℝ))) * ((z : ℝ) + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul (threeBodyDimensionRatio_le_two hQ)
          (threeBodyGramCoefficient_abs_le hQ hz.2.2 (by omega)) (abs_nonneg _)
          (by norm_num)
      _ = _ := by ring
  · positivity

lemma summable_threeBodyTail_majorant :
    Summable (fun z : ℕ => 6 * (z : ℝ) * ((z : ℝ) + 1) * (2 / 3 : ℝ) ^ z) := by
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)
  exact ((hs2.add hs1).mul_left (6 : ℝ)).congr (fun z => by ring)

theorem threeBodyTailTerm_tendsto (z : ℕ) :
    Tendsto (fun Q : ℕ => threeBodyTailTerm Q z) atTop (𝓝 (threeBodyTailStar z)) := by
  by_cases hz : 17 ≤ z ∧ Odd z
  · have ha := (threeBodyGramCoefficient_tendsto z).abs
    have hzR : (17 : ℝ) ≤ z := by exact_mod_cast hz.1
    have he : |(3 * (z : ℝ) - 1) * (-1 / 2 : ℝ) ^ z| =
        (3 * (z : ℝ) - 1) * (1 / 2 : ℝ) ^ z := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * (z : ℝ) - 1), abs_pow]
      norm_num
    rw [he] at ha
    have hh := ((threeBodyDimensionRatio_tendsto z).mul ha).mul_const ((z : ℝ) + 1)
    have hlim : (3 / 2 : ℝ) * ((3 * (z : ℝ) - 1) * (1 / 2 : ℝ) ^ z) * ((z : ℝ) + 1) =
        threeBodyTailStar z := by
      simp only [threeBodyTailStar, ite_eq_left hz]
      ring
    rw [hlim] at hh
    apply hh.congr' 
    filter_upwards [eventually_ge_atTop z] with Q hQ
    simp [threeBodyTailTerm, hz.1, hz.2, hQ]
  · have he : ∀ Q, threeBodyTailTerm Q z = 0 := by
      intro Q
      simp only [threeBodyTailTerm]
      rw [ite_eq_right (by tauto)]
    simpa only [he, threeBodyTailStar, ite_eq_right hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

private lemma hasSum_square_quarter :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 4 : ℝ) ^ n) (20 / 27 : ℝ) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  convert ((h2.mul_left (2 : ℝ)).sub (h1.mul_left (3 : ℝ))).sub (h0.mul_left (2 : ℝ)) using 1 <;> try rfl
  · ext n
    rw [Nat.cast_choose_two]
    push_cast
    ring
  · norm_num

theorem hasSum_threeBodyTailStar_progression :
    HasSum (fun m : ℕ => threeBodyTailStar (17 + 2 * m)) (61 / 4096 : ℝ) := by
  have h0 := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)
  have h2 := hasSum_square_quarter
  convert (((h0.mul_left (900 : ℝ)).add (h1.mul_left (208 : ℝ))).add
    (h2.mul_left (12 : ℝ))).mul_left (3 / 262144 : ℝ) using 1 <;> try rfl
  · ext m
    have hm : 17 ≤ 17 + 2 * m ∧ Odd (17 + 2 * m) := by
      constructor
      · omega
      · rw [Nat.odd_iff]; omega
    simp only [threeBodyTailStar, ite_eq_left hm, pow_add, pow_mul]
    push_cast
    norm_num
    ring
  · norm_num

theorem hasSum_threeBodyTailStar : HasSum threeBodyTailStar (61 / 4096 : ℝ) := by
  have hinj : Function.Injective (fun m : ℕ => 17 + 2 * m) := by
    intro a b hab
    dsimp at hab
    omega
  have hout : ∀ z, z ∉ Set.range (fun m : ℕ => 17 + 2 * m) → threeBodyTailStar z = 0 := by
    intro z hz
    have hbad : ¬ (17 ≤ z ∧ Odd z) := by
      rintro ⟨hz17, hzodd⟩
      have hp := Nat.odd_iff.mp hzodd
      apply hz
      exact ⟨(z - 17) / 2, by dsimp; omega⟩
    exact ite_eq_right hbad
  exact (hinj.hasSum_iff hout).mp hasSum_threeBodyTailStar_progression

theorem threeBodyTail_tendsto :
    Tendsto threeBodyTail atTop (𝓝 (61 / 4096 : ℝ)) := by
  have ht := tendsto_tsum_of_dominated_convergence summable_threeBodyTail_majorant
    threeBodyTailTerm_tendsto
    (show ∀ᶠ Q in atTop, ∀ z, ‖threeBodyTailTerm Q z‖ ≤
        6 * (z : ℝ) * ((z : ℝ) + 1) * (2 / 3 : ℝ) ^ z by
      filter_upwards [eventually_ge_atTop 4] with Q hQ z
      exact threeBodyTailTerm_norm_le hQ z)
  rw [hasSum_threeBodyTailStar.tsum_eq] at ht
  have he : threeBodyTail = (fun Q => ∑' z, threeBodyTailTerm Q z) := by
    funext Q
    unfold threeBodyTail
    symm
    apply tsum_eq_sum
    intro z hz
    have hzQ : ¬ z ≤ Q := by
      simp only [Finset.mem_range] at hz
      omega
    simp [threeBodyTailTerm, hzQ]
  rw [he]
  exact ht

end LaughlinGap
namespace LaughlinGap
open scoped BigOperators InnerProduct ComplexConjugate

section Compression
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem compression_positive_iff (W : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E)
    (hC : C.IsSymmetric) :
    (W ∘ₗ C ∘ₗ W.adjoint).IsPositive ↔
      ∀ x ∈ W.adjoint.range, 0 ≤ RCLike.re (inner 𝕜 (C x) x) := by
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    simpa only [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right] using
      h.re_inner_nonneg_left y
  · intro h
    refine ⟨hC.conj_adjoint W, fun y => ?_⟩
    simpa only [LinearMap.comp_apply, ← LinearMap.adjoint_inner_right] using
      h (W.adjoint y) (LinearMap.mem_range_self W.adjoint y)

theorem gram_compression_positive_iff (W : E →ₗ[𝕜] F) (C : E →ₗ[𝕜] E)
    (hC : C.IsSymmetric) :
    ((W.adjoint ∘ₗ W) ∘ₗ C ∘ₗ (W.adjoint ∘ₗ W)).IsPositive ↔
      (W ∘ₗ C ∘ₗ W.adjoint).IsPositive := by
  have hG : (W.adjoint ∘ₗ W).IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self W
  have h := compression_positive_iff (W.adjoint ∘ₗ W) C hC
  rw [hG.adjoint_eq, LinearMap.range_adjoint_comp_self] at h
  exact h.trans (compression_positive_iff W C hC).symm

end Compression

section AnnihilatorBound
variable {ι κ E F : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup F]

theorem annihilator_collection_bound (p : ι → κ) (B : κ → E → F)
    (A : ι → F → F) {M : ℕ}
    (hM : ∀ k, (Finset.univ.filter (fun b => p b = k)).card ≤ M)
    (hA : ∀ b y, ‖A b y‖ ≤ ‖y‖) (x : E) :
    ∑ b, ‖A b (B (p b) x)‖ ^ 2 ≤ (M : ℝ) * ∑ k, ‖B k x‖ ^ 2 := by
  classical
  calc
    (∑ b, ‖A b (B (p b) x)‖ ^ 2) ≤ ∑ b, ‖B (p b) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      exact pow_le_pow_left₀ (norm_nonneg _) (hA b _) 2
    _ = ∑ k, ((Finset.univ.filter (fun b => p b = k)).card : ℝ) * ‖B k x‖ ^ 2 := by
      rw [← Finset.sum_fiberwise' Finset.univ p (fun k => ‖B k x‖ ^ 2)]
      simp
    _ ≤ ∑ k, (M : ℝ) * ‖B k x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hM k) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

end AnnihilatorBound

section Perturbation
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem quadratic_perturbation_abs_le (T S : E →L[𝕜] E) (x : E) :
    |RCLike.re (inner 𝕜 x (T x)) - RCLike.re (inner 𝕜 x (S x))| ≤
      ‖T - S‖ * ‖x‖ ^ 2 := by
  have h₁ := RCLike.norm_re_le_norm (inner 𝕜 x ((T - S) x))
  have h₂ := norm_inner_le_norm (𝕜 := 𝕜) x ((T - S) x)
  have h₃ := mul_le_mul_of_nonneg_left ((T - S).le_opNorm x) (norm_nonneg x)
  have h := (h₁.trans h₂).trans h₃
  simpa only [sub_apply, inner_sub_right, map_sub, Real.norm_eq_abs,
    mul_left_comm ‖x‖ ‖T - S‖ ‖x‖, ← pow_two, mul_assoc] using h

theorem quadratic_perturbation_lower_bound (T S : E →L[𝕜] E) (x : E)
    (hS : 0 ≤ RCLike.re (inner 𝕜 x (S x))) :
    -‖T - S‖ * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 x (T x)) := by
  have h := (abs_le.mp (quadratic_perturbation_abs_le T S x)).1
  nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] in

theorem relative_column_perturbation_bound {ι : Type*} [Fintype ι]
    (A : ι → E → F) (Δ : E → E) (eStar eQ : E → ℝ) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hA : ∀ x, (∑ b, ‖A b x‖ ^ 2) ≤ C₀ * eStar x)
    (hΔ : ∀ x, eStar (Δ x) ≤ eQ x)
    (T S : (PiLp 2 (fun _ : ι => F)) →L[𝕜] (PiLp 2 (fun _ : ι => F)))
    (hS : ∀ x, 0 ≤ RCLike.re (inner 𝕜 (WithLp.toLp 2 (fun b => A b x))
      (S (WithLp.toLp 2 (fun b => A b x))))) (x : E) :
    -(C₀ * ‖T - S‖) * eQ x ≤
      RCLike.re (inner 𝕜 (WithLp.toLp 2 (fun b => A b (Δ x)))
        (T (WithLp.toLp 2 (fun b => A b (Δ x))))) := by
  let v : PiLp 2 (fun _ : ι => F) := WithLp.toLp 2 (fun b => A b (Δ x))
  have hv : ‖v‖ ^ 2 ≤ C₀ * eQ x := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact (hA (Δ x)).trans (mul_le_mul_of_nonneg_left (hΔ x) hC₀)
  have hp := quadratic_perturbation_lower_bound T S v (hS (Δ x))
  calc
    -(C₀ * ‖T - S‖) * eQ x = -‖T - S‖ * (C₀ * eQ x) := by ring
    _ ≤ -‖T - S‖ * ‖v‖ ^ 2 := by
      exact mul_le_mul_of_nonpos_left hv (neg_nonpos.mpr (norm_nonneg _))
    _ ≤ _ := hp

theorem relative_column_error_tendsto {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {T : ℕ → G →L[𝕜] G} {S : G →L[𝕜] G} {C₀ : ℝ}
    (hT : Filter.Tendsto T Filter.atTop (nhds S)) :
    Filter.Tendsto (fun Q => C₀ * ‖T Q - S‖) Filter.atTop (nhds 0) := by
  simpa using (((hT.sub (tendsto_const_nhds (x := S))).norm).const_mul C₀)

end Perturbation

end LaughlinGap

end

end OAI
