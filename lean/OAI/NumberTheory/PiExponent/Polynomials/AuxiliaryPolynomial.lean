import OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix
import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame
import OAI.NumberTheory.PiExponent.Polynomials.SimplexRational

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

noncomputable def polynomialOfCoefficients {d : ℕ} (S : Finset (Fin d → ℕ)) :
    (S → ℂ) →ₗ[ℂ] MvPolynomial (Fin d) ℂ := by
  classical
  exact
    { toFun := fun x => ∑ a : S, MvPolynomial.monomial
        (InterpolationMatrix.exponentVector a.val) (x a)
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun z x => by
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]  }

theorem exponentVector_injective {d : ℕ} :
    Function.Injective (@InterpolationMatrix.exponentVector d) := by
  intro a b h
  funext i
  have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
  simpa only [InterpolationMatrix.exponentVector_apply] using hi

@[simp] theorem polynomialOfCoefficients_coeff {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) (a : S) :
    (polynomialOfCoefficients S x).coeff (InterpolationMatrix.exponentVector a.val) = x a := by
  classical
  change (∑ exponent : S, MvPolynomial.monomial
    (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff
      (InterpolationMatrix.exponentVector a.val) = x a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : InterpolationMatrix.exponentVector b.val ≠
        InterpolationMatrix.exponentVector a.val := by
      intro h
      exact hba (Subtype.ext (exponentVector_injective h))
    simp [hne]
  · simp

theorem polynomialOfCoefficients_injective {d : ℕ} (S : Finset (Fin d → ℕ)) :
    Function.Injective (polynomialOfCoefficients S) := by
  intro x y h
  funext a
  have := congrArg (fun p : MvPolynomial (Fin d) ℂ =>
    p.coeff (InterpolationMatrix.exponentVector a.val)) h
  simpa only [polynomialOfCoefficients_coeff] using this

theorem polynomialOfCoefficients_support {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) :
    (polynomialOfCoefficients S x).support ⊆ S.image InterpolationMatrix.exponentVector := by
  classical
  intro e he
  by_contra hn
  have hzero : (polynomialOfCoefficients S x).coeff e = 0 := by
    change (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff e = 0
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : InterpolationMatrix.exponentVector a.val ≠ e := by
      intro h
      exact hn (Finset.mem_image.mpr ⟨a.val, a.property, h⟩)
    simp [MvPolynomial.coeff_monomial, hne]
  exact (MvPolynomial.mem_support_iff.mp he) hzero

theorem polynomialOfCoefficients_weighted {m : ℕ} (W : Fin (m + 1) → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    PiExponentApprox.HasWeightedDegreeLE W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by
  classical
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [PiExponentApprox.monomialWeight,
    InterpolationMatrix.exponentVector_apply, mul_comm] using h

theorem exists_nonzero_kernel_of_card_lt {C R : Type*} [Fintype C] [Fintype R]
    (E : (C → ℂ) →ₗ[ℂ] (R → ℂ)) (h : Fintype.card R < Fintype.card C) :
    ∃ x : C → ℂ, x ≠ 0 ∧ E x = 0 := by
  have hk : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Module.finrank_fintype_fun_eq_card] using h)
  obtain ⟨x, hx, hn⟩ := (LinearMap.ker E).ne_bot_iff.mp hk
  exact ⟨x, hn, LinearMap.mem_ker.mp hx⟩

theorem tendsto_card_strictWeightedSimplex_scale {d : ℕ} (V : Fin d → ℚ)
    (hV : ∀ i, 0 < V i) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℝ =>
      ((strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℝ) / N ^ d)
      atTop (𝓝 (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)))) := by
  have ht : Tendsto (fun N : ℝ => a * N) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have h := ((tendsto_card_strictWeightedSimplex_rational V hV).comp ht).mul_const (a ^ d)
  have heq : 1 / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) * a ^ d =
      a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) := by ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun N => by
    simp only [Function.comp_apply, mul_pow]
    field_simp)

theorem eventually_auxiliary_card_lt {d : ℕ} (W V : Fin d → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card <
        (realWeightedSimplex (fun i => (W i : ℝ)) N).card := by
  have hPW : 0 < ∏ i, (W i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hW i)
  have hPV : 0 < ∏ i, (V i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hV i)
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hconst : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) <
      1 / ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) := by
    have hmain := (div_lt_one hPV).mp hvol
    apply (lt_div_iff₀ (mul_pos hF hPW)).mpr
    have heq : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) *
        ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) =
        (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) := by
      field_simp
    rw [heq]
    exact hvol
  have hsmall := ((tendsto_card_strictWeightedSimplex_scale V hV ha).const_mul (K : ℝ)).eventually_lt
    (tendsto_card_realWeightedSimplex_rational W hW) hconst
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  have hscaled : ((K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℕ) : ℝ) /
      N ^ d < ((realWeightedSimplex (fun i => (W i : ℝ)) N).card : ℝ) / N ^ d := by
    simpa only [Nat.cast_mul, mul_div_assoc] using hN
  exact_mod_cast (div_lt_div_iff_of_pos_right (pow_pos hNpos d)).mp hscaled

theorem eventually_exists_auxiliaryPolynomial {m : ℕ} (W V : Fin (m + 1) → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      ∀ E : PiExponentApprox.FramePolynomial m →ₗ[ℂ]
        ((Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) → ℂ),
      ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
        PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧ E p = 0 := by
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  intro E
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let A := E.comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) <
      Fintype.card S := by simpa [S] using hN
  obtain ⟨x, hx, hAx⟩ := exists_nonzero_kernel_of_card_lt A hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, hAx⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_weighted (fun i => (W i : ℝ))
      (fun i => by exact_mod_cast hW i) N x

end PiExponent

end OAI
